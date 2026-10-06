package kgo

import java.math.BigInteger
import java.math.BigDecimal
import java.math.MathContext
import java.math.RoundingMode
import java.util.IdentityHashMap
import java.util.concurrent.ConcurrentHashMap
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineExceptionHandler
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.async
import kotlinx.coroutines.cancel
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.selects.selectUnbiased
import kotlinx.coroutines.yield
import java.util.concurrent.atomic.AtomicInteger

open class RuntimeGoError(message: String) : RuntimeException(message)

private class GoString(val bytes: ByteArray, val type: GoTypeSyntax = NamedGoType("string")) {
    override fun equals(other: Any?) = other is GoString && bytes.contentEquals(other.bytes)
    override fun hashCode() = bytes.contentHashCode()
    override fun toString() = String(bytes, Charsets.UTF_8)
}

internal class GoRational private constructor(val numerator: BigInteger, val denominator: BigInteger) : Comparable<GoRational> {
    operator fun plus(other: GoRational) = of(numerator * other.denominator + other.numerator * denominator, denominator * other.denominator)
    operator fun minus(other: GoRational) = of(numerator * other.denominator - other.numerator * denominator, denominator * other.denominator)
    operator fun times(other: GoRational) = of(numerator * other.numerator, denominator * other.denominator)
    operator fun div(other: GoRational): GoRational {
        if (other.numerator.signum() == 0) throw RuntimeGoError("division by zero")
        return of(numerator * other.denominator, denominator * other.numerator)
    }
    fun negate() = of(numerator.negate(), denominator)
    fun isInteger() = denominator == BigInteger.ONE
    fun toDouble(): Double = BigDecimal(numerator).divide(BigDecimal(denominator), DOUBLE_CONTEXT).toDouble()
    override fun compareTo(other: GoRational): Int = (numerator * other.denominator).compareTo(other.numerator * denominator)
    override fun equals(other: Any?) = other is GoRational && numerator == other.numerator && denominator == other.denominator
    override fun hashCode() = 31 * numerator.hashCode() + denominator.hashCode()
    override fun toString() = toDouble().toString()

    companion object {
        val ZERO = GoRational(BigInteger.ZERO, BigInteger.ONE)
        private val DOUBLE_CONTEXT = MathContext(1200, RoundingMode.HALF_EVEN)
        fun of(numerator: BigInteger, denominator: BigInteger = BigInteger.ONE): GoRational {
            if (denominator.signum() == 0) throw RuntimeGoError("division by zero")
            val sign = if (denominator.signum() < 0) BigInteger.ONE.negate() else BigInteger.ONE
            val n = numerator * sign
            val d = denominator.abs()
            val divisor = n.gcd(d)
            return GoRational(n / divisor, d / divisor)
        }
        fun decimal(text: String): GoRational {
            val value = BigDecimal(text)
            val scale = value.scale()
            return if (scale >= 0) of(value.unscaledValue(), BigInteger.TEN.pow(scale))
            else of(value.unscaledValue() * BigInteger.TEN.pow(-scale))
        }
    }
}

private data class GoExactComplex(val real: GoRational, val imaginary: GoRational)
private val untypedRuneRuntimeType = NamedGoType("#untyped-rune")

/** Runtime for the currently implemented Go 1.0 execution subset. */
class Interpreter(private val output: (String) -> Unit = { print(it) }) {
    private val functions = mutableMapOf<String, FunctionDeclaration>()
    private val methods = mutableMapOf<String, FunctionDeclaration>()
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val globals = Environment()
    private val elementPointers = IdentityHashMap<MutableList<Any?>, MutableMap<Int, GoPointer>>()
    private val typeDefinitions = ConcurrentHashMap<String, GoTypeSyntax>()
    private val localTypeIdentities = IdentityHashMap<TypeDeclaration, String>()
    private val nextLocalTypeIdentity = AtomicInteger()
    private val fmtAliases = mutableSetOf("fmt")
    private lateinit var goroutines: CoroutineScope

    fun run(file: GoFile) {
        runBlocking {
            val goroutineFailure = CompletableDeferred<Throwable>()
            val failureHandler = CoroutineExceptionHandler { _, failure -> goroutineFailure.complete(failure) }
            goroutines = CoroutineScope(SupervisorJob() + Dispatchers.Default + failureHandler)
            try {
                file.declarations.filterIsInstance<ImportDeclaration>().flatMap { it.imports }.forEach { spec ->
                    val importPath = decodeGoStringLiteralBytes(spec.path).toString(Charsets.UTF_8)
                    val alias = when (spec.alias) {
                        ".", "_" -> null
                        null -> importPath.substringAfterLast('/')
                        else -> spec.alias
                    }
                    if (alias != null && importPath.substringAfterLast('/') == "fmt") fmtAliases += alias
                }
        file.declarations.filterIsInstance<FunctionDeclaration>().forEach { function ->
                    if (function.receiver != null) methods[methodKey(function.receiver.type, function.name)] = function
                    else if (function.name == "init") initFunctions += function
                    else functions[function.name] = function
                }
                file.declarations.filterIsInstance<TypeDeclaration>().forEach {
                    typeDefinitions[it.name] = it.type
                    globals.defineType(it.name, NamedGoType(it.name))
                }
                val packageConstants = file.declarations.filterIsInstance<ConstantDeclaration>()
                val packageVariables = file.declarations.filterIsInstance<VariableDeclaration>()
                packageConstants.forEach { declaration -> declaration.names.filter { it != "_" }.forEach { name -> globals.define(name, null, declaration.type) } }
                packageVariables.forEach { declaration -> declaration.names.filter { it != "_" }.forEach { name ->
                    globals.define(name, declaration.type?.let(::zeroValue), declaration.type)
                } }
                orderPackageDeclarations(packageConstants, { it.names }, { it.values }, includeFunctionDependencies = false)
                    .forEach { initializeConstant(it) }
                orderPackageDeclarations(packageVariables, { it.names }, { it.values }, includeFunctionDependencies = true)
                    .forEach { initialize(it.names, it.values, globals, it.type) }
                initFunctions.forEach { invoke(it, emptyList()) }
                val main = functions["main"] ?: throw RuntimeGoError("main function not found")
                val mainExecution = async { invoke(main, emptyList()) }
                selectUnbiased<Unit> {
                    mainExecution.onAwait { }
                    goroutineFailure.onAwait { throw it }
                }
            } finally {
                // Go exits when main returns; it does not wait for remaining goroutines.
                goroutines.cancel()
            }
        }
    }

    private suspend fun invoke(
        function: FunctionDeclaration,
        arguments: List<Any?>,
        receiver: Any? = null,
        parent: Environment = globals,
        expandedVariadic: Boolean = false,
        panicState: PanicState = parent.panicState,
        deferredCall: Boolean = false
    ): List<Any?> {
        val fixedCount = if (function.variadic) function.parameters.size - 1 else function.parameters.size
        if ((!function.variadic && arguments.size != fixedCount) ||
            (function.variadic && (arguments.size < fixedCount || (expandedVariadic && arguments.size != function.parameters.size)))) {
            throw RuntimeGoError("${function.name} has incompatible argument count: ${arguments.size}")
        }
        val boundArguments = if (!function.variadic || expandedVariadic) arguments else {
            val sliceType = function.parameterTypes.lastOrNull() as? SliceGoType
                ?: throw RuntimeGoError("invalid variadic function signature")
            val extras = arguments.drop(fixedCount)
            arguments.take(fixedCount) + GoSlice(sliceType.element, extras.mapTo(mutableListOf(), ::copyValue), 0, extras.size, extras.size,
                type = sliceType)
        }
        val body = function.body ?: throw RuntimeGoError("function ${function.name} has no Go body")
        val env = Environment(parent, panicState = panicState)
        function.receiver?.let { env.define(it.name ?: "", copyForType(receiver, it.type), it.type) }
        function.parameters.zip(boundArguments).forEachIndexed { i, (name, value) ->
            name?.let { parameterName ->
                val type = function.parameterTypes.getOrNull(i)
                env.define(parameterName, type?.let { copyForType(value, it) } ?: value, type)
            }
        }
        val resultNames = function.resultNames.ifEmpty { List(function.resultTypes.size) { null } }
        resultNames.forEachIndexed { index, name ->
            if (name != null && name != "_") env.define(name, zeroValue(function.resultTypes[index]), function.resultTypes[index])
        }
        val priorRecoverAllowed = panicState.recoverAllowed
        panicState.recoverAllowed = deferredCall
        var defersRun = false
        return try {
            executeBlock(body, env, createScope = false)
            emptyList()
        } catch (returned: ReturnSignal) {
            if (returned.values.size == function.resultTypes.size) {
                returned.values.forEachIndexed { i, value ->
                    val name = resultNames.getOrNull(i)
                    val normalized = if (returned.runeConstants.getOrNull(i) == true &&
                        underlying(function.resultTypes[i]) is InterfaceGoType) asRuneValue(value) else value
                    if (name != null && name != "_") env.set(name, normalized)
                }
            }
            defersRun = true
            env.runDefers()
            val values = when {
                returned.values.isEmpty() && resultNames.isNotEmpty() && resultNames.all { it != null } ->
                    resultNames.mapIndexed { i, name ->
                        if (name == "_") zeroValue(function.resultTypes[i]) else env.get(name!!)
                    }
                returned.values.size == function.resultTypes.size -> returned.values.mapIndexed { i, value ->
                    val name = resultNames.getOrNull(i)
                    val normalized = if (returned.runeConstants.getOrNull(i) == true &&
                        underlying(function.resultTypes[i]) is InterfaceGoType) asRuneValue(value) else value
                    if (name != null && name != "_") env.get(name)
                    else copyForType(normalized, function.resultTypes[i])
                }
                else -> returned.values
            }
            values.mapIndexed { i, value -> function.resultTypes.getOrNull(i)?.let { type ->
                val normalized = if (returned.runeConstants.getOrNull(i) == true && underlying(type) is InterfaceGoType)
                    asRuneValue(value) else value
                copyForType(normalized, type)
            } ?: value }
        } catch (panic: PanicSignal) {
            panicState.activePanic = panic
            defersRun = true
            env.runDefers()
            if (panic.recovered) recoveredResultValues(function, resultNames, env) else throw panic
        } catch (failure: RuntimeGoError) {
            val panic = PanicSignal(failure.message ?: "runtime panic", failure.message ?: "runtime panic")
            panicState.activePanic = panic
            defersRun = true
            env.runDefers()
            if (panic.recovered) recoveredResultValues(function, resultNames, env) else throw panic
        } finally {
            if (!defersRun && currentCoroutineContext().isActive) env.runDefers()
            panicState.recoverAllowed = priorRecoverAllowed
        }
    }

    private fun recoveredResultValues(
        function: FunctionDeclaration,
        resultNames: List<String?>,
        env: Environment
    ): List<Any?> = function.resultTypes.mapIndexed { index, type ->
        val name = resultNames.getOrNull(index)
        val value = if (name != null && name != "_") env.get(name) else zeroValue(type)
        copyForType(value, type)
    }

    private suspend fun executeBlock(block: BlockStatement, parent: Environment, createScope: Boolean = true) {
        val env = if (createScope) parent.child() else parent
        predeclareBlockTypes(block, env)
        var index = 0
        while (index < block.statements.size) {
            yield()
            try {
                execute(block.statements[index], env)
                index++
            } catch (jump: GotoSignal) {
                val target = block.statements.indexOfFirst { it is LabeledStatement && it.label == jump.label }
                if (target < 0) throw jump
                index = target
            }
        }
    }

    private fun predeclareBlockTypes(block: BlockStatement, env: Environment) {
        predeclareTypes(block.statements, env)
    }

    private fun predeclareTypes(statements: List<Statement>, env: Environment) {
        fun predeclare(statement: Statement) {
            when (statement) {
                is DeclarationStatement -> statement.declarations.filterIsInstance<TypeDeclaration>()
                    .forEach { defineLocalType(it, env) }
                is LabeledStatement -> predeclare(statement.statement)
                else -> Unit
            }
        }
        statements.forEach(::predeclare)
    }

    private suspend fun execute(statement: Statement, env: Environment, labels: Set<String> = emptySet()) {
        when (statement) {
            EmptyStatement -> Unit
            is LabeledStatement -> execute(statement.statement, env, labels + statement.label)
            is DeclarationStatement -> statement.declarations.forEach { declaration ->
                when (declaration) {
                    is VariableDeclaration -> initialize(declaration.names, declaration.values, env, declaration.type)
                    is ConstantDeclaration -> initializeConstantIn(declaration, env)
                    is TypeDeclaration -> defineLocalType(declaration, env)
                    else -> throw RuntimeGoError("unsupported local declaration")
                }
            }
            is BlockStatement -> executeBlock(statement, env)
            is VariableStatement -> initialize(statement.names, statement.values, env, statement.type)
            is ReturnStatement -> {
                val evaluated = statement.values.map { copyValue(evaluate(it, env)) }
                val values = if (statement.values.size == 1 && evaluated.singleOrNull() is GoMultiValue)
                    (evaluated.single() as GoMultiValue).values else evaluated
                val runeConstants = if (values.size == statement.values.size) statement.values.mapIndexed { index, expression ->
                    values.getOrNull(index) is BigInteger && isRuneConstantExpression(expression, env)
                } else List(values.size) { false }
                throw ReturnSignal(values, runeConstants)
            }
            is ExpressionStatement -> evaluate(statement.expression, env)
            is AssignmentStatement -> assign(statement, env)
            is IfStatement -> {
                val scope = env.child()
                statement.init?.let { execute(it, scope) }
                if (truth(evaluate(statement.condition, scope))) executeBlock(statement.thenBranch, scope)
                else statement.elseBranch?.let { execute(it, scope) }
            }
            is ForStatement -> {
                val scope = env.child()
                if (statement.rangeClause != null) {
                    executeRange(statement.rangeClause, statement.body, scope, labels)
                } else {
                    statement.init?.let { execute(it, scope) }
                    while (statement.condition == null || truth(evaluate(statement.condition, scope))) {
                        yield()
                        try { executeBlock(statement.body, scope) }
                        catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                        catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                        statement.post?.let { execute(it, scope) }
                    }
                }
            }
            is IncrementStatement -> {
                val target = resolveTarget(statement.target, env)
                val old = number(target.get(), "increment")
                target.set(old + statement.delta)
            }
            is SendStatement -> {
                val channel = evaluate(statement.channel, env)
                val value = evaluate(statement.value, env)
                when (channel) {
                    is GoChannel -> channel.send(value)
                    is GoNilValue -> if (underlying(channel.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("send on non-channel")
                    else -> throw RuntimeGoError("send on non-channel")
                }
            }
            is GoStatement -> {
                val call = statement.call.unparenthesized() as? CallExpression
                    ?: throw RuntimeGoError("go statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = evaluateCallArguments(call, env)
                goroutines.launch { call(target, arguments, call.expandLastArgument, PanicState(), environment = env) }
            }
            is DeferStatement -> {
                val call = statement.call.unparenthesized() as? CallExpression
                    ?: throw RuntimeGoError("defer statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = evaluateCallArguments(call, env)
                env.defer { call(target, arguments, call.expandLastArgument, env.panicState, deferredCall = true, environment = env) }
            }
            is BranchStatement -> when (statement.kind) {
                TokenKind.BREAK -> throw BreakSignal(statement.label)
                TokenKind.CONTINUE -> throw ContinueSignal(statement.label)
                TokenKind.GOTO -> throw GotoSignal(statement.label ?: throw RuntimeGoError("goto requires a label"))
                TokenKind.FALLTHROUGH -> throw FallthroughSignal()
                else -> throw RuntimeGoError("invalid branch statement")
            }
            is SelectStatement -> executeSelect(statement, env, labels)
            is SwitchStatement -> executeSwitch(statement, env, labels)
            is TypeSwitchStatement -> executeTypeSwitch(statement, env, labels)
        }
    }

    private fun targets(label: String?, labels: Set<String>) = label == null || label in labels

    private suspend fun assign(statement: AssignmentStatement, env: Environment) {
        if (statement.operator == TokenKind.DEFINE) {
            val values = expandValues(evaluateRhs(statement.values, statement.targets.size, env), statement.targets.size)
            assignValues(statement.targets, statement.operator, values, env, statement.values)
        } else {
            val locations = statement.targets.map { resolveTarget(it, env) }
            val previous = if (statement.operator == TokenKind.ASSIGN) emptyList() else locations.map { it.get() }
            val values = expandValues(evaluateRhs(statement.values, statement.targets.size, env), statement.targets.size)
            assignToLocations(locations, statement.operator, assignedValues(locations, values, statement.values, env), previous)
        }
    }

    private suspend fun assignValues(
        targets: List<Expression>,
        operator: TokenKind,
        values: List<Any?>,
        env: Environment,
        sourceExpressions: List<Expression>? = null
    ) {
        if (operator == TokenKind.DEFINE) {
            val names = targets.map { (it as? NameExpression)?.name ?: throw RuntimeGoError("short declaration targets must be names") }
            if (names.size != values.size) throw RuntimeGoError("assignment count mismatch")
            val declared = mutableSetOf<String>()
            names.zip(values).forEachIndexed { index, (name, value) ->
                if (name == "_") return@forEachIndexed
                if (!declared.add(name)) throw RuntimeGoError("$name repeated on left side of :=")
                val initialized = defaultConstantValue(value, sourceExpressions?.getOrNull(index), env)
                if (env.containsLocal(name)) env.set(name, initialized)
                else env.define(name, initialized, runtimeType(initialized))
            }
            return
        }
        if (targets.size != values.size) throw RuntimeGoError("assignment count mismatch")
        val locations = targets.map { resolveTarget(it, env) }
        assignToLocations(locations, operator, assignedValues(locations, values, sourceExpressions, env),
            if (operator == TokenKind.ASSIGN) emptyList() else locations.map { it.get() })
    }

    private fun assignedValues(
        locations: List<RuntimeTarget>,
        values: List<Any?>,
        sourceExpressions: List<Expression>?,
        env: Environment
    ): List<Any?> = values.mapIndexed { index, value ->
        if (locations[index].type?.let { underlying(it) is InterfaceGoType } == true)
            defaultRuneValue(value, sourceExpressions?.getOrNull(index), env) else value
    }

    private fun assignToLocations(
        locations: List<RuntimeTarget>,
        operator: TokenKind,
        values: List<Any?>,
        previous: List<Any?> = emptyList()
    ) {
        if (locations.size != values.size) throw RuntimeGoError("assignment count mismatch")
        locations.indices.forEach { i ->
            val value = if (operator == TokenKind.ASSIGN) values[i] else binary(previous[i], compoundOperator(operator), values[i])
            locations[i].set(value)
        }
    }

    private suspend fun resolveTarget(target: Expression, env: Environment): RuntimeTarget = when (target) {
        is ParenthesizedExpression -> resolveTarget(target.expression, env)
        is NameExpression -> if (target.name == "_") RuntimeTarget({ null }, {})
            else RuntimeTarget({ env.get(target.name) }, { env.set(target.name, it) }, env.typeOf(target.name))
        is IndexExpression -> {
            val receiver = evaluate(target.receiver, env)
            val key = evaluate(target.index, env)
            when (receiver) {
                is GoSlice -> {
                    val index = number(key, "index").toInt()
                    RuntimeTarget({ receiver.get(index) }, { receiver.set(index, it) }, receiver.elementType)
                }
                is GoArray -> {
                    val index = number(key, "index").toInt()
                    RuntimeTarget({ arrayElement(receiver, index.toLong()) }, { setArrayElement(receiver, index.toLong(), it) }, receiver.elementType)
                }
                is GoPointer -> {
                    val index = number(key, "index").toInt()
                    RuntimeTarget({
                        val array = receiver.get() as? GoArray ?: throw RuntimeGoError("index requires pointer to array")
                        arrayElement(array, index.toLong())
                    }, {
                        val array = receiver.get() as? GoArray ?: throw RuntimeGoError("index assignment requires pointer to array")
                        setArrayElement(array, index.toLong(), it)
                    }, (receiver.pointeeType?.let { underlying(it) as? ArrayGoType })?.element)
                }
                is GoMap -> {
                    val mapKey = mapKey(key, receiver.keyType)
                    RuntimeTarget(
                        { if (receiver.values.containsKey(mapKey)) receiver.values[mapKey] else receiver.elementZero },
                        { receiver.values[mapKey] = copyForType(it, receiver.valueType) },
                        receiver.valueType
                    )
                }
                is GoNilValue -> {
                    val mapType = underlying(receiver.type) as? MapGoType
                        ?: throw RuntimeGoError("cannot assign through index")
                    mapKey(key, mapType.key)
                    RuntimeTarget({ zeroValue(mapType.value) }, { throw RuntimeGoError("assignment to entry in nil map") }, mapType.value)
                }
                else -> throw RuntimeGoError("cannot assign through index")
            }
        }
        is SelectorExpression -> {
            val receiver = evaluate(target.receiver, env)
            val field = pointerToStructField(receiver, target.field)
            RuntimeTarget({ field.get() }, { value -> field.set(copyForType(value, field.pointeeType ?: runtimeType(field.get()) ?: NamedGoType("<unknown>"))) }, field.pointeeType)
        }
        is UnaryExpression -> {
            if (target.operator != TokenKind.MUL) throw RuntimeGoError("invalid assignment target")
            val pointer = evaluate(target.operand, env) as? GoPointer ?: throw RuntimeGoError("dereference of non-pointer")
            RuntimeTarget({ pointer.get() }, { value ->
                pointer.set(copyForType(value, pointer.pointeeType ?: runtimeType(pointer.get()) ?: NamedGoType("<unknown>")))
            }, pointer.pointeeType)
        }
        else -> throw RuntimeGoError("invalid assignment target")
    }

    private suspend fun executeSelect(statement: SelectStatement, env: Environment, labels: Set<String>) {
        val operations = statement.cases.mapIndexedNotNull { caseIndex, clause ->
            when (val communication = clause.communication) {
                null -> null
                is SendStatement -> {
                    val channelValue = evaluate(communication.channel, env)
                    val sendValue = evaluate(communication.value, env)
                    val channel = selectChannelOrNull(channelValue) ?: return@mapIndexedNotNull null
                    SelectSend(caseIndex, channel, copyForType(sendValue, channel.elementType))
                }
                is ExpressionStatement -> {
                    val receive = communication.expression.unparenthesized() as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("invalid select receive clause")
                    val channel = selectChannelOrNull(evaluate(receive.operand, env)) ?: return@mapIndexedNotNull null
                    SelectReceive(caseIndex, channel, null)
                }
                is AssignmentStatement -> {
                    val receive = communication.values.singleOrNull()?.unparenthesized() as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("select assignment must receive from a channel")
                    val channel = selectChannelOrNull(evaluate(receive.operand, env)) ?: return@mapIndexedNotNull null
                    SelectReceive(caseIndex, channel, communication)
                }
                else -> throw RuntimeGoError("invalid select communication clause")
            }
        }
        val defaultIndex = statement.cases.indexOfFirst { it.communication == null }
        for (operation in operations.shuffled()) {
            when (operation) {
                is SelectSend -> if (operation.channel.trySend(operation.value)) {
                    executeSelectedCase(statement.cases[operation.caseIndex], env, labels)
                    return
                }
                is SelectReceive -> operation.channel.tryReceive()?.let { received ->
                    executeSelectedCase(statement.cases[operation.caseIndex], env, labels, operation.assignment, received)
                    return
                }
            }
        }
        if (defaultIndex >= 0) {
            executeSelectedCase(statement.cases[defaultIndex], env, labels)
            return
        }
        if (operations.isEmpty()) awaitCancellation()
        val selected = try {
            selectUnbiased<SelectSelection> {
                operations.forEach { operation ->
                    when (operation) {
                        is SelectSend -> operation.channel.queue.onSend(operation.value) {
                            operation.channel.recordSelectSend()
                            SelectSelection(operation.caseIndex, null)
                        }
                        is SelectReceive -> operation.channel.queue.onReceiveCatching { result ->
                            SelectSelection(operation.caseIndex, operation.channel.decode(result))
                        }
                    }
                }
            }
        } catch (_: kotlinx.coroutines.channels.ClosedSendChannelException) {
            throw RuntimeGoError("send on closed channel")
        }
        val clause = statement.cases[selected.caseIndex]
        val receive = operations.filterIsInstance<SelectReceive>().firstOrNull { it.caseIndex == selected.caseIndex }
        executeSelectedCase(clause, env, labels, receive?.assignment, selected.received)
    }

    private fun selectChannelOrNull(value: Any?): GoChannel? = when (value) {
        is GoChannel -> value
        is GoNilValue -> if (underlying(value.type) is ChannelGoType) null else throw RuntimeGoError("select operation requires a channel")
        else -> throw RuntimeGoError("select operation requires a channel")
    }

    private suspend fun executeSelectedCase(
        clause: SelectCase,
        parent: Environment,
        labels: Set<String>,
        assignment: AssignmentStatement? = null,
        received: GoReceiveResult? = null
    ) {
        val env = parent.child()
        predeclareTypes(clause.statements, env)
        if (assignment != null && received != null) {
            assignValues(assignment.targets, assignment.operator, expandValues(listOf(received), assignment.targets.size), env)
        }
        try { for (statement in clause.statements) execute(statement, env) }
        catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal }
    }

    private suspend fun executeSwitch(statement: SwitchStatement, env: Environment, labels: Set<String>) {
        val scope = env.child()
        statement.init?.let { execute(it, scope) }
        val tag = statement.tag?.let { copyValue(evaluate(it, scope)) } ?: if (statement.tag == null) true else null
        var selected = -1
        for ((clauseIndex, clause) in statement.clauses.withIndex()) {
            if (clause.expressions?.any { goEqual(evaluate(it, scope), tag) } == true) {
                selected = clauseIndex
                break
            }
        }
        if (selected < 0) selected = statement.clauses.indexOfFirst { it.expressions == null }
        if (selected < 0) return
        var index = selected
        while (index < statement.clauses.size) {
            try {
                val caseScope = scope.child()
                predeclareTypes(statement.clauses[index].statements, caseScope)
                statement.clauses[index].statements.forEach { execute(it, caseScope) }
                return
            } catch (_: FallthroughSignal) {
                if (index == statement.clauses.lastIndex) throw RuntimeGoError("fallthrough in final switch clause")
                index++
            } catch (signal: BreakSignal) {
                if (!targets(signal.label, labels)) throw signal
                return
            }
        }
    }

    private suspend fun executeTypeSwitch(statement: TypeSwitchStatement, env: Environment, labels: Set<String>) {
        val scope = env.child()
        statement.init?.let { execute(it, scope) }
        val value = copyValue(evaluate(statement.guard.expression, scope))
        val dynamicType = (value as? GoInterfaceValue)?.dynamicType
        val resolvedClauses = statement.clauses.map { clause ->
            clause.types?.map { resolveRuntimeType(it, scope) }
        }
        val selected = statement.clauses.indices.firstOrNull { clauseIndex ->
            resolvedClauses[clauseIndex]?.any { type ->
                if (type == NamedGoType("nil")) value == null
                else dynamicType != null && matchesDynamicType(dynamicType, type)
            } == true
        } ?: statement.clauses.indexOfFirst { clause -> clause.types == null }
        if (selected < 0) return
        val clause = statement.clauses[selected]
        val singleType = resolvedClauses[selected]?.singleOrNull()?.takeUnless { it == NamedGoType("nil") }
        val caseValue = when {
            singleType == null -> value
            underlying(singleType) is InterfaceGoType -> value
            else -> (value as? GoInterfaceValue)?.value
        }
        val caseScope = scope.child()
        predeclareTypes(clause.statements, caseScope)
        if (statement.guard.name != null && statement.guard.name != "_")
            caseScope.define(statement.guard.name, caseValue, singleType ?: interfaceOperandType(statement.guard.expression, scope))
        try {
            clause.statements.forEach { execute(it, caseScope) }
        } catch (signal: BreakSignal) {
            if (!targets(signal.label, labels)) throw signal
        } catch (_: FallthroughSignal) {
            throw RuntimeGoError("fallthrough in type switch")
        }
    }

    private fun matchesDynamicType(dynamicType: GoTypeSyntax, target: GoTypeSyntax): Boolean {
        val interfaceType = underlying(target) as? InterfaceGoType
        return if (interfaceType != null) implementsInterface(dynamicType, interfaceType) else sameRuntimeType(dynamicType, target)
    }

    private fun sameRuntimeType(left: GoTypeSyntax, right: GoTypeSyntax): Boolean =
        canonicalAliasType(left) == canonicalAliasType(right)

    private fun canonicalAliasType(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        NamedGoType("byte") -> if (!typeDefinitions.containsKey("byte")) NamedGoType("uint8") else type
        NamedGoType("rune") -> if (!typeDefinitions.containsKey("rune")) NamedGoType("int32") else type
        is PointerGoType -> PointerGoType(canonicalAliasType(type.element))
        is SliceGoType -> SliceGoType(canonicalAliasType(type.element))
        is ArrayGoType -> ArrayGoType(type.length, canonicalAliasType(type.element))
        is MapGoType -> MapGoType(canonicalAliasType(type.key), canonicalAliasType(type.value))
        is ChannelGoType -> ChannelGoType(canonicalAliasType(type.element), type.direction)
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = canonicalAliasType(it.type)) },
            type.results.map(::canonicalAliasType)
        )
        is StructGoType -> StructGoType(type.fields.map { it.copy(type = canonicalAliasType(it.type), tag = it.tag.orEmpty()) })
        is InterfaceGoType -> InterfaceGoType(
            type.methods.map { method -> method.copy(
                parameters = method.parameters.map { it.copy(type = canonicalAliasType(it.type)) },
                results = method.results.map(::canonicalAliasType)
            ) },
            type.embeddedTypes.map(::canonicalAliasType)
        )
        else -> type
    }

    private fun interfaceOperandType(expression: Expression, env: Environment): GoTypeSyntax = when (expression) {
        is NameExpression -> env.typeOf(expression.name) ?: InterfaceGoType(emptyList())
        is ParenthesizedExpression -> interfaceOperandType(expression.expression, env)
        else -> InterfaceGoType(emptyList())
    }

    private suspend fun executeRange(range: RangeClause, body: BlockStatement, env: Environment, labels: Set<String>) {
        val onlyIndexIsUsed = range.targets.size <= 1 || range.targets.getOrNull(1).isBlankIdentifier()
        if (onlyIndexIsUsed) {
            val arrayLength = staticRangeArrayLength(range.expression, env)
            if (arrayLength != null) {
                rangeIndexed(arrayLength, range, body, env, labels) { index -> listOf(index.toLong()) }
                return
            }
        }
        val evaluated = copyValue(evaluate(range.expression, env))
        val pointerToArray = (evaluated as? GoPointer)?.takeIf { pointer ->
            pointer.pointeeType?.let { underlying(it) is ArrayGoType } == true || (!pointer.isNil && pointer.get() is GoArray)
        }
        val value = if (pointerToArray == null) evaluated else pointerToArray
        when (value) {
            is GoChannel -> while (true) {
                val received = value.receive()
                if (!received.ok) break
                if (range.targets.isNotEmpty()) {
                    val values = listOf(received.value).take(range.targets.size)
                    assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, env)
                }
                try { executeBlock(body, env) }
                catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
            }
            is GoNilValue -> when (underlying(value.type)) {
                is SliceGoType, is MapGoType -> Unit
                is ChannelGoType -> awaitCancellation()
                else -> throw RuntimeGoError("range over this value is not implemented")
            }
            is GoString -> {
                var byteIndex = 0
                while (byteIndex < value.bytes.size) {
                    yield()
                    val (cp, width) = decodeUtf8Rune(value.bytes, byteIndex)
                    if (range.targets.isNotEmpty()) {
                        val values = listOf(byteIndex.toLong(), GoInteger(cp.toLong(), NamedGoType("rune"))).take(range.targets.size)
                        assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, env)
                    }
                    try { executeBlock(body, env) }
                    catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                    catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                    byteIndex += width
                }
            }
            is GoSlice -> rangeIndexed(value.length, range, body, env, labels) { i ->
                if (onlyIndexIsUsed) listOf(i.toLong()) else listOf(i.toLong(), value.get(i))
            }
            is GoPointer -> {
                val arrayLength = staticRangeArrayLength(range.expression, env)
                    ?: if (!value.isNil) (value.get() as? GoArray)?.values?.size
                        ?: throw RuntimeGoError("range over pointer requires an array")
                    else throw RuntimeGoError("range over nil pointer requires a known array length")
                rangeIndexed(arrayLength, range, body, env, labels) { index ->
                    if (onlyIndexIsUsed) listOf(index.toLong()) else {
                        val array = value.get() as? GoArray ?: throw RuntimeGoError("range over pointer requires an array")
                        listOf(index.toLong(), array.values[index])
                    }
                }
            }
            is GoArray -> rangeIndexed(value.values.size, range, body, env, labels) { i ->
                if (onlyIndexIsUsed) listOf(i.toLong()) else listOf(i.toLong(), value.values[i])
            }
            is GoMap -> {
                // Snapshot key order, but read membership and values as each entry is reached.
                // Deleting a not-yet-reached entry must suppress that iteration value.
                for (key in value.values.keys.toList()) {
                    yield()
                    if (!value.values.containsKey(key)) continue
                    val entryValue = if (onlyIndexIsUsed) null else value.values[key]
                    if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN,
                        (if (onlyIndexIsUsed) listOf(copyValue(key.value)) else listOf(copyValue(key.value), entryValue))
                            .take(range.targets.size), env)
                    try { executeBlock(body, env) }
                    catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                    catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                }
            }
            else -> throw RuntimeGoError("range over this value is not implemented")
        }
    }

    private fun Expression?.isBlankIdentifier(): Boolean = when (this) {
        is NameExpression -> name == "_"
        is ParenthesizedExpression -> expression.isBlankIdentifier()
        else -> false
    }

    private fun staticRangeArrayLength(expression: Expression, env: Environment): Int? {
        val type = staticExpressionType(expression, env) ?: return null
        val actual = underlying(type)
        val array = when (actual) {
            is ArrayGoType -> actual
            is PointerGoType -> underlying(actual.element) as? ArrayGoType
            else -> null
        } ?: return null
        val length = array.length?.let { integerLiteral(it, env).intValueExact() }
            ?: arrayCompositeLiteral(expression, env)?.let { inferredArrayLiteralLength(it, env) }
            ?: return null
        if (length < 0) throw RuntimeGoError("negative array length")
        return length
    }

    private fun pointerArrayLength(pointer: GoPointer, env: Environment?): Long {
        val arrayType = pointer.pointeeType?.let(::underlying) as? ArrayGoType
        if (arrayType != null) {
            arrayType.length?.let { return integerLiteral(it, env).longValueExact() }
        }
        if (!pointer.isNil) {
            val array = pointer.get() as? GoArray
                ?: throw RuntimeGoError("len or cap requires pointer to array")
            return array.values.size.toLong()
        }
        throw RuntimeGoError("len or cap requires pointer to array with a known length")
    }

    private fun arrayCompositeLiteral(expression: Expression, env: Environment): CompositeLiteral? = when (expression) {
        is CompositeLiteral -> expression.takeIf { underlying(resolveRuntimeType(it.type, env)) is ArrayGoType }
        is ParenthesizedExpression -> arrayCompositeLiteral(expression.expression, env)
        is UnaryExpression -> if (expression.operator == TokenKind.AND) arrayCompositeLiteral(expression.operand, env) else null
        else -> null
    }

    private fun inferredArrayLiteralLength(literal: CompositeLiteral, env: Environment): Int {
        var nextIndex = 0
        var largestIndex = -1
        literal.elements.forEach { element ->
            val index = element.key?.let { integerLiteral(it, env).intValueExact() } ?: nextIndex
            if (index < 0) throw RuntimeGoError("negative array index")
            largestIndex = maxOf(largestIndex, index)
            nextIndex = index + 1
        }
        return largestIndex + 1
    }

    private fun staticExpressionType(expression: Expression, env: Environment): GoTypeSyntax? = when (expression) {
        is NameExpression -> env.typeOf(expression.name) ?: functions[expression.name]?.let { function ->
            FunctionGoType(function.parameterTypes.mapIndexed { index, type ->
                ParameterSyntax(function.parameters.getOrNull(index), type,
                    function.variadic && index == function.parameterTypes.lastIndex)
            }, function.resultTypes)
        }
        is ParenthesizedExpression -> staticExpressionType(expression.expression, env)
        is CompositeLiteral -> resolveRuntimeType(expression.type, env)
        is TypeAssertionExpression -> resolveRuntimeType(expression.type, env)
        is SelectorExpression -> {
            val receiverType = staticExpressionType(expression.receiver, env)?.let { resolveRuntimeType(it, env) }
            val method = receiverType?.let { methods[methodKey(it, expression.field)] }
            if (method != null) FunctionGoType(method.parameterTypes.mapIndexed { index, type ->
                ParameterSyntax(method.parameters.getOrNull(index), type,
                    method.variadic && index == method.parameterTypes.lastIndex)
            }, method.resultTypes)
            else {
                val struct = receiverType?.let(::underlying).let { if (it is PointerGoType) underlying(it.element) else it }
                when (struct) {
                    is StructGoType -> staticPromotedFieldType(struct, expression.field, env)
                    is InterfaceGoType -> interfaceMethodsRuntime(struct)[expression.field]
                    else -> null
                }
            }
        }
        is UnaryExpression -> when (expression.operator) {
            TokenKind.AND -> staticExpressionType(expression.operand, env)?.let(::PointerGoType)
            TokenKind.MUL -> (staticExpressionType(expression.operand, env)?.let(::underlying) as? PointerGoType)?.element
            else -> null
        }
        is CallExpression -> {
            runtimeTypeConversion(expression, env)?.let { return it }
            val functionType = when (val target = expression.function) {
                is FunctionLiteralExpression -> FunctionGoType(target.parameters, target.results)
                else -> staticExpressionType(target, env)?.let(::underlying) as? FunctionGoType
            }
            functionType?.results?.singleOrNull()?.let { resolveRuntimeType(it, env) }
        }
        is IndexExpression -> when (val receiver = staticExpressionType(expression.receiver, env)?.let(::underlying)) {
            is ArrayGoType -> receiver.element
            is SliceGoType -> receiver.element
            is MapGoType -> receiver.value
            else -> null
        }
        else -> null
    }

    private fun staticPromotedFieldType(type: StructGoType, name: String, env: Environment): GoTypeSyntax? {
        data class Node(val type: GoTypeSyntax, val ancestors: Set<String>)
        var level = listOf(Node(type, emptySet()))
        while (level.isNotEmpty()) {
            val matches = mutableListOf<GoTypeSyntax>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                val actual = when (val resolved = underlying(resolveRuntimeType(node.type, env))) {
                    is PointerGoType -> underlying(resolved.element)
                    else -> resolved
                } as? StructGoType ?: return@forEach
                actual.fields.forEach { field ->
                    if (name in field.names) matches += resolveRuntimeType(field.type, env)
                    if (field.names.isEmpty()) {
                        val embedded = resolveRuntimeType(field.type, env)
                        val key = "${actual.hashCode()}:${embedded}"
                        if (key !in node.ancestors) next += Node(embedded, node.ancestors + key)
                    }
                }
            }
            if (matches.isNotEmpty()) return matches.singleOrNull()
            level = next
        }
        return null
    }

    private suspend fun rangeIndexed(
        length: Int,
        range: RangeClause,
        body: BlockStatement,
        env: Environment,
        labels: Set<String>,
        values: (Int) -> List<Any?>
    ) {
        for (i in 0 until length) {
            yield()
            if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values(i).take(range.targets.size), env)
            try { executeBlock(body, env) }
            catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
            catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
        }
    }

    private suspend fun initialize(names: List<String>, expressions: List<Expression>, env: Environment, type: GoTypeSyntax? = null) {
        val resolvedType = type?.let { resolveRuntimeType(it, env) }
        val values = expandValues(evaluateRhs(expressions, names.size, env), names.size)
        if (values.isNotEmpty() && values.size != names.size) throw RuntimeGoError("initializer count mismatch")
        names.forEachIndexed { i, name ->
            val value = if (values.isNotEmpty()) values[i].let {
                val sourceExpression = expressions.getOrNull(i)
                if (resolvedType != null) convert(resolvedType, defaultRuneValue(it, sourceExpression, env))
                else defaultConstantValue(it, sourceExpression, env)
            }
            else if (resolvedType != null) zeroValue(resolvedType) else GoInteger(0L, NamedGoType("int"))
            if (name != "_") env.define(name, value, resolvedType ?: runtimeType(value))
        }
    }

    private suspend fun initializeConstant(declaration: ConstantDeclaration) {
        initializeConstantIn(declaration, globals)
    }

    private suspend fun initializeConstantIn(declaration: ConstantDeclaration, target: Environment) {
        val resolvedType = declaration.type?.let { resolveRuntimeType(it, target) }
        val scope = target.child()
        scope.define("iota", BigInteger.valueOf(declaration.iotaIndex.toLong()))
        val values = expandValues(declaration.values.map { evaluate(it, scope) }, declaration.names.size)
        if (values.size != declaration.names.size) throw RuntimeGoError("constant initializer count mismatch")
        declaration.names.zip(values).forEachIndexed { index, (name, value) ->
            val expression = declaration.values.getOrNull(index)
            val initialized = resolvedType?.let { convert(it, defaultRuneValue(value, expression, scope)) } ?: value
            val type = resolvedType ?: if (expression != null && isRuneConstantExpression(expression, scope)) untypedRuneRuntimeType else null
            if (name != "_") target.define(name, initialized, type)
        }
    }

    private fun <T> orderPackageDeclarations(
        declarations: List<T>,
        names: (T) -> List<String>,
        expressions: (T) -> List<Expression>,
        includeFunctionDependencies: Boolean
    ): List<T> {
        val declarationByName = mutableMapOf<String, Int>()
        declarations.forEachIndexed { index, declaration -> names(declaration).forEach { name ->
            if (name != "_") declarationByName[name] = index
        } }
        val dependencies = declarations.indices.map { index ->
            val refs = expressions(declarations[index]).flatMapTo(linkedSetOf(), ::expressionNames)
            if (includeFunctionDependencies) addFunctionDependencies(refs)
            refs.mapNotNullTo(linkedSetOf()) { declarationByName[it] }
        }
        val initialized = BooleanArray(declarations.size)
        val ordered = mutableListOf<T>()
        while (ordered.size < declarations.size) {
            val next = declarations.indices.firstOrNull { i ->
                !initialized[i] && dependencies[i].all { initialized[it] }
            } ?: throw RuntimeGoError("package initialization cycle")
            initialized[next] = true
            ordered += declarations[next]
        }
        return ordered
    }

    private fun addFunctionDependencies(references: MutableSet<String>) {
        val pending = ArrayDeque(references.filter { it in functions })
        val visited = mutableSetOf<String>()
        while (pending.isNotEmpty()) {
            val name = pending.removeFirst()
            if (!visited.add(name)) continue
            val function = functions[name] ?: continue
            val body = function.body ?: continue
            val functionReferences = statementNames(body) - functionLocalNames(function)
            functionReferences.filter { it !in references && it in functions }.forEach(pending::addLast)
            references += functionReferences
        }
    }

    private fun expressionNames(expression: Expression): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> expressionNames(expression.operand)
        is BinaryExpression -> expressionNames(expression.left) + expressionNames(expression.right)
        is CallExpression -> expressionNames(expression.function) + expression.arguments.flatMap(::expressionNames)
        is SelectorExpression -> expressionNames(expression.receiver)
        is IndexExpression -> expressionNames(expression.receiver) + expressionNames(expression.index)
        is SliceExpression -> expressionNames(expression.receiver) + listOfNotNull(expression.low, expression.high).flatMap(::expressionNames)
        is TypeAssertionExpression -> expressionNames(expression.receiver)
        is TypeSwitchGuardExpression -> expressionNames(expression.receiver)
        is ParenthesizedExpression -> expressionNames(expression.expression)
        is CompositeLiteral -> expression.elements.flatMapTo(linkedSetOf()) { element ->
            (element.key?.let(::expressionNames) ?: emptySet()) + expressionNames(element.value)
        }
        is ElidedCompositeLiteral -> expression.elements.flatMapTo(linkedSetOf()) { element ->
            (element.key?.let(::expressionNames) ?: emptySet()) + expressionNames(element.value)
        }
        is FunctionLiteralExpression -> statementNames(expression.body) - functionLocalNames(expression.parameters.mapNotNull { it.name }.toSet(), expression.body)
    }

    private fun statementNames(statement: Statement): Set<String> = when (statement) {
        EmptyStatement -> emptySet()
        is LabeledStatement -> statementNames(statement.statement)
        is DeclarationStatement -> statement.declarations.flatMapTo(linkedSetOf()) { declaration -> when (declaration) {
            is VariableDeclaration -> declaration.values.flatMap(::expressionNames)
            is ConstantDeclaration -> declaration.values.flatMap(::expressionNames)
            else -> emptyList()
        } }
        is BlockStatement -> statement.statements.flatMapTo(linkedSetOf(), ::statementNames)
        is VariableStatement -> statement.values.flatMapTo(linkedSetOf(), ::expressionNames)
        is ReturnStatement -> statement.values.flatMapTo(linkedSetOf(), ::expressionNames)
        is ExpressionStatement -> expressionNames(statement.expression)
        is SendStatement -> expressionNames(statement.channel) + expressionNames(statement.value)
        is GoStatement -> expressionNames(statement.call)
        is DeferStatement -> expressionNames(statement.call)
        is BranchStatement -> emptySet()
        is SelectStatement -> statement.cases.flatMapTo(linkedSetOf()) { clause ->
            (clause.communication?.let(::statementNames) ?: emptySet()) + clause.statements.flatMap(::statementNames)
        }
        is SwitchStatement -> (statement.init?.let(::statementNames) ?: emptySet()) +
            (statement.tag?.let(::expressionNames) ?: emptySet()) + statement.clauses.flatMap { clause ->
                (clause.expressions?.flatMap(::expressionNames) ?: emptyList()) + clause.statements.flatMap(::statementNames)
            }
        is TypeSwitchStatement -> (statement.init?.let(::statementNames) ?: emptySet()) + expressionNames(statement.guard.expression) +
            statement.clauses.flatMap { it.statements.flatMap(::statementNames) }
        is AssignmentStatement -> statement.targets.flatMapTo(linkedSetOf(), ::expressionNames) + statement.values.flatMap(::expressionNames)
        is IncrementStatement -> expressionNames(statement.target)
        is IfStatement -> (statement.init?.let(::statementNames) ?: emptySet()) + expressionNames(statement.condition) +
            statementNames(statement.thenBranch) + (statement.elseBranch?.let(::statementNames) ?: emptySet())
        is ForStatement -> (statement.init?.let(::statementNames) ?: emptySet()) +
            (statement.condition?.let(::expressionNames) ?: emptySet()) + (statement.post?.let(::statementNames) ?: emptySet()) +
            (statement.rangeClause?.let { expressionNames(it.expression) + it.targets.flatMap(::expressionNames) } ?: emptySet()) + statementNames(statement.body)
    }

    private fun functionLocalNames(function: FunctionDeclaration): Set<String> =
        functionLocalNames(function.parameters.filterNotNull().toSet() + listOfNotNull(function.receiver?.name), function.body)

    private fun functionLocalNames(initial: Set<String>, body: BlockStatement?): Set<String> {
        if (body == null) return initial
        val names = initial.toMutableSet()
        fun collect(statement: Statement) {
            when (statement) {
                is LabeledStatement -> collect(statement.statement)
                is DeclarationStatement -> statement.declarations.forEach { declaration -> when (declaration) {
                    is VariableDeclaration -> names += declaration.names
                    is ConstantDeclaration -> names += declaration.names
                    is TypeDeclaration -> names += declaration.name
                    else -> Unit
                } }
                is VariableStatement -> names += statement.names
                is AssignmentStatement -> if (statement.operator == TokenKind.DEFINE)
                    names += statement.targets.mapNotNull { (it as? NameExpression)?.name }
                is BlockStatement -> statement.statements.forEach(::collect)
                is IfStatement -> { statement.init?.let(::collect); collect(statement.thenBranch); statement.elseBranch?.let(::collect) }
                is ForStatement -> {
                    statement.rangeClause?.takeIf { it.operator == TokenKind.DEFINE }?.targets?.mapNotNullTo(names) { (it as? NameExpression)?.name }
                    statement.init?.let(::collect); statement.post?.let(::collect); collect(statement.body)
                }
                is SwitchStatement -> { statement.init?.let(::collect); statement.clauses.forEach { it.statements.forEach(::collect) } }
                is TypeSwitchStatement -> {
                    statement.init?.let(::collect)
                    statement.guard.name?.let(names::add)
                    statement.clauses.forEach { it.statements.forEach(::collect) }
                }
                is SelectStatement -> statement.cases.forEach { clause ->
                    clause.communication?.let(::collect); clause.statements.forEach(::collect)
                }
                else -> Unit
            }
        }
        collect(body)
        return names
    }

    private suspend fun evaluateRhs(expressions: List<Expression>, arity: Int, env: Environment): List<Any?> {
        if (expressions.size == 1 && arity == 2 && expressions[0] is TypeAssertionExpression) {
            val assertion = expressions[0] as TypeAssertionExpression
            return listOf(assertType(evaluate(assertion.receiver, env), assertion.type))
        }
        if (expressions.size == 1 && expressions[0] is UnaryExpression &&
            (expressions[0] as UnaryExpression).operator == TokenKind.ARROW) {
            val receive = expressions[0] as UnaryExpression
            return listOf(receiveResult(evaluate(receive.operand, env)))
        }
        if (expressions.size == 1 && arity == 2 && expressions[0] is IndexExpression) {
            val index = expressions[0] as IndexExpression
            val receiver = evaluate(index.receiver, env)
            val key = evaluate(index.index, env)
            if (receiver is GoMap) {
                val mapKey = mapKey(key, receiver.keyType)
                val found = receiver.values.containsKey(mapKey)
                return listOf(MapLookupResult(if (found) receiver.values[mapKey] else receiver.elementZero, found))
            }
            if (receiver is GoNilValue && underlying(receiver.type) is MapGoType) {
                val mapType = underlying(receiver.type) as MapGoType
                return listOf(MapLookupResult(zeroValue(mapType.value), false))
            }
        }
        return expressions.map { evaluate(it, env) }
    }

private suspend fun evaluate(expression: Expression, env: Environment): Any? = when (expression) {
        is NameExpression -> {
            val binding = env.binding(expression.name)
            if (binding != null) binding.value
            else typeDefinitions[expression.name]?.let { TypeValue(NamedGoType(expression.name)) }
                ?: functions[expression.name]?.let { FunctionValue(it, globals) }
                ?: when (expression.name) {
                    "true" -> true
                    "false" -> false
                    "nil" -> null
                    "make", "new", "close", "len", "cap", "append", "copy", "delete", "print", "println", "panic", "recover", "complex", "real", "imag" -> BuiltinValue(expression.name)
                    in builtinTypes -> TypeValue(NamedGoType(expression.name))
                    else -> throw RuntimeGoError("undefined: ${expression.name}")
                }
        }
        is LiteralExpression -> literal(expression.token)
        is ParenthesizedExpression -> evaluate(expression.expression, env)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.AND -> addressOf(expression.operand, env)
            TokenKind.MUL -> {
                val pointer = evaluate(expression.operand, env) as? GoPointer
                    ?: throw RuntimeGoError("dereference of non-pointer")
                val pointedType = pointer.pointeeType
                    ?: throw RuntimeGoError("pointer has no static element type")
                copyForType(pointer.get(), pointedType)
            }
            TokenKind.ARROW -> receiveResult(evaluate(expression.operand, env)).value
            else -> unary(expression.operator, evaluate(expression.operand, env))
        }
        is BinaryExpression -> {
            val left = copyValue(evaluate(expression.left, env))
            if (expression.operator == TokenKind.LAND && !booleanValue(left, "&&")) false
            else if (expression.operator == TokenKind.LOR && booleanValue(left, "||")) true
            else binary(left, expression.operator, copyValue(evaluate(expression.right, env)))
        }
        is SelectorExpression -> {
            val methodReceiverType = methodExpressionReceiver(expression.receiver, env)
            if (methodReceiverType != null) {
                val method = runtimeMethodSet(methodReceiverType)[expression.field]
                    ?: throw RuntimeGoError("undefined method ${expression.field} on $methodReceiverType")
                MethodExpressionValue(
                    methodReceiverType,
                    expression.field,
                    FunctionGoType(listOf(ParameterSyntax(null, methodReceiverType)) + method.parameters, method.results)
                )
            } else if (expression.receiver is NameExpression && expression.receiver.name in fmtAliases &&
                !env.contains(expression.receiver.name)) BuiltinValue(expression.field)
            else {
                val receiver = evaluate(expression.receiver, env)
                if (receiver is GoPointer && receiver.isNil) {
                    val baseType = receiver.pointeeType ?: throw RuntimeGoError("nil pointer has no static type")
                    val method = methods["${methodKey(baseType, expression.field)}"]
                        ?: throw RuntimeGoError("unknown field or method: ${expression.field}")
                    if (method.receiver?.type !is PointerGoType)
                        throw RuntimeGoError("invalid memory address or nil pointer dereference")
                    MethodValue(method, receiver)
                } else if (receiver is GoInterfaceValue) {
                    val method = methods["${methodKey(receiver.dynamicType, expression.field)}"]
                        ?: throw RuntimeGoError("unknown interface method: ${expression.field}")
                    val pointerReceiver = method.receiver?.type is PointerGoType
                    val boundReceiver = when {
                        pointerReceiver && receiver.value is GoPointer -> receiver.value
                        pointerReceiver -> throw RuntimeGoError("interface value does not contain a pointer receiver")
                        receiver.value is GoPointer -> copyValue(dereference(receiver.value))
                        else -> copyValue(receiver.value)
                    }
                    MethodValue(method, boundReceiver)
                } else {
                    selectStructMember(receiver, expression.field, expression.receiver, env)
                }
            }
        }
        is CallExpression -> call(expression, env)
        is IndexExpression -> index(evaluate(expression.receiver, env), evaluate(expression.index, env))
        is SliceExpression -> slice(evaluate(expression.receiver, env), expression.low?.let { evaluate(it, env) },
            expression.high?.let { evaluate(it, env) })
        is TypeAssertionExpression -> {
            val assertion = assertType(evaluate(expression.receiver, env), resolveRuntimeType(expression.type, env))
            if (!assertion.ok) throw RuntimeGoError("type assertion failed: ${assertion.dynamicType} is not ${expression.type}")
            assertion.value
        }
        is TypeSwitchGuardExpression -> throw RuntimeGoError("type switch guard used outside a type switch")
        is TypeExpression -> TypeValue(resolveRuntimeType(expression.type, env))
        is CompositeLiteral -> composite(expression.copy(type = resolveRuntimeType(expression.type, env)), env)
        is ElidedCompositeLiteral -> throw RuntimeGoError("elided composite literal requires an element type")
        is FunctionLiteralExpression -> {
            val parameters = expression.parameters.map { it.copy(type = resolveRuntimeType(it.type, env)) }
            val results = expression.results.map { resolveRuntimeType(it, env) }
            val declaration = FunctionDeclaration(
                "<function literal>", parameters.map { it.name }, expression.body,
                parameters.map { it.type }, results, null, expression.variadic, expression.resultNames
            )
            FunctionValue(declaration, env, FunctionGoType(parameters, results))
        }
    }

    private fun methodExpressionReceiver(expression: Expression, env: Environment): GoTypeSyntax? = when (expression) {
        is NameExpression -> if (env.contains(expression.name)) null else {
            env.typeBinding(expression.name) ?: typeDefinitions[expression.name]?.let { NamedGoType(expression.name) }
                ?: if (expression.name in builtinTypes) NamedGoType(expression.name) else null
        }
        is ParenthesizedExpression -> methodExpressionReceiver(expression.expression, env)
        is UnaryExpression -> if (expression.operator == TokenKind.MUL) {
            methodExpressionReceiver(expression.operand, env)?.let(::PointerGoType)
        } else null
        else -> null
    }

    private suspend fun addressOf(expression: Expression, env: Environment): GoPointer = when (expression) {
        is NameExpression -> env.pointer(expression.name)
        is SelectorExpression -> pointerToStructField(evaluate(expression.receiver, env), expression.field)
        is IndexExpression -> {
            val receiver = evaluate(expression.receiver, env)
            val key = number(evaluate(expression.index, env), "index").toInt()
            when (receiver) {
                is GoSlice -> receiver.pointerAt(key)
                is GoArray -> receiver.pointerAt(key)
                is GoPointer -> (receiver.get() as? GoArray)?.pointerAt(key)
                    ?: throw RuntimeGoError("address-of index requires pointer to array")
                else -> throw RuntimeGoError("address-of index requires an array or slice element")
            }
        }
        is UnaryExpression -> if (expression.operator == TokenKind.MUL) {
            evaluate(expression.operand, env) as? GoPointer ?: throw RuntimeGoError("cannot take address through a non-pointer")
        } else throw RuntimeGoError("expression is not addressable")
        is CompositeLiteral -> GoPointer.cell(composite(expression, env), expression.type)
        else -> throw RuntimeGoError("expression is not addressable")
    }

    private fun pointerToStructField(receiver: Any?, name: String): GoPointer {
        data class Node(val value: Any?, val ancestors: Set<String>)
        var level = listOf(Node(receiver, emptySet()))
        while (level.isNotEmpty()) {
            val matches = mutableListOf<GoPointer>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                if (node.value is GoPointer && node.value.isNil)
                    throw RuntimeGoError("invalid memory address or nil pointer dereference")
                val struct = dereference(node.value) as? GoStruct ?: return@forEach
                if (name in struct.fields) matches += struct.pointer(name)
                struct.embeddedFields.forEach { embeddedName ->
                    val embeddedValue = struct.fields[embeddedName] ?: return@forEach
                    val key = "${struct.namedType}.$embeddedName"
                    if (key !in node.ancestors) {
                        val child = if (embeddedValue is GoPointer) embeddedValue else struct.pointer(embeddedName)
                        next += Node(child, node.ancestors + key)
                    }
                }
            }
            if (matches.isNotEmpty()) {
                if (matches.size != 1) throw RuntimeGoError("ambiguous selector $name")
                return matches.single()
            }
            level = next
        }
        throw RuntimeGoError("unknown struct field: $name")
    }

    private suspend fun selectStructMember(receiver: Any?, name: String, receiverExpression: Expression, env: Environment): Any? {
        data class Node(val value: Any?, val ancestors: Set<String>)
        data class Candidate(val owner: GoStruct?, val method: FunctionDeclaration?, val receiver: Any?)
        var level = listOf(Node(receiver, emptySet()))
        while (level.isNotEmpty()) {
            val candidates = mutableListOf<Candidate>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                if (node.value is GoPointer && node.value.isNil) {
                    val embeddedType = node.value.pointeeType
                    if (embeddedType != null) methods[methodKey(embeddedType, name)]?.let {
                        candidates += Candidate(null, it, node.value)
                    }
                    return@forEach
                }
                val current = dereference(node.value)
                if (current is GoInterfaceValue) {
                    methods[methodKey(current.dynamicType, name)]?.let { candidates += Candidate(null, it, current) }
                    return@forEach
                }
                val struct = current as? GoStruct
                if (struct == null) {
                    val valueType = (node.value as? GoPointer)?.pointeeType ?: runtimeType(current) ?: return@forEach
                    methods[methodKey(valueType, name)]?.let { candidates += Candidate(null, it, node.value) }
                    return@forEach
                }
                if (name in struct.fields) candidates += Candidate(struct, null, node.value)
                val receiverType = (node.value as? GoPointer)?.pointeeType
                    ?: struct.namedType?.let(::NamedGoType)
                receiverType?.let { methods[methodKey(it, name)] }?.let { candidates += Candidate(null, it, node.value) }
                struct.embeddedFields.forEach { embeddedName ->
                    val embeddedValue = struct.fields[embeddedName] ?: return@forEach
                    val key = "${struct.namedType}.$embeddedName"
                    if (key !in node.ancestors) {
                        val child = if (embeddedValue is GoPointer) embeddedValue else struct.pointer(embeddedName)
                        next += Node(child, node.ancestors + key)
                    }
                }
            }
            if (candidates.isNotEmpty()) {
                if (candidates.size != 1) throw RuntimeGoError("ambiguous selector $name")
                val candidate = candidates.single()
                candidate.owner?.let { owner -> return owner.fields[name] }
                val method = candidate.method ?: throw RuntimeGoError("unknown selector $name")
                val pointerReceiver = method.receiver?.type is PointerGoType
                val methodReceiver = when {
                    candidate.receiver is GoInterfaceValue -> {
                        val value = candidate.receiver
                        when {
                            pointerReceiver && value.value is GoPointer -> value.value
                            pointerReceiver -> throw RuntimeGoError("interface value does not contain a pointer receiver")
                            value.value is GoPointer -> copyValue(dereference(value.value))
                            else -> copyValue(value.value)
                        }
                    }
                    pointerReceiver && candidate.receiver is GoPointer -> candidate.receiver
                    pointerReceiver -> addressOf(receiverExpression, env)
                    candidate.receiver is GoPointer && candidate.receiver.isNil ->
                        throw RuntimeGoError("invalid memory address or nil pointer dereference")
                    candidate.receiver is GoPointer -> copyValue(dereference(candidate.receiver))
                    else -> copyValue(candidate.receiver)
                }
                return MethodValue(method, methodReceiver)
            }
            level = next
        }
        throw RuntimeGoError("unknown struct field or method: $name")
    }

    private suspend fun call(call: CallExpression, env: Environment): Any? {
        if (call.function is TypeExpression && call.arguments.size == 1 && !call.expandLastArgument) {
            val value = evaluate(call.arguments.single(), env)
            val source = call.arguments.single()
            return convert(resolveRuntimeType(call.function.type, env), defaultRuneValue(value, source, env))
        }
        val builtinName = (call.function as? NameExpression)?.name
        if (builtinName in setOf("len", "cap") && builtinName?.let {
                !env.contains(it) && env.typeBinding(it) == null && !functions.containsKey(it) && !typeDefinitions.containsKey(it)
            } == true &&
            call.arguments.size == 1 && !call.expandLastArgument && !containsCallOrReceive(call.arguments.single(), env)) {
            staticRangeArrayLength(call.arguments.single(), env)?.let { return it.toLong() }
        }
        val target = evaluate(call.function, env)
        val rawArgs = evaluateCallArguments(call, env)
        val parameterTypes = when (target) {
            is FunctionValue -> target.function.parameterTypes
            is MethodValue -> target.function.parameterTypes
            is MethodExpressionValue -> (target.type as? FunctionGoType)?.parameters?.map { it.type }.orEmpty()
            else -> emptyList()
        }
        val args = rawArgs.mapIndexed { index, value ->
            val declaredType = parameterTypes.getOrNull(index)
                ?: parameterTypes.lastOrNull()?.let { if (target is FunctionValue && target.function.variadic) (it as? SliceGoType)?.element else null }
            if (declaredType != null && underlying(declaredType) is InterfaceGoType)
                defaultRuneValue(value, call.arguments.getOrNull(index), env) else value
        }
        return call(target, args, call.expandLastArgument, env.panicState, environment = env)
    }

    private suspend fun evaluateCallArguments(call: CallExpression, env: Environment): List<Any?> {
        if (!call.expandLastArgument && call.arguments.size == 1) {
            val value = evaluate(call.arguments.single(), env)
            if (value is GoMultiValue) return value.values.map(::copyValue)
            return listOf(copyValue(value))
        }
        return call.arguments.map { copyValue(evaluate(it, env)) }
    }

    private fun runtimeTypeConversion(call: CallExpression, env: Environment): GoTypeSyntax? = when (val target = call.function) {
        is TypeExpression -> resolveRuntimeType(target.type, env)
        is NameExpression -> {
            val binding = env.binding(target.name)
            when {
                binding?.value is TypeValue -> binding.value.type
                binding == null && target.name in builtinTypes -> NamedGoType(target.name)
                else -> null
            }
        }
        else -> null
    }

    private fun containsCallOrReceive(expression: Expression, env: Environment): Boolean = when (expression) {
        is CallExpression -> runtimeTypeConversion(expression, env)?.let {
            expression.arguments.any { argument -> containsCallOrReceive(argument, env) }
        } ?: true
        is UnaryExpression -> expression.operator == TokenKind.ARROW || containsCallOrReceive(expression.operand, env)
        is BinaryExpression -> containsCallOrReceive(expression.left, env) || containsCallOrReceive(expression.right, env)
        is SelectorExpression -> containsCallOrReceive(expression.receiver, env)
        is IndexExpression -> containsCallOrReceive(expression.receiver, env) || containsCallOrReceive(expression.index, env)
        is SliceExpression -> containsCallOrReceive(expression.receiver, env) ||
            listOfNotNull(expression.low, expression.high).any { containsCallOrReceive(it, env) }
        is TypeAssertionExpression -> containsCallOrReceive(expression.receiver, env)
        is ParenthesizedExpression -> containsCallOrReceive(expression.expression, env)
        is CompositeLiteral -> expression.elements.any { (it.key?.let { key -> containsCallOrReceive(key, env) } ?: false) ||
            containsCallOrReceive(it.value, env) }
        is ElidedCompositeLiteral -> expression.elements.any { (it.key?.let { key -> containsCallOrReceive(key, env) } ?: false) ||
            containsCallOrReceive(it.value, env) }
        is FunctionLiteralExpression -> true
        else -> false
    }

    private suspend fun call(
        target: Any?,
        args: List<Any?>,
        expandLastArgument: Boolean = false,
        panicState: PanicState = PanicState(),
        deferredCall: Boolean = false,
        environment: Environment? = null
    ): Any? {
        val effectiveArgs = if (expandLastArgument && !(target == BuiltinValue("append") && args.lastOrNull() is GoString)) {
            val last = args.lastOrNull()
            args.dropLast(1).map(::copyValue) + when (last) {
                is GoSlice -> last.toList().map(::copyValue)
                null -> emptyList()
                else -> throw RuntimeGoError("... argument must be a slice")
            }
        } else args.map(::copyValue)
        when (target) {
            is FunctionValue -> {
                val values = invoke(target.function, args, parent = target.closure, expandedVariadic = expandLastArgument,
                    panicState = panicState, deferredCall = deferredCall)
                return if (values.isEmpty()) null else if (values.size == 1) values.single() else GoMultiValue(values)
            }
            is MethodValue -> {
                val values = invoke(target.function, args, target.receiver, expandedVariadic = expandLastArgument,
                    panicState = panicState, deferredCall = deferredCall)
                return if (values.isEmpty()) null else if (values.size == 1) values.single() else GoMultiValue(values)
            }
            is MethodExpressionValue -> {
                val receiver = args.firstOrNull() ?: throw RuntimeGoError("method expression requires a receiver")
                val scope = environment ?: globals
                val method = selectStructMember(receiver, target.name, NameExpression("<method-expression receiver>"), scope)
                    as? MethodValue ?: throw RuntimeGoError("${target.name} is not a method")
                return call(method, args.drop(1), expandLastArgument, panicState, deferredCall, environment)
            }
            is GoNilValue -> if (underlying(target.type) is FunctionGoType)
                throw RuntimeGoError("call of nil function")
            is BuiltinValue -> when (target.name) {
                "print", "println" -> {
                    output(effectiveArgs.joinToString(if (target.name == "println") " " else "") { stringify(it) } + if (target.name == "println") "\n" else "")
                    return null
                }
                "panic" -> args.singleOrNull().let { throw PanicSignal(it, stringify(it)) }
                "recover" -> {
                    if (!panicState.recoverAllowed) return null
                    val activePanic = panicState.activePanic ?: return null
                    activePanic.recovered = true
                    panicState.activePanic = null
                    return when (val value = activePanic.value) {
                        null, is GoInterfaceValue -> value
                        else -> runtimeType(value)?.let { GoInterfaceValue(it, value) } ?: value
                    }
                }
                "complex" -> {
                    if (args.size != 2) throw RuntimeGoError("complex expects two arguments")
                    if (args.all { it is BigInteger || it is GoRational })
                        return GoExactComplex(exactRational(args[0]), exactRational(args[1]))
                    val type = if (args.filterIsInstance<GoFloat>().any { underlying(it.type) == NamedGoType("float32") })
                        NamedGoType("complex64") else NamedGoType("complex128")
                    return GoComplex(real(args[0]), real(args[1]), type)
                }
                "real" -> return when (val value = args.singleOrNull()) {
                    is GoExactComplex -> value.real
                    is GoRational -> value
                    is BigInteger -> GoRational.of(value)
                    is GoComplex -> floatResult(value.real, value.type)
                    is GoFloat -> value.value
                    is GoInteger -> integerAsDouble(value)
                    is Double -> value
                    is Long -> value.toDouble()
                    else -> throw RuntimeGoError("real requires a numeric argument")
                }
                "imag" -> return when (val value = args.singleOrNull()) {
                    is GoExactComplex -> value.imaginary
                    is GoRational, is BigInteger -> GoRational.ZERO
                    is GoComplex -> floatResult(value.imaginary, value.type)
                    is GoFloat, is GoInteger, is Double, is Long -> 0.0
                    else -> throw RuntimeGoError("imag requires a numeric argument")
                }
                "make" -> return make(args)
                "new" -> {
                    val type = (args.singleOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("new requires a type")
                    return GoPointer.cell(zeroValue(type), type)
                }
                "close" -> {
                    when (val channel = args.singleOrNull()) {
                        is GoChannel -> channel.close()
                        is GoNilValue -> if (underlying(channel.type) is ChannelGoType) throw RuntimeGoError("close of nil channel") else throw RuntimeGoError("close of non-channel")
                        else -> throw RuntimeGoError("close of non-channel")
                    }
                    return null
                }
                "len" -> return when (val value = args.singleOrNull()) {
                    is GoString -> value.bytes.size.toLong()
                    is GoSlice -> value.length.toLong()
                    is GoArray -> value.values.size.toLong()
                    is GoPointer -> pointerArrayLength(value, environment)
                    is GoMap -> value.values.size.toLong()
                    is GoChannel -> value.len()
                    is GoNilValue -> when (underlying(value.type)) {
                        is SliceGoType, is MapGoType, is ChannelGoType -> 0L
                        else -> throw RuntimeGoError("len is not defined for this value")
                    }
                    else -> throw RuntimeGoError("len is not defined for this value")
                }
                "cap" -> return when (val value = args.singleOrNull()) {
                    is GoChannel -> value.capacity.toLong()
                    is GoSlice -> value.capacity.toLong()
                    is GoArray -> value.values.size.toLong()
                    is GoPointer -> pointerArrayLength(value, environment)
                    is GoNilValue -> when (underlying(value.type)) {
                        is SliceGoType, is ChannelGoType -> 0L
                        else -> throw RuntimeGoError("cap is not defined for this value")
                    }
                    else -> throw RuntimeGoError("cap is not defined for this value")
                }
                "append" -> return append(effectiveArgs, expandString = expandLastArgument)
                "copy" -> return copy(args)
                "delete" -> { delete(args); return null }
                "Print", "Fprint" -> {
                    output(effectiveArgs.drop(if (target.name == "Fprint") 1 else 0).joinToString("") { stringify(it) })
                    return null
                }
                "Println", "Fprintln" -> {
                    output(effectiveArgs.drop(if (target.name == "Fprintln") 1 else 0).joinToString(" ") { stringify(it) } + "\n")
                    return null
                }
            }
            is TypeValue -> return convert(target.type, args.singleOrNull() ?: throw RuntimeGoError("conversion requires one argument"))
        }
        throw RuntimeGoError("cannot call value")
    }

    private suspend fun composite(literal: CompositeLiteral, env: Environment): Any? {
        val type = underlying(literal.type)
        return when (type) {
            is SliceGoType -> {
                val backing = mutableListOf<Any?>()
                var nextIndex = 0
                val usedIndices = mutableSetOf<Int>()
                literal.elements.forEach { element ->
                    val at = element.key?.let { compositeIndex(it, "slice literal index", env) } ?: nextIndex
                    if (at < 0 || at == Int.MAX_VALUE) throw RuntimeGoError("slice literal index out of range")
                    if (!usedIndices.add(at)) throw RuntimeGoError("duplicate slice literal index")
                    while (backing.size <= at) backing += zeroValue(type.element)
                    backing[at] = copyForType(evaluateCompositeValue(element.value, type.element, env), type.element)
                    nextIndex = at + 1
                }
                GoSlice(type.element, backing, 0, backing.size, backing.size, (literal.type as? NamedGoType)?.name, literal.type)
            }
            is ArrayGoType -> {
                val indices = mutableListOf<Int>()
                var nextIndex = 0
                literal.elements.forEach { element ->
                    val at = element.key?.let { compositeIndex(it, "array literal index", env) } ?: nextIndex
                    indices += at
                    nextIndex = at + 1
                }
                val size = type.length?.let {
                    val length = number(evaluate(it, env), "array length")
                    if (length < 0 || length > Int.MAX_VALUE) throw RuntimeGoError("array length out of range")
                    length.toInt()
                }
                    ?: (indices.maxOrNull()?.plus(1) ?: 0)
                if (size < 0) throw RuntimeGoError("negative array length")
                val values = MutableList(size) { zeroValue(type.element) }
                val usedIndices = mutableSetOf<Int>()
                literal.elements.forEachIndexed { index, element ->
                    val at = indices[index]
                    if (at !in values.indices) throw RuntimeGoError("array literal index out of range")
                    if (!usedIndices.add(at)) throw RuntimeGoError("duplicate array literal index")
                    values[at] = copyForType(evaluateCompositeValue(element.value, type.element, env), type.element)
                }
                GoArray(type.element, values, (literal.type as? NamedGoType)?.name, literal.type)
            }
            is MapGoType -> {
                val values = linkedMapOf<GoMapKey, Any?>()
                literal.elements.forEach { element ->
                    val keyExpression = element.key ?: throw RuntimeGoError("map literal element requires a key")
                    val key = evaluateCompositeValue(keyExpression, type.key, env)
                    values[mapKey(key, type.key)] = copyForType(evaluateCompositeValue(element.value, type.value, env), type.value)
                }
                GoMap(type.key, type.value, zeroValue(type.value), values,
                    (literal.type as? NamedGoType)?.name, literal.type)
            }
            is StructGoType -> {
                val fields = linkedMapOf<String, Any?>()
                val fieldList = structFieldSlots(type)
                fieldList.forEach { field ->
                    if (field.name.isNotEmpty()) fields[field.storageKey] = zeroValue(field.type)
                }
                val keyed = literal.elements.map { it.key != null }.toSet()
                if (keyed.size > 1) throw RuntimeGoError("mixture of keyed and unkeyed struct literal elements")
                if (keyed.singleOrNull() != true && literal.elements.size != fieldList.size)
                    throw RuntimeGoError("struct literal has ${literal.elements.size} values for ${fieldList.size} fields")
                val usedFields = mutableSetOf<String>()
                literal.elements.forEachIndexed { i, element ->
                    val field = if (element.key == null) fieldList.getOrNull(i) else {
                        val name = (element.key as? NameExpression)?.name
                        if (name == null || name == "_") throw RuntimeGoError("invalid struct literal field")
                        fieldList.firstOrNull { it.name == name }
                    }
                    if (field == null || field.name.isEmpty()) throw RuntimeGoError("unknown struct literal field")
                    if (!usedFields.add(field.storageKey)) throw RuntimeGoError("duplicate field ${field.name} in struct literal")
                    val value = evaluateCompositeValue(element.value, field.type, env)
                    fields[field.storageKey] = copyForType(value, field.type)
                }
                val fieldTypes = fieldList.filter { it.name.isNotEmpty() }.associate { it.storageKey to it.type }
                val runtimeStructType = resolveRuntimeType(literal.type, env)
                GoStruct(fields, (runtimeStructType as? NamedGoType)?.name, fieldTypes,
                    fieldList.filter { it.embedded }.mapTo(linkedSetOf()) { it.storageKey }, runtimeStructType)
            }
            else -> throw RuntimeGoError("composite literal for this type is not implemented")
        }
    }

    private suspend fun compositeIndex(expression: Expression, context: String, env: Environment): Int {
        val index = number(evaluate(expression, env), context)
        if (index < 0 || index >= Int.MAX_VALUE) throw RuntimeGoError("$context out of range")
        return index.toInt()
    }

    private suspend fun evaluateCompositeValue(expression: Expression, type: GoTypeSyntax, env: Environment): Any? = when {
        expression !is ElidedCompositeLiteral -> evaluate(expression, env)
        underlying(type) is PointerGoType -> {
            val pointerType = underlying(type) as PointerGoType
            GoPointer.cell(composite(CompositeLiteral(pointerType.element, expression.elements), env), pointerType.element)
        }
        else -> composite(CompositeLiteral(type, expression.elements), env)
    }

    private fun underlying(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        is NamedGoType -> typeDefinitions[type.name]?.let(::underlying) ?: when (type.name) {
            "byte" -> NamedGoType("uint8")
            "rune" -> NamedGoType("int32")
            "error" -> errorInterfaceType
            else -> type
        }
        else -> type
    }

    private fun resolveRuntimeType(type: GoTypeSyntax, env: Environment): GoTypeSyntax = when (type) {
        is NamedGoType -> env.typeBinding(type.name) ?: type
        is QualifiedGoType -> type
        is PointerGoType -> PointerGoType(resolveRuntimeType(type.element, env))
        is SliceGoType -> SliceGoType(resolveRuntimeType(type.element, env))
        is ArrayGoType -> ArrayGoType(type.length, resolveRuntimeType(type.element, env))
        is MapGoType -> MapGoType(resolveRuntimeType(type.key, env), resolveRuntimeType(type.value, env))
        is ChannelGoType -> ChannelGoType(resolveRuntimeType(type.element, env), type.direction)
        is StructGoType -> StructGoType(type.fields.map { field ->
            field.copy(type = resolveRuntimeType(field.type, env))
        })
        is InterfaceGoType -> InterfaceGoType(
            type.methods.map { method ->
                method.copy(
                    parameters = method.parameters.map { it.copy(type = resolveRuntimeType(it.type, env)) },
                    results = method.results.map { resolveRuntimeType(it, env) }
                )
            },
            type.embeddedTypes.map { resolveRuntimeType(it, env) }
        )
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = resolveRuntimeType(it.type, env)) },
            type.results.map { resolveRuntimeType(it, env) }
        )
    }

    private fun defineLocalType(declaration: TypeDeclaration, env: Environment) {
        val identity = synchronized(localTypeIdentities) {
            localTypeIdentities[declaration] ?: "<local:${nextLocalTypeIdentity.incrementAndGet()}:${declaration.name}>".also {
                localTypeIdentities[declaration] = it
            }
        }
        val namedType = NamedGoType(identity)
        env.defineType(declaration.name, namedType)
        typeDefinitions.putIfAbsent(identity, resolveRuntimeType(declaration.type, env))
    }

    private fun boxInterface(value: Any?, targetType: GoTypeSyntax): Any? {
        if ((underlying(targetType) as? InterfaceGoType) == null || value == null || value is GoInterfaceValue) return value
        val dynamicType = runtimeType(value) ?: return value
        return GoInterfaceValue(dynamicType, value)
    }

    private fun runtimeType(value: Any?): GoTypeSyntax? = when (value) {
        is GoInterfaceValue -> value.dynamicType
        is GoStruct -> value.namedType?.let(::NamedGoType) ?: value.staticType
        is GoArray -> value.namedType?.let(::NamedGoType) ?: value.type
        is GoSlice -> value.namedType?.let(::NamedGoType) ?: value.type ?: SliceGoType(value.elementType)
        is GoChannel -> value.namedType?.let(::NamedGoType) ?: value.type ?: ChannelGoType(value.elementType, value.direction)
        is GoPointer -> value.pointeeType?.let(::PointerGoType) ?: runtimeType(value.get())?.let(::PointerGoType)
        is GoNilValue -> value.type
        is GoComplex -> value.type
        is GoFloat -> value.type
        is GoBoolean -> value.type
        is GoInteger -> when {
            value.type == NamedGoType("byte") && !typeDefinitions.containsKey("byte") -> NamedGoType("uint8")
            value.type == NamedGoType("rune") && !typeDefinitions.containsKey("rune") -> NamedGoType("int32")
            else -> value.type
        }
        is GoRational -> NamedGoType("float64")
        is GoExactComplex -> NamedGoType("complex128")
        is BigInteger -> NamedGoType("int")
        is GoMap -> value.namedType?.let(::NamedGoType) ?: value.type ?: MapGoType(value.keyType, value.valueType)
        is FunctionValue -> value.type ?: FunctionGoType(value.function.parameterTypes.mapIndexed { i, type ->
            ParameterSyntax(value.function.parameters.getOrNull(i), type, value.function.variadic && i == value.function.parameterTypes.lastIndex)
        }, value.function.resultTypes)
        is MethodExpressionValue -> value.type
        is Long -> NamedGoType("int")
        is Double -> NamedGoType("float64")
        is GoString -> value.type
        is Boolean -> NamedGoType("bool")
        else -> null
    }

    private fun assertType(value: Any?, target: GoTypeSyntax): GoAssertionResult {
        if (value == null) return GoAssertionResult(zeroValue(target), false, NamedGoType("<nil>"))
        val iface = value as? GoInterfaceValue ?: throw RuntimeGoError("type assertion on non-interface value")
        val targetInterface = underlying(target) as? InterfaceGoType
        val matches = when {
            targetInterface != null -> implementsInterface(iface.dynamicType, targetInterface)
            else -> sameRuntimeType(iface.dynamicType, target)
        }
        return GoAssertionResult(if (matches) iface.value else zeroValue(target), matches, iface.dynamicType)
    }

    private fun implementsInterface(type: GoTypeSyntax, target: InterfaceGoType): Boolean {
        val required = interfaceMethodsRuntime(target)
        val actual = runtimeMethodSet(type)
        return required.all { (name, signature) -> actual[name]?.let { sameFunctionType(it, signature) } == true }
    }

    private fun interfaceMethodsRuntime(type: GoTypeSyntax, seen: Set<String> = emptySet()): Map<String, FunctionGoType> {
        val iface = underlying(type) as? InterfaceGoType ?: return emptyMap()
        val result = linkedMapOf<String, FunctionGoType>()
        iface.embeddedTypes.forEach { embedded ->
            val key = embedded.toString()
            if (key !in seen) interfaceMethodsRuntime(embedded, seen + key).forEach { (name, signature) ->
                if (result.putIfAbsent(name, signature) != null) throw RuntimeGoError("duplicate interface method $name")
            }
        }
        iface.methods.forEach { method ->
            if (result.putIfAbsent(method.name, FunctionGoType(method.parameters, method.results)) != null)
                throw RuntimeGoError("duplicate interface method ${method.name}")
        }
        return result
    }

    private fun runtimeMethodSet(type: GoTypeSyntax): Map<String, FunctionGoType> {
        // A pointer to an interface does not inherit the interface's method set.
        if (type is PointerGoType && underlying(type.element) is InterfaceGoType) return emptyMap()
        val actual = underlying(type)
        if (actual is InterfaceGoType) return interfaceMethodsRuntime(actual)
        val result = linkedMapOf<String, FunctionGoType>()
        data class SearchNode(val type: GoTypeSyntax, val pointer: Boolean, val ancestors: Set<String>)
        fun baseType(nodeType: GoTypeSyntax): GoTypeSyntax = underlying((nodeType as? PointerGoType)?.element ?: nodeType)
        fun baseName(nodeType: GoTypeSyntax): String? = when (val base = if (nodeType is PointerGoType) nodeType.element else nodeType) {
            is NamedGoType -> base.name
            else -> null
        }
        var level = listOf(SearchNode(type, type is PointerGoType, emptySet()))
        val blocked = mutableSetOf<String>()
        while (level.isNotEmpty()) {
            val candidates = linkedMapOf<String, MutableList<FunctionGoType>>()
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                when (val nodeUnderlying = baseType(node.type)) {
                    is InterfaceGoType -> interfaceMethodsRuntime(nodeUnderlying).forEach { (name, signature) ->
                        candidates.getOrPut(name) { mutableListOf() } += signature
                    }
                    is StructGoType -> {
                        val named = baseName(node.type)
                        if (named != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            val receiverBase = if (receiverType is PointerGoType) receiverType.element else receiverType
                            if (receiverBase != NamedGoType(named) || receiverType is PointerGoType && !node.pointer) return@methodLoop
                            candidates.getOrPut(method.name) { mutableListOf() } += FunctionGoType(
                                method.parameterTypes.mapIndexed { i, parameter ->
                                    ParameterSyntax(method.parameters.getOrNull(i), parameter, method.variadic && i == method.parameterTypes.lastIndex)
                                },
                                method.resultTypes
                            )
                        }
                        nodeUnderlying.fields.filter { it.names.isEmpty() }.forEach { field ->
                            val embedded = field.type
                            val key = embedded.toString()
                            if (key !in node.ancestors) next += SearchNode(
                                embedded,
                                node.pointer || embedded is PointerGoType,
                                node.ancestors + key
                            )
                        }
                    }
                    else -> {
                        val named = baseName(node.type)
                        if (named != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            val receiverBase = if (receiverType is PointerGoType) receiverType.element else receiverType
                            if (receiverBase != NamedGoType(named) || receiverType is PointerGoType && !node.pointer) return@methodLoop
                            candidates.getOrPut(method.name) { mutableListOf() } += FunctionGoType(
                                method.parameterTypes.mapIndexed { i, parameter ->
                                    ParameterSyntax(method.parameters.getOrNull(i), parameter, method.variadic && i == method.parameterTypes.lastIndex)
                                },
                                method.resultTypes
                            )
                        }
                    }
                }
            }
            candidates.forEach { (name, methodsAtDepth) ->
                if (methodsAtDepth.size == 1 && name !in blocked) result[name] = methodsAtDepth.single()
                blocked += name
            }
            level = next
        }
        return result
    }

    private fun sameFunctionType(left: FunctionGoType, right: FunctionGoType): Boolean =
        left.parameters.size == right.parameters.size && left.results.size == right.results.size &&
            left.parameters.zip(right.parameters).all { (a, b) -> a.type == b.type && a.variadic == b.variadic } &&
            left.results.zip(right.results).all { (a, b) -> a == b }

    private fun methodKey(type: GoTypeSyntax, name: String): String {
        val base = if (type is PointerGoType) type.element else type
        return "${(base as? NamedGoType)?.name ?: base}.$name"
    }

    private fun dereference(value: Any?): Any? = if (value is GoPointer) value.get() else value

    private fun copyValue(value: Any?): Any? = when (value) {
        is GoStruct -> GoStruct(
            value.fields.mapValuesTo(linkedMapOf()) { copyValue(it.value) },
            value.namedType, value.fieldTypes, value.embeddedFields, value.staticType
        )
        is GoArray -> GoArray(value.elementType, value.values.mapTo(mutableListOf(), ::copyValue), value.namedType, value.type)
        is GoInterfaceValue -> GoInterfaceValue(value.dynamicType, copyValue(value.value))
        else -> value
    }

    private fun copyForType(value: Any?, type: GoTypeSyntax): Any? {
        val actual = underlying(type)
        val copied = if (value == null) when (actual) {
            is PointerGoType -> GoPointer.nil(actual.element)
            is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType -> GoNilValue(type)
            else -> null
        } else if (value is GoBoolean && actual == NamedGoType("bool")) GoBoolean(value.value, type)
        else if (value is Boolean && actual == NamedGoType("bool")) GoBoolean(value, type)
        else if (value is GoString && actual == NamedGoType("string")) GoString(value.bytes.copyOf(), type)
        else if (value is GoPointer && actual is PointerGoType) value.retype(actual.element)
        else if (value is GoArray && actual is ArrayGoType)
            GoArray(actual.element, value.values.mapTo(mutableListOf()) { copyForType(it, actual.element) },
                (type as? NamedGoType)?.name, type)
        else if (value is GoSlice && actual is SliceGoType) value.retype(actual.element, (type as? NamedGoType)?.name, type)
        else if (value is GoMap && actual is MapGoType) value.retype(actual.key, actual.value, (type as? NamedGoType)?.name, type)
        else if (value is GoChannel && actual is ChannelGoType)
            value.retype(actual.element, actual.direction, (type as? NamedGoType)?.name, type)
        else if (value is FunctionValue && actual is FunctionGoType) value.copy(type = type)
        else if (value is MethodExpressionValue && actual is FunctionGoType) value.copy(type = type)
        else if (value is GoStruct && actual is StructGoType) {
            val fields = linkedMapOf<String, Any?>()
            val fieldTypes = linkedMapOf<String, GoTypeSyntax>()
            val embeddedFields = linkedSetOf<String>()
            structFieldSlots(actual).forEach { field ->
                if (field.name.isEmpty()) return@forEach
                fields[field.storageKey] = copyForType(value.fields[field.storageKey], field.type)
                fieldTypes[field.storageKey] = field.type
                if (field.embedded) embeddedFields += field.storageKey
            }
            GoStruct(fields, (type as? NamedGoType)?.name, fieldTypes, embeddedFields, type)
        }
        else if ((value is BigInteger || value is GoRational || value is GoExactComplex) && actual is InterfaceGoType) defaultConstantValue(value)
        else if (actual is NamedGoType && (actual.name in integerTypeNames || actual.name in setOf("complex64", "complex128", "float32", "float64"))) convert(type, value)
        else copyValue(value)
        return boxInterface(copied, type)
    }

    private fun index(receiver: Any?, rawIndex: Any?): Any? {
        return when (receiver) {
            is GoSlice -> receiver.get(number(rawIndex, "index").toInt())
            is GoArray -> arrayElement(receiver, rawIndex)
            is GoPointer -> {
                val array = receiver.get() as? GoArray ?: throw RuntimeGoError("index requires pointer to array")
                arrayElement(array, rawIndex)
            }
            is GoMap -> mapKey(rawIndex, receiver.keyType).let { if (receiver.values.containsKey(it)) receiver.values[it] else receiver.elementZero }
            is GoNilValue -> (underlying(receiver.type) as? MapGoType)?.let { zeroValue(it.value) }
                ?: throw RuntimeGoError("cannot index this value")
            is GoStruct -> {
                val field = rawIndex as? String ?: throw RuntimeGoError("struct field must be a name")
                if (receiver.fields.containsKey(field)) receiver.fields[field] else throw RuntimeGoError("unknown struct field: $field")
            }
            is GoString -> {
                val i = number(rawIndex, "index").toInt()
                if (i !in receiver.bytes.indices) throw RuntimeGoError("string index out of range")
                (receiver.bytes[i].toInt() and 0xff).toLong()
            }
            else -> throw RuntimeGoError("cannot index this value")
        }
    }

    private fun arrayElement(array: GoArray, rawIndex: Any?): Any? {
        val index = number(rawIndex, "index").toInt()
        if (index !in array.values.indices) throw RuntimeGoError("array index out of range")
        return array.values[index]
    }

    private fun setArrayElement(array: GoArray, rawIndex: Any?, value: Any?) {
        val index = number(rawIndex, "index").toInt()
        if (index !in array.values.indices) throw RuntimeGoError("array index out of range")
        array.values[index] = copyForType(value, array.elementType)
    }

    private fun sliceArray(array: GoArray, low: Int, high: Int, max: Int): GoSlice {
        if (low < 0 || high < low || max < high || max > array.values.size)
            throw RuntimeGoError("slice bounds out of range")
        return GoSlice(array.elementType, array.values, low, high - low, max - low,
            type = SliceGoType(array.elementType))
    }

    private fun slice(receiver: Any?, lowValue: Any?, highValue: Any?): Any? {
        val low = lowValue?.let { number(it, "slice index").toInt() } ?: 0
        return when (receiver) {
            is GoSlice -> {
                val high = highValue?.let { number(it, "slice index").toInt() } ?: receiver.length
                receiver.subSlice(low, high, receiver.capacity)
            }
            is GoArray -> {
                val high = highValue?.let { number(it, "slice index").toInt() } ?: receiver.values.size
                sliceArray(receiver, low, high, receiver.values.size)
            }
            is GoPointer -> {
                val array = receiver.get() as? GoArray ?: throw RuntimeGoError("slice requires pointer to array")
                val high = highValue?.let { number(it, "slice index").toInt() } ?: array.values.size
                sliceArray(array, low, high, array.values.size)
            }
            is GoString -> {
                val bytes = receiver.bytes
                val high = highValue?.let { number(it, "slice index").toInt() } ?: bytes.size
                if (low < 0 || high < low || high > bytes.size) throw RuntimeGoError("string slice bounds out of range")
                GoString(bytes.copyOfRange(low, high), receiver.type)
            }
            else -> throw RuntimeGoError("cannot slice this value")
        }
    }

    private fun convert(type: GoTypeSyntax, value: Any?): Any? = when (val target = underlying(type)) {
        is PointerGoType -> when (value) {
            is GoPointer -> value.retype(target.element)
            null, is GoNilValue -> GoPointer.nil(target.element)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is ArrayGoType -> {
            if (value !is GoArray) throw RuntimeGoError("cannot convert value to $type")
            GoArray(target.element, value.values.mapTo(mutableListOf()) { copyForType(it, target.element) },
                (type as? NamedGoType)?.name, type)
        }
        is SliceGoType -> {
            if (value is GoString && isByteOrRuneType(target.element)) {
                if (value.bytes.isEmpty()) GoNilValue(type)
                else {
                    val converted = if (isByteType(target.element))
                        value.bytes.map { (it.toInt() and 0xff).toLong() }
                    else decodeUtf8Runes(value.bytes).map(Int::toLong)
                    val backing = converted.mapTo(mutableListOf()) { copyForType(it, target.element) }
                    GoSlice(target.element, backing, 0, backing.size, backing.size, (type as? NamedGoType)?.name, type)
                }
            } else if (value is GoSlice) value.retype(target.element, (type as? NamedGoType)?.name, type)
            else if (value == null || value is GoNilValue && underlying(value.type) is SliceGoType) GoNilValue(type)
            else throw RuntimeGoError("cannot convert value to $type")
        }
        is MapGoType -> when (value) {
            is GoMap -> value.retype(target.key, target.value, (type as? NamedGoType)?.name, type)
            null, is GoNilValue -> GoNilValue(type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is ChannelGoType -> when (value) {
            is GoChannel -> value.retype(target.element, target.direction, (type as? NamedGoType)?.name, type)
            null, is GoNilValue -> GoNilValue(type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is FunctionGoType -> when (value) {
            is FunctionValue -> value.copy(type = type)
            is MethodExpressionValue -> value.copy(type = type)
            null, is GoNilValue -> GoNilValue(type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is InterfaceGoType -> boxInterface(value, type)
        is StructGoType -> when (value) {
            is GoStruct -> copyForType(value, type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is NamedGoType -> when (target.name) {
            "string" -> when (value) {
                is GoString -> GoString(value.bytes.copyOf(), type)
                is Long -> GoString(codePointString(value).toByteArray(Charsets.UTF_8), type)
                is BigInteger -> GoString(codePointString(value).toByteArray(Charsets.UTF_8), type)
                is GoInteger -> GoString(codePointString(value.value).toByteArray(Charsets.UTF_8), type)
                is GoSlice -> when {
                    isByteType(value.elementType) -> GoString(value.toList().map { number(it, "string conversion").toInt().toByte() }.toByteArray(), type)
                    isRuneType(value.elementType) -> GoString(value.toList().joinToString("") { codePointString(number(it, "string conversion")) }.toByteArray(Charsets.UTF_8), type)
                    else -> throw RuntimeGoError("cannot convert slice to string")
                }
                is GoNilValue -> if (isByteOrRuneSlice(value.type)) GoString(byteArrayOf(), type) else throw RuntimeGoError("cannot convert to string")
                else -> throw RuntimeGoError("cannot convert to string")
            }
            "bool" -> GoBoolean(booleanValue(value, "bool conversion"), type)
            "float32", "float64" -> when (value) {
                is Long -> GoFloat(if (target.name == "float32") value.toFloat().toDouble() else value.toDouble(), type)
                is BigInteger -> value.toDouble().let { GoFloat(if (target.name == "float32") it.toFloat().toDouble() else it, type) }
                is GoRational -> value.toDouble().let { GoFloat(if (target.name == "float32") it.toFloat().toDouble() else it, type) }
                is GoExactComplex -> value.real.toDouble().let { GoFloat(if (target.name == "float32") it.toFloat().toDouble() else it, type) }
                is GoInteger -> integerAsDouble(value).let { GoFloat(if (target.name == "float32") it.toFloat().toDouble() else it, type) }
                is Double -> GoFloat(if (target.name == "float32") value.toFloat().toDouble() else value, type)
                is GoFloat -> GoFloat(if (target.name == "float32") value.value.toFloat().toDouble() else value.value, type)
                is GoComplex -> GoFloat(if (target.name == "float32") value.real.toFloat().toDouble() else value.real, type)
                else -> throw RuntimeGoError("cannot convert to float")
            }
            "complex64", "complex128" -> {
                val real = when (value) { is Long -> value.toDouble(); is BigInteger -> value.toDouble(); is GoRational -> value.toDouble(); is GoExactComplex -> value.real.toDouble(); is GoInteger -> integerAsDouble(value); is Double -> value; is GoFloat -> value.value; is GoComplex -> value.real; else -> throw RuntimeGoError("cannot convert to complex") }
                val imaginary = when (value) {
                    is GoComplex -> value.imaginary
                    is GoExactComplex -> value.imaginary.toDouble()
                    else -> 0.0
                }
                val convertedType = type
                if (target.name == "complex64") GoComplex(real.toFloat().toDouble(), imaginary.toFloat().toDouble(), convertedType)
                else GoComplex(real, imaginary, convertedType)
            }
            in integerTypeNames -> {
                val converted = when (value) {
                    is Long -> value
                    is GoInteger -> value.value
                    is BigInteger -> value.toLong()
                    is GoRational -> value.integerValue("integer conversion").toLong()
                    is Double -> value.toLong()
                    is GoFloat -> value.value.toLong()
                    is GoComplex -> value.real.toLong()
                    else -> throw RuntimeGoError("cannot convert to integer")
                }
                GoInteger(wrapInteger(converted, type), type)
            }
            else -> value
        }
        else -> value
    }

    private fun isByteType(type: GoTypeSyntax): Boolean = underlying(type) == NamedGoType("uint8")
    private fun isRuneType(type: GoTypeSyntax): Boolean = underlying(type) == NamedGoType("int32")
    private fun isPredeclaredByteType(type: GoTypeSyntax): Boolean =
        type == NamedGoType("byte") && !typeDefinitions.containsKey("byte") ||
            type == NamedGoType("uint8") && !typeDefinitions.containsKey("uint8")
    private fun isByteOrRuneType(type: GoTypeSyntax): Boolean = isByteType(type) || isRuneType(type)
    private fun isByteOrRuneSlice(type: GoTypeSyntax): Boolean =
        (underlying(type) as? SliceGoType)?.element?.let(::isByteOrRuneType) == true

    private fun isUnsignedInteger(type: GoTypeSyntax): Boolean = (underlying(type) as? NamedGoType)?.name in
        setOf("uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte")

    private fun integerBitWidth(type: GoTypeSyntax): Int = when ((underlying(type) as? NamedGoType)?.name) {
        "int8", "uint8", "byte" -> 8
        "int16", "uint16" -> 16
        "int32", "uint32", "rune" -> 32
        else -> 64
    }

    private fun wrapInteger(value: Long, type: GoTypeSyntax): Long {
        val bits = integerBitWidth(type)
        if (bits == Long.SIZE_BITS) return value
        val mask = (1L shl bits) - 1
        val narrowed = value and mask
        return if (!isUnsignedInteger(type) && narrowed.and(1L shl (bits - 1)) != 0L) narrowed or mask.inv() else narrowed
    }

    private fun integerAsDouble(value: GoInteger): Double = integerValue(value, "float conversion").toDouble()

    private fun codePointString(value: Long): String {
        val codePoint = value.toInt()
        return if (value !in 0..Character.MAX_CODE_POINT.toLong() || codePoint in 0xd800..0xdfff)
            "\ufffd" else String(Character.toChars(codePoint))
    }

    private fun codePointString(value: BigInteger): String = if (value < BigInteger.ZERO ||
        value > BigInteger.valueOf(Character.MAX_CODE_POINT.toLong())) "\ufffd" else codePointString(value.toLong())

    private fun append(args: List<Any?>, expandString: Boolean = false): Any? {
        val first = args.firstOrNull()
        val values = args.drop(1)
        if (first is GoNilValue && values.isEmpty()) return first
        val slice = when (first) {
            is GoSlice -> first
            is GoNilValue -> (underlying(first.type) as? SliceGoType)?.let {
                GoSlice(it.element, mutableListOf(), 0, 0, 0,
                    (first.type as? NamedGoType)?.name, first.type)
            } ?: throw RuntimeGoError("append requires a slice")
            else -> throw RuntimeGoError("append requires a slice")
        }
        if (expandString && values.singleOrNull() is GoString) {
            if (!isPredeclaredByteType(slice.elementType)) throw RuntimeGoError("append string expansion requires a byte slice")
            return slice.append((values.single() as GoString).bytes.map { (it.toInt() and 0xff).toLong() })
        }
        return slice.append(values)
    }

    private fun copy(args: List<Any?>): Long {
        val destinationValue = args.getOrNull(0)
        val destination = destinationValue as? GoSlice
        val destinationType = when (destinationValue) {
            is GoSlice -> SliceGoType(destinationValue.elementType)
            is GoNilValue -> underlying(destinationValue.type).takeIf { it is SliceGoType }
            null -> null
            else -> throw RuntimeGoError("copy destination must be a slice")
        } as? SliceGoType ?: if (destinationValue == null) return 0L else throw RuntimeGoError("copy destination must be a slice")
        val values = when (val source = args.getOrNull(1)) {
            is GoSlice -> {
                if (!sameRuntimeType(destinationType.element, source.elementType)) throw RuntimeGoError("copy slice element types do not match")
                source.toList()
            }
            is GoNilValue -> {
                val sourceType = underlying(source.type) as? SliceGoType
                    ?: throw RuntimeGoError("copy source must be a slice or string")
                if (!sameRuntimeType(destinationType.element, sourceType.element)) throw RuntimeGoError("copy slice element types do not match")
                emptyList()
            }
            null -> emptyList()
            is GoString -> {
                if (!isPredeclaredByteType(destinationType.element)) throw RuntimeGoError("copy from string requires a byte slice")
                source.bytes.map { (it.toInt() and 0xff).toLong() }
            }
            else -> throw RuntimeGoError("copy source must be a slice or string")
        }
        if (destination == null) return 0L
        val count = minOf(destination.length, values.size)
        repeat(count) { destination.set(it, values[it]) }
        return count.toLong()
    }

    private fun delete(args: List<Any?>) {
        val map = args.getOrNull(0) as? GoMap ?: when (val nilMap = args.getOrNull(0)) {
            is GoNilValue -> if (underlying(nilMap.type) is MapGoType)
                throw RuntimeGoError("delete from nil map") else throw RuntimeGoError("delete requires a map")
            else -> throw RuntimeGoError("delete requires a map")
        }
        map.values.remove(mapKey(args.getOrNull(1), map.keyType))
    }

    private fun mapKey(value: Any?, keyType: GoTypeSyntax? = null): GoMapKey {
        val typedValue = keyType?.let { copyForType(value, it) } ?: value
        if (!runtimeComparable(typedValue)) throw RuntimeGoError("hash of unhashable type")
        return GoMapKey(copyValue(typedValue))
    }

    private fun literal(token: Token): Any = when (token.kind) {
        TokenKind.INT -> integer(token.lexeme)
        TokenKind.FLOAT -> runCatching { GoRational.decimal(token.lexeme) }.getOrElse { throw RuntimeGoError("invalid float ${token.lexeme}") }
        TokenKind.IMAG -> GoExactComplex(GoRational.ZERO, imaginaryPart(token.lexeme.removeSuffix("i")))
        TokenKind.CHAR -> BigInteger.valueOf(decodeQuoted(token.lexeme, '\'').codePointAt(0).toLong())
        TokenKind.STRING -> decodeString(token.lexeme)
        else -> throw RuntimeGoError("invalid literal")
    }

    private fun integer(text: String): BigInteger = try {
        when {
            text.startsWith("0x", true) -> BigInteger(text.substring(2), 16)
            text.length > 1 && text.startsWith("0") -> BigInteger(text.substring(1), 8)
            else -> BigInteger(text, 10)
        }
    } catch (_: Exception) { throw RuntimeGoError("invalid integer literal: $text") }

    private suspend fun unary(operator: TokenKind, value: Any?): Any? = when (operator) {
        TokenKind.ADD -> value
        TokenKind.SUB -> when (value) {
            is GoRational -> value.negate()
            is GoExactComplex -> GoExactComplex(value.real.negate(), value.imaginary.negate())
            is BigInteger -> value.negate()
            is Long -> -value
            is GoInteger -> value.copy(value = wrapInteger(-value.value, value.type))
            is Double -> -value
            is GoFloat -> value.copy(value = -value.value)
            is GoComplex -> value.copy(real = -value.real, imaginary = -value.imaginary)
            else -> typeError("unary -", value)
        }
        TokenKind.NOT -> !booleanValue(value, "!")
        TokenKind.XOR -> when (value) {
            is BigInteger -> value.not()
            is GoInteger -> value.copy(value = wrapInteger(value.value.inv(), value.type))
            else -> number(value, "^").inv()
        }
        TokenKind.AND -> throw RuntimeGoError("pointers are not implemented")
        TokenKind.MUL -> throw RuntimeGoError("pointer dereference is not implemented")
        TokenKind.ARROW -> when (value) {
            is GoChannel -> value.receive()
            is GoNilValue -> if (underlying(value.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("receive from non-channel")
            else -> throw RuntimeGoError("receive from non-channel")
        }
        else -> value
    }

    private suspend fun receiveResult(value: Any?): GoReceiveResult = when (value) {
        is GoChannel -> value.receive()
        is GoNilValue -> if (underlying(value.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("receive from non-channel")
        else -> throw RuntimeGoError("receive from non-channel")
    }

    private fun make(args: List<Any?>): Any? {
        val type = underlying((args.firstOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("make requires a type"))
        return when (type) {
            is ChannelGoType -> {
                if (args.size !in 1..2) throw RuntimeGoError("make channel accepts one or two arguments")
                val capacity = args.getOrNull(1)?.let { makeSize(it, "channel capacity") } ?: 0
                if (capacity < 0) throw RuntimeGoError("negative channel capacity")
                val requestedType = (args.first() as TypeValue).type
                GoChannel(type.element, capacity, (requestedType as? NamedGoType)?.name, requestedType, type.direction)
            }
            is SliceGoType -> {
                if (args.size !in 2..3) throw RuntimeGoError("make slice requires length and optional capacity")
                val length = args.getOrNull(1)?.let { makeSize(it, "slice length") }
                    ?: throw RuntimeGoError("make slice requires a length")
                val capacity = args.getOrNull(2)?.let { makeSize(it, "slice capacity") } ?: length
                if (length < 0 || capacity < length) throw RuntimeGoError("invalid slice length or capacity")
                val requestedType = (args.first() as TypeValue).type
                GoSlice(type.element, zeroedSliceBacking(capacity, type.element), 0, length, capacity,
                    (requestedType as? NamedGoType)?.name, requestedType)
            }
            is MapGoType -> {
                if (args.size !in 1..2) throw RuntimeGoError("make map accepts one or two arguments")
                val size = args.getOrNull(1)?.let { makeSize(it, "map size hint") } ?: 0
                if (size < 0) throw RuntimeGoError("negative map size hint")
                val requestedType = (args.first() as TypeValue).type
                GoMap(type.key, type.value, zeroValue(type.value), linkedMapOf(),
                    (requestedType as? NamedGoType)?.name, requestedType)
            }
            else -> throw RuntimeGoError("make for this type is not implemented")
        }
    }

    private fun makeSize(value: Any?, operation: String): Int {
        val size = number(value, operation)
        if (size > Int.MAX_VALUE) throw RuntimeGoError("$operation out of range")
        return size.toInt()
    }

    private fun zeroedSliceBacking(capacity: Int, elementType: GoTypeSyntax): MutableList<Any?> = try {
        MutableList(capacity) { zeroValue(elementType) }
    } catch (_: OutOfMemoryError) {
        throw RuntimeGoError("slice allocation failed")
    }

    private fun expandValues(values: List<Any?>, targets: Int): List<Any?> {
        if (values.size == 1) {
            val only = values.single()
            if (only is GoAssertionResult && targets == 2) return listOf(only.value, only.ok)
            if (only is GoAssertionResult) return listOf(only.value)
            if (only is GoReceiveResult && targets == 2) return listOf(only.value, only.ok)
            if (only is GoReceiveResult) return listOf(only.value)
            if (only is MapLookupResult && targets == 2) return listOf(only.value, only.ok)
            if (only is MapLookupResult) return listOf(only.value)
            if (only is GoMultiValue) return only.values
            return listOf(only)
        }
        return values.map { when (it) { is GoReceiveResult -> it.value; is MapLookupResult -> it.value; else -> it } }
    }

    private fun zeroValue(type: GoTypeSyntax): Any? = when (val actual = underlying(type)) {
        is NamedGoType -> when (actual.name) {
            "bool" -> GoBoolean(false, type)
            "string" -> GoString(byteArrayOf(), type)
            in integerTypeNames -> GoInteger(0L, type)
            "float32", "float64" -> GoFloat(0.0, type)
            "complex64", "complex128" -> GoComplex(0.0, 0.0, type)
            else -> null
        }
        is ArrayGoType -> {
            val length = actual.length?.let {
                val value = try { integerLiteral(it).intValueExact() }
                catch (_: ArithmeticException) { throw RuntimeGoError("array length out of range") }
                if (value < 0) throw RuntimeGoError("negative array length")
                value
            } ?: 0
            GoArray(actual.element, MutableList(length) { zeroValue(actual.element) }, (type as? NamedGoType)?.name, type)
        }
        is StructGoType -> {
            val fields = linkedMapOf<String, Any?>()
            val fieldTypes = linkedMapOf<String, GoTypeSyntax>()
            structFieldSlots(actual).forEach { field ->
                if (field.name.isNotEmpty()) {
                    fields[field.storageKey] = zeroValue(field.type)
                    fieldTypes[field.storageKey] = field.type
                }
            }
            GoStruct(fields, (type as? NamedGoType)?.name, fieldTypes,
                structFieldSlots(actual).filter { it.embedded }.mapTo(linkedSetOf()) { it.storageKey }, type)
        }
        is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType -> GoNilValue(type)
        is PointerGoType -> GoPointer.nil(actual.element)
        else -> null
    }

    private fun embeddedFieldName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is PointerGoType -> embeddedFieldName(type.element)
        else -> ""
    }

    private fun structFieldSlots(type: StructGoType): List<RuntimeStructField> =
        type.fields.flatMap { field ->
            val embedded = field.names.isEmpty()
            val names = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
            names.map { Triple(it, field.type, embedded) }
        }.mapIndexed { index, (name, fieldType, embedded) ->
            RuntimeStructField(name, if (name == "_") "\u0000blank:$index" else name, fieldType, embedded)
        }

    private fun integerLiteral(expression: Expression, env: Environment? = null): BigInteger = when (expression) {
        is LiteralExpression -> integer(expression.token.lexeme)
        is NameExpression -> when (val value = env?.getOrNull(expression.name) ?: globals.getOrNull(expression.name)) {
            is BigInteger -> value
            is Long -> BigInteger.valueOf(value)
            is GoInteger -> integerValue(value, "array length")
            else -> throw RuntimeGoError("array length is not a constant integer expression")
        }
        is ParenthesizedExpression -> integerLiteral(expression.expression, env)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.ADD -> integerLiteral(expression.operand, env)
            TokenKind.SUB -> integerLiteral(expression.operand, env).negate()
            TokenKind.XOR -> integerLiteral(expression.operand, env).not()
            else -> throw RuntimeGoError("invalid integer constant expression")
        }
        is BinaryExpression -> {
            val left = integerLiteral(expression.left, env)
            val right = integerLiteral(expression.right, env)
            when (expression.operator) {
                TokenKind.ADD -> left + right
                TokenKind.SUB -> left - right
                TokenKind.MUL -> left * right
                TokenKind.QUO -> if (right.signum() == 0) throw RuntimeGoError("division by zero in array length") else left / right
                TokenKind.REM -> if (right.signum() == 0) throw RuntimeGoError("division by zero in array length") else left % right
                TokenKind.AND -> left.and(right)
                TokenKind.OR -> left.or(right)
                TokenKind.XOR -> left.xor(right)
                TokenKind.AND_NOT -> left.and(right.not())
                TokenKind.SHL -> left.shiftLeft(right.intValueExact())
                TokenKind.SHR -> left.shiftRight(right.intValueExact())
                else -> throw RuntimeGoError("invalid integer constant expression")
            }
        }
        else -> throw RuntimeGoError("array length is not a constant integer expression")
    }

    private fun materializeExactConstant(value: Any?, typedOperand: Any?): Any? = when (value) {
        is GoRational -> when (typedOperand) {
            is GoInteger -> value.integerValue("integer operation")
            is Long -> value.integerValue("integer operation")
            is GoFloat, is Double -> value.toDouble()
            is GoComplex -> GoComplex(value.toDouble(), 0.0, typedOperand.type)
            else -> value
        }
        is GoExactComplex -> when (typedOperand) {
            is GoComplex -> GoComplex(value.real.toDouble(), value.imaginary.toDouble(), typedOperand.type)
            else -> throw RuntimeGoError("complex constant cannot be used with this operand")
        }
        else -> value
    }

    private fun GoRational.integerValue(context: String): BigInteger = if (isInteger()) numerator
        else throw RuntimeGoError("non-integer constant in $context")

    private fun exactRational(value: Any?): GoRational = when (value) {
        is GoRational -> value
        is BigInteger -> GoRational.of(value)
        is GoInteger -> GoRational.of(integerValue(value, "constant arithmetic"))
        is Long -> GoRational.of(BigInteger.valueOf(value))
        else -> typeError("constant arithmetic", value)
    }

    private fun exactComplex(value: Any?): GoExactComplex = when (value) {
        is GoExactComplex -> value
        else -> GoExactComplex(exactRational(value), GoRational.ZERO)
    }

    private fun exactConstantBinary(left: Any?, op: TokenKind, right: Any?): Any? {
        if (op == TokenKind.SHL || op == TokenKind.SHR) {
            val leftInteger = exactRational(left).integerValue("shift")
            val count = exactRational(right).integerValue("shift count")
            if (count.signum() < 0) throw RuntimeGoError("negative shift count")
            if (count > BigInteger.valueOf(Int.MAX_VALUE.toLong()))
                throw RuntimeGoError("untyped shift result exceeds implementation limits")
            return if (op == TokenKind.SHL) leftInteger.shiftLeft(count.toInt()) else leftInteger.shiftRight(count.toInt())
        }
        if (left is GoExactComplex || right is GoExactComplex) {
            if (left is GoComplex || right is GoComplex || left is GoFloat || right is GoFloat || left is Double || right is Double) {
                val a = complexValue(left)
                val b = complexValue(right)
                return a.real == b.real && a.imaginary == b.imaginary
            }
            val a = exactComplex(left)
            val b = exactComplex(right)
            return when (op) {
                TokenKind.ADD -> GoExactComplex(a.real + b.real, a.imaginary + b.imaginary)
                TokenKind.SUB -> GoExactComplex(a.real - b.real, a.imaginary - b.imaginary)
                TokenKind.MUL -> GoExactComplex(a.real * b.real - a.imaginary * b.imaginary,
                    a.real * b.imaginary + a.imaginary * b.real)
                TokenKind.QUO -> {
                    val denominator = b.real * b.real + b.imaginary * b.imaginary
                    GoExactComplex((a.real * b.real + a.imaginary * b.imaginary) / denominator,
                        (a.imaginary * b.real - a.real * b.imaginary) / denominator)
                }
                else -> throw RuntimeGoError("invalid complex constant operator $op")
            }
        }
        val a = exactRational(left)
        val b = exactRational(right)
        return when (op) {
            TokenKind.ADD -> a + b
            TokenKind.SUB -> a - b
            TokenKind.MUL -> a * b
            TokenKind.QUO -> a / b
            TokenKind.LSS -> a < b
            TokenKind.LEQ -> a <= b
            TokenKind.GTR -> a > b
            TokenKind.GEQ -> a >= b
            else -> throw RuntimeGoError("invalid real constant operator $op")
        }
    }

    private fun binary(left: Any?, op: TokenKind, right: Any?): Any? {
        if (op == TokenKind.EQL || op == TokenKind.NEQ) {
            val equal = goEqual(left, right)
            return if (op == TokenKind.EQL) equal else !equal
        }
        if (op == TokenKind.LAND || op == TokenKind.LOR) {
            val a = booleanValue(left, "logical operator")
            val b = booleanValue(right, "logical operator")
            return if (op == TokenKind.LAND) a && b else a || b
        }
        if (left is GoString && right is GoString) {
            if (op == TokenKind.ADD) {
                val resultType = when {
                    left.type != NamedGoType("string") -> left.type
                    right.type != NamedGoType("string") -> right.type
                    else -> left.type
                }
                return GoString(left.bytes + right.bytes, resultType)
            }
            val comparison = compareGoStrings(left, right)
            return when (op) {
                TokenKind.LSS -> comparison < 0
                TokenKind.LEQ -> comparison <= 0
                TokenKind.GTR -> comparison > 0
                TokenKind.GEQ -> comparison >= 0
                else -> throw RuntimeGoError("invalid string operator $op")
            }
        }
        if (left is GoRational || right is GoRational || left is GoExactComplex || right is GoExactComplex) {
            val typedOperand = listOf(left, right).firstOrNull {
                it is GoInteger || it is GoFloat || it is GoComplex || it is Long || it is Double
            }
            if (typedOperand != null) {
                return binary(materializeExactConstant(left, typedOperand), op, materializeExactConstant(right, typedOperand))
            }
            return exactConstantBinary(left, op, right)
        }
        if (left is GoComplex || right is GoComplex) {
            val a = complexValue(left)
            val b = complexValue(right)
            val resultType = (left as? GoComplex)?.type ?: (right as? GoComplex)?.type ?: NamedGoType("complex128")
            fun result(real: Double, imaginary: Double): GoComplex = if (underlying(resultType) == NamedGoType("complex64"))
                GoComplex(real.toFloat().toDouble(), imaginary.toFloat().toDouble(), resultType)
            else GoComplex(real, imaginary, resultType)
            return when (op) {
                TokenKind.ADD -> result(a.real + b.real, a.imaginary + b.imaginary)
                TokenKind.SUB -> result(a.real - b.real, a.imaginary - b.imaginary)
                TokenKind.MUL -> result(a.real * b.real - a.imaginary * b.imaginary,
                    a.real * b.imaginary + a.imaginary * b.real)
                TokenKind.QUO -> {
                    val denominator = b.real * b.real + b.imaginary * b.imaginary
                    result((a.real * b.real + a.imaginary * b.imaginary) / denominator,
                        (a.imaginary * b.real - a.real * b.imaginary) / denominator)
                }
                else -> throw RuntimeGoError("invalid complex operator $op")
            }
        }
        if (left is Double || right is Double || left is GoFloat || right is GoFloat) {
            val a = real(left); val b = real(right)
            val resultType = (left as? GoFloat)?.type ?: (right as? GoFloat)?.type
            fun result(value: Double): Any = if (resultType == null) value else GoFloat(
                if (underlying(resultType) == NamedGoType("float32")) value.toFloat().toDouble() else value,
                resultType
            )
            return when (op) {
                TokenKind.ADD -> result(a + b); TokenKind.SUB -> result(a - b); TokenKind.MUL -> result(a * b); TokenKind.QUO -> result(a / b)
                TokenKind.LSS -> a < b; TokenKind.LEQ -> a <= b; TokenKind.GTR -> a > b; TokenKind.GEQ -> a >= b
                else -> throw RuntimeGoError("invalid floating-point operator $op")
            }
        }
        val leftType = (left as? GoInteger)?.type ?: if (left is Long) NamedGoType("int") else null
        val rightType = (right as? GoInteger)?.type ?: if (right is Long) NamedGoType("int") else null
        val integerType = if (op == TokenKind.SHL || op == TokenKind.SHR) leftType else leftType ?: rightType
        val a = integerValue(left, op.name)
        val b = integerValue(right, op.name)
        val compare = a.compareTo(b)
        when (op) {
            TokenKind.LSS -> return compare < 0
            TokenKind.LEQ -> return compare <= 0
            TokenKind.GTR -> return compare > 0
            TokenKind.GEQ -> return compare >= 0
            else -> Unit
        }
        val shift = if (op == TokenKind.SHL || op == TokenKind.SHR) b else BigInteger.ZERO
        if (shift.signum() < 0) throw RuntimeGoError("negative shift count")
        if (shift > BigInteger.valueOf(Int.MAX_VALUE.toLong())) {
            if (integerType == null) throw RuntimeGoError("untyped shift result exceeds implementation limits")
            val saturated = when {
                op == TokenKind.SHL -> BigInteger.ZERO
                isUnsignedInteger(integerType) || a.signum() >= 0 -> BigInteger.ZERO
                else -> BigInteger.ONE.negate()
            }
            return GoInteger(wrapInteger(saturated.toLong(), integerType), integerType)
        }
        val result = when (op) {
            TokenKind.ADD -> a + b
            TokenKind.SUB -> a - b
            TokenKind.MUL -> a * b
            TokenKind.QUO -> when {
                b.signum() == 0 -> throw RuntimeGoError("integer divide by zero")
                else -> a / b
            }
            TokenKind.REM -> when {
                b.signum() == 0 -> throw RuntimeGoError("integer divide by zero")
                else -> a % b
            }
            TokenKind.AND -> a.and(b)
            TokenKind.OR -> a.or(b)
            TokenKind.XOR -> a.xor(b)
            TokenKind.AND_NOT -> a.and(b.not())
            TokenKind.SHL -> a.shiftLeft(shift.toInt())
            TokenKind.SHR -> a.shiftRight(shift.toInt())
            else -> throw RuntimeGoError("invalid operator $op")
        }
        return integerType?.let { GoInteger(wrapInteger(result.toLong(), it), it) } ?: result
    }

    private fun goEqual(left: Any?, right: Any?): Boolean {
        if (left is GoBoolean || right is GoBoolean)
            return runCatching { booleanValue(left, "comparison") == booleanValue(right, "comparison") }.getOrDefault(false)
        if (left is GoPointer && right == null) return left.isNil
        if (right is GoPointer && left == null) return right.isNil
        if (left is GoNilValue && right == null || right is GoNilValue && left == null) return true
        if (left is GoNilValue && right is GoNilValue) {
            if (sameRuntimeType(left.type, right.type)) return true
            val leftType = underlying(left.type)
            val rightType = underlying(right.type)
            if (leftType is PointerGoType && rightType is PointerGoType)
                return sameRuntimeType(leftType.element, rightType.element)
            if (leftType is ChannelGoType && rightType is ChannelGoType) {
                val sameElement = sameRuntimeType(leftType.element, rightType.element)
                val compatibleDirection = leftType.direction == rightType.direction ||
                    leftType.direction == ChannelDirection.SEND_RECEIVE ||
                    rightType.direction == ChannelDirection.SEND_RECEIVE
                return sameElement && compatibleDirection
            }
            return false
        }
        if (left is GoInterfaceValue || right is GoInterfaceValue) {
            if (left == null || right == null) return left == null && right == null
            val leftType = (left as? GoInterfaceValue)?.dynamicType ?: runtimeType(left)
            val rightType = (right as? GoInterfaceValue)?.dynamicType ?: runtimeType(right)
            if (leftType != rightType) return false
            val leftInterface = left as? GoInterfaceValue
            val rightInterface = right as? GoInterfaceValue
            val leftValue = if (leftInterface != null) leftInterface.value else left
            val rightValue = if (rightInterface != null) rightInterface.value else right
            if (!runtimeComparable(leftValue) || !runtimeComparable(rightValue))
                throw RuntimeGoError("comparing uncomparable type ${leftType ?: "interface value"}")
            return goEqual(leftValue, rightValue)
        }
        if (left is GoExactComplex || right is GoExactComplex) {
            val a = exactComplex(left)
            val b = exactComplex(right)
            return a.real == b.real && a.imaginary == b.imaginary
        }
        if (left is GoRational || right is GoRational) {
            if (left is GoComplex || left is GoFloat || left is Double || right is GoComplex || right is GoFloat || right is Double) {
                val a = complexValue(left)
                val b = complexValue(right)
                return a.real == b.real && a.imaginary == b.imaginary
            }
            return runCatching { exactRational(left) == exactRational(right) }.getOrDefault(false)
        }
        if (left is GoComplex && right is GoComplex) return left.real == right.real && left.imaginary == right.imaginary
        if (left is GoComplex || right is GoComplex) {
            val a = complexValue(left)
            val b = complexValue(right)
            return a.real == b.real && a.imaginary == b.imaginary
        }
        if (left is GoInteger || right is GoInteger) {
            val a = runCatching { integerValue(left, "comparison") }.getOrNull() ?: return false
            val b = runCatching { integerValue(right, "comparison") }.getOrNull() ?: return false
            return a == b
        }
        if (left is BigInteger || right is BigInteger) {
            val a = runCatching { integerValue(left, "comparison") }.getOrNull() ?: return false
            val b = runCatching { integerValue(right, "comparison") }.getOrNull() ?: return false
            return a == b
        }
        if (left is GoFloat || right is GoFloat) return real(left) == real(right)
        if (left is Double && right is Double) return left == right
        if (left is GoArray && right is GoArray)
            return left.values.size == right.values.size &&
                left.values.indices.all { goEqual(left.values[it], right.values[it]) }
        if (left is GoStruct && right is GoStruct) return left == right
        return left == right
    }

    private fun compareGoStrings(left: GoString, right: GoString): Int {
        val leftBytes = left.bytes
        val rightBytes = right.bytes
        for (i in 0 until minOf(leftBytes.size, rightBytes.size)) {
            val difference = (leftBytes[i].toInt() and 0xff) - (rightBytes[i].toInt() and 0xff)
            if (difference != 0) return difference
        }
        return leftBytes.size.compareTo(rightBytes.size)
    }

    private fun runtimeComparable(value: Any?): Boolean = when (value) {
        is GoSlice, is GoMap, is FunctionValue -> false
        is GoNilValue -> when (underlying(value.type)) {
            is SliceGoType, is MapGoType, is FunctionGoType -> false
            else -> true
        }
        is GoArray -> value.values.all(::runtimeComparable)
        is GoStruct -> value.fields.values.all(::runtimeComparable)
        is GoInterfaceValue -> runtimeComparable(value.value)
        else -> true
    }

    private fun goHash(value: Any?): Int = when (value) {
        null -> 0
        is GoRational -> value.hashCode()
        is GoExactComplex -> 31 * value.real.hashCode() + value.imaginary.hashCode()
        is GoBoolean -> value.value.hashCode()
        is Double -> if (value == 0.0) 0 else value.hashCode()
        is GoFloat -> if (value.value == 0.0) 0 else value.value.hashCode()
        is GoComplex -> 31 * (if (value.real == 0.0) 0 else value.real.hashCode()) + (if (value.imaginary == 0.0) 0 else value.imaginary.hashCode())
        is GoArray -> value.values.fold(1) { hash, element -> 31 * hash + goHash(element) }
        is GoStruct -> value.fields.entries.fold(value.namedType?.hashCode() ?: 0) { hash, (name, element) ->
            31 * (31 * hash + name.hashCode()) + goHash(element)
        }
        is GoInterfaceValue -> 31 * value.dynamicType.hashCode() + goHash(value.value)
        else -> value.hashCode()
    }

    private fun number(value: Any?, op: String): Long = when (value) {
        is Long -> value
        is GoInteger -> try { integerValue(value, op).longValueExact() }
            catch (_: ArithmeticException) { throw RuntimeGoError("integer out of range for $op") }
        is BigInteger -> try { value.longValueExact() }
            catch (_: ArithmeticException) { throw RuntimeGoError("integer out of range for $op") }
        else -> typeError(op, value)
    }
    private fun integerValue(value: Any?, op: String): BigInteger = when (value) {
        is BigInteger -> value
        is Long -> BigInteger.valueOf(value)
        is GoInteger -> {
            val integer = BigInteger.valueOf(value.value)
            if (isUnsignedInteger(value.type) && value.value < 0L)
                integer.add(BigInteger.ONE.shiftLeft(Long.SIZE_BITS)) else integer
        }
        else -> typeError(op, value)
    }
    private fun defaultIntegerValue(value: Any?): Any = if (value is BigInteger) {
        try { GoInteger(value.longValueExact(), NamedGoType("int")) } catch (_: ArithmeticException) {
            throw RuntimeGoError("constant overflows default int")
        }
    } else value ?: throw RuntimeGoError("invalid integer value")
    private fun defaultConstantValue(value: Any?, expression: Expression? = null, env: Environment? = null): Any = when {
        value is BigInteger && expression != null && env != null && isRuneConstantExpression(expression, env) ->
            GoInteger(value.longValueExact(), NamedGoType("rune"))
        value is GoRational -> value.toDouble()
        value is GoExactComplex -> GoComplex(value.real.toDouble(), value.imaginary.toDouble(), NamedGoType("complex128"))
        else -> defaultIntegerValue(value)
    }

    private fun defaultRuneValue(value: Any?, expression: Expression?, env: Environment): Any? =
        if (value is BigInteger && expression != null && isRuneConstantExpression(expression, env))
            GoInteger(value.longValueExact(), NamedGoType("rune")) else value

    private fun asRuneValue(value: Any?): Any? = if (value is BigInteger)
        GoInteger(value.longValueExact(), NamedGoType("rune")) else value

    private fun isRuneConstantExpression(expression: Expression, env: Environment): Boolean =
        integerConstantKind(expression, env) == 2

    /** 1 denotes an untyped integer constant; 2 denotes an untyped character constant. */
    private fun integerConstantKind(expression: Expression, env: Environment): Int? = when (expression) {
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> 1
            TokenKind.CHAR -> 2
            else -> null
        }
        is NameExpression -> when (env.typeOf(expression.name)) {
            untypedRuneRuntimeType -> 2
            null -> if (env.getOrNull(expression.name) is BigInteger) 1 else null
            else -> null
        }
        is ParenthesizedExpression -> integerConstantKind(expression.expression, env)
        is UnaryExpression -> if (expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.XOR))
            integerConstantKind(expression.operand, env) else null
        is BinaryExpression -> {
            val left = integerConstantKind(expression.left, env)
            val right = integerConstantKind(expression.right, env)
            when {
                expression.operator in setOf(TokenKind.SHL, TokenKind.SHR) -> if (left != null && right != null) 1 else null
                expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.MUL, TokenKind.QUO, TokenKind.REM,
                    TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT) && left != null && right != null -> maxOf(left, right)
                else -> null
            }
        }
        else -> null
    }

    private fun complexValue(value: Any?): GoComplex = when (value) {
        is GoComplex -> value
        is GoExactComplex -> GoComplex(value.real.toDouble(), value.imaginary.toDouble(), NamedGoType("complex128"))
        is GoRational -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is GoInteger -> GoComplex(integerAsDouble(value), 0.0, NamedGoType("complex128"))
        is GoFloat -> GoComplex(value.value, 0.0, NamedGoType("complex128"))
        is BigInteger -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is Long -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is Double -> GoComplex(value, 0.0, NamedGoType("complex128"))
        else -> typeError("complex arithmetic", value)
    }
    private fun imaginaryPart(text: String): GoRational = runCatching { GoRational.decimal(text) }
        .getOrElse { throw RuntimeGoError("invalid imaginary literal") }
    private fun real(value: Any?): Double = when (value) {
        is Long -> value.toDouble()
        is BigInteger -> value.toDouble()
        is GoRational -> value.toDouble()
        is GoInteger -> integerAsDouble(value)
        is Double -> value
        is GoFloat -> value.value
        is GoComplex -> value.real
        else -> typeError("arithmetic", value)
    }
    private fun floatResult(value: Double, complexType: GoTypeSyntax): Any =
        if (underlying(complexType) == NamedGoType("complex64")) GoFloat(value.toFloat().toDouble(), NamedGoType("float32")) else value
    private fun booleanValue(value: Any?, operation: String): Boolean = when (value) {
        is Boolean -> value
        is GoBoolean -> value.value
        else -> typeError(operation, value)
    }
    private fun truth(value: Any?) = booleanValue(value, "condition")
    private fun stringify(value: Any?): String = when (value) {
        null -> "<nil>"
        is GoNilValue -> "<nil>"
        is GoInterfaceValue -> stringify(value.value)
        is GoComplex -> "(${value.real}${if (value.imaginary < 0) "" else "+"}${value.imaginary}i)"
        is GoFloat -> value.value.toString()
        is GoRational -> value.toString()
        is GoExactComplex -> "(${value.real}+${value.imaginary}i)"
        is BigInteger -> value.toString()
        is GoInteger -> if (isUnsignedInteger(value.type)) java.lang.Long.toUnsignedString(value.value) else value.value.toString()
        is GoBoolean -> value.value.toString()
        is GoPointer -> if (value.isNil) "<nil>" else "&${stringify(value.get())}"
        is GoString -> value.toString()
        is FunctionValue -> "<function ${value.function.name}>"
        is GoSlice -> value.toList().joinToString(prefix = "[", postfix = "]") { stringify(it) }
        is GoArray -> value.values.joinToString(prefix = "[", postfix = "]") { stringify(it) }
        is GoMap -> value.values.entries.joinToString(prefix = "map[", postfix = "]") { "${stringify(it.key.value)}:${stringify(it.value)}" }
        is GoStruct -> value.fields.values.joinToString(prefix = "{", postfix = "}") { stringify(it) }
        else -> value.toString()
    }
    private fun <T> typeError(op: String, value: Any?): T = throw RuntimeGoError("invalid operand for $op: ${value?.javaClass?.simpleName ?: "nil"}")

    private fun compoundOperator(op: TokenKind) = when (op) {
        TokenKind.ADD_ASSIGN -> TokenKind.ADD; TokenKind.SUB_ASSIGN -> TokenKind.SUB; TokenKind.MUL_ASSIGN -> TokenKind.MUL
        TokenKind.QUO_ASSIGN -> TokenKind.QUO; TokenKind.REM_ASSIGN -> TokenKind.REM; TokenKind.AND_ASSIGN -> TokenKind.AND
        TokenKind.OR_ASSIGN -> TokenKind.OR; TokenKind.XOR_ASSIGN -> TokenKind.XOR; TokenKind.SHL_ASSIGN -> TokenKind.SHL
        TokenKind.SHR_ASSIGN -> TokenKind.SHR; TokenKind.AND_NOT_ASSIGN -> TokenKind.AND_NOT
        else -> throw RuntimeGoError("invalid compound assignment")
    }

    private fun decodeString(text: String): GoString = GoString(decodeGoStringLiteralBytes(text))

    private fun decodeUtf8Runes(bytes: ByteArray): List<Int> {
        val runes = mutableListOf<Int>()
        var offset = 0
        while (offset < bytes.size) {
            val (rune, width) = decodeUtf8Rune(bytes, offset)
            runes += rune
            offset += width
        }
        return runes
    }

    private fun decodeUtf8Rune(bytes: ByteArray, offset: Int): Pair<Int, Int> {
        val first = bytes[offset].toInt() and 0xff
        if (first < 0x80) return first to 1
        fun continuation(i: Int) = i < bytes.size && (bytes[i].toInt() and 0xc0) == 0x80
        if (first in 0xc2..0xdf && continuation(offset + 1)) {
            val cp = ((first and 0x1f) shl 6) or (bytes[offset + 1].toInt() and 0x3f)
            return cp to 2
        }
        if (first in 0xe0..0xef && continuation(offset + 1) && continuation(offset + 2)) {
            val second = bytes[offset + 1].toInt() and 0xff
            if ((first != 0xe0 || second >= 0xa0) && (first != 0xed || second < 0xa0)) {
                val cp = ((first and 0x0f) shl 12) or ((second and 0x3f) shl 6) or (bytes[offset + 2].toInt() and 0x3f)
                return cp to 3
            }
        }
        if (first in 0xf0..0xf4 && continuation(offset + 1) && continuation(offset + 2) && continuation(offset + 3)) {
            val second = bytes[offset + 1].toInt() and 0xff
            if ((first != 0xf0 || second >= 0x90) && (first != 0xf4 || second <= 0x8f)) {
                val cp = ((first and 0x07) shl 18) or ((second and 0x3f) shl 12) or
                    ((bytes[offset + 2].toInt() and 0x3f) shl 6) or (bytes[offset + 3].toInt() and 0x3f)
                return cp to 4
            }
        }
        return 0xfffd to 1
    }

    private fun decodeQuoted(text: String, quote: Char): String {
        if (text.length < 2 || text.first() != quote || text.last() != quote) throw RuntimeGoError("invalid quoted literal")
        val body = text.substring(1, text.length - 1)
        if (quote == '`') return body.replace("\r", "")
        val out = StringBuilder()
        var i = 0
        while (i < body.length) {
            val c = body[i++]
            if (c != '\\') { out.append(c); continue }
            if (i >= body.length) throw RuntimeGoError("unfinished escape")
            when (val escaped = body[i++]) {
                'a' -> out.append('\u0007'); 'b' -> out.append('\b'); 'f' -> out.append('\u000c'); 'n' -> out.append('\n')
                'r' -> out.append('\r'); 't' -> out.append('\t'); 'v' -> out.append('\u000b'); '\\' -> out.append('\\'); '"', '\'' -> out.append(escaped)
                'x', 'u', 'U' -> {
                    val digits = when (escaped) { 'x' -> 2; 'u' -> 4; else -> 8 }
                    if (i + digits > body.length) throw RuntimeGoError("short unicode escape")
                    val cp = body.substring(i, i + digits).toLongOrNull(16)?.toInt() ?: throw RuntimeGoError("invalid unicode escape")
                    out.appendCodePoint(cp); i += digits
                }
                in '0'..'7' -> {
                    val rest = body.getOrNull(i)?.takeIf { it in '0'..'7' }?.toString() ?: throw RuntimeGoError("short octal escape")
                    val third = body.getOrNull(i + 1)?.takeIf { it in '0'..'7' }?.toString() ?: throw RuntimeGoError("short octal escape")
                    out.append(("$escaped$rest$third").toInt(8).toChar()); i += 2
                }
                else -> throw RuntimeGoError("unknown escape sequence \\$escaped")
            }
        }
        return out.toString()
    }

    private inner class Environment(
        private val parent: Environment? = null,
        private val deferredCalls: MutableList<suspend () -> Unit> = mutableListOf(),
        val panicState: PanicState = parent?.panicState ?: PanicState()
    ) {
        private val values = mutableMapOf<String, Any?>()
        private val types = mutableMapOf<String, GoTypeSyntax>()
        private val namedTypes = mutableMapOf<String, NamedGoType>()
        private val addresses = mutableMapOf<String, GoPointer>()
        fun child() = Environment(this, deferredCalls, panicState)
        fun containsLocal(name: String) = values.containsKey(name)
        fun define(name: String, value: Any?, type: GoTypeSyntax? = null) {
            values[name] = type?.let { copyForType(value, it) } ?: copyValue(value)
            if (type != null) types[name] = type
        }
        fun get(name: String): Any? = lookup(name)?.value ?: if (contains(name)) null else throw RuntimeGoError("undefined: $name")
        fun lookup(name: String): Lookup? = if (values.containsKey(name)) Lookup(values[name]) else parent?.lookup(name)
        fun binding(name: String): Lookup? = when {
            values.containsKey(name) -> Lookup(values[name])
            name in namedTypes -> Lookup(TypeValue(namedTypes.getValue(name)))
            else -> parent?.binding(name)
        }
        fun getOrNull(name: String): Any? = lookup(name)?.value
        fun contains(name: String): Boolean = values.containsKey(name) || parent?.contains(name) == true
        fun typeOf(name: String): GoTypeSyntax? = types[name] ?: parent?.typeOf(name)
        fun defineType(name: String, type: NamedGoType) { namedTypes[name] = type }
        fun typeBinding(name: String): NamedGoType? = namedTypes[name] ?: parent?.typeBinding(name)
        fun pointer(name: String): GoPointer {
            val owner = owner(name) ?: throw RuntimeGoError("undefined: $name")
            return owner.addresses.getOrPut(name) {
                GoPointer.reference({ owner.get(name) }, { owner.set(name, it) }, owner.types[name] ?: runtimeType(owner.get(name)))
            }
        }
        private fun owner(name: String): Environment? = if (values.containsKey(name)) this else parent?.owner(name)
        fun defer(action: suspend () -> Unit) { deferredCalls += action }
        suspend fun runDefers() {
            val actions = deferredCalls.asReversed().toList()
            deferredCalls.clear()
            var panicFromDefer: PanicSignal? = null
            for (action in actions) {
                val previousPermission = panicState.recoverAllowed
                panicState.recoverAllowed = true
                try {
                    action()
                } catch (panic: PanicSignal) {
                    panicFromDefer = panic
                    panicState.activePanic = panic
                } catch (failure: RuntimeGoError) {
                    val panic = PanicSignal(failure.message ?: "runtime panic", failure.message ?: "runtime panic")
                    panicFromDefer = panic
                    panicState.activePanic = panic
                } finally {
                    panicState.recoverAllowed = previousPermission
                }
                if (panicState.activePanic == null && panicFromDefer?.recovered == true) panicFromDefer = null
            }
            panicFromDefer?.takeUnless { it.recovered }?.let { throw it }
        }
        fun set(name: String, value: Any?) {
            if (values.containsKey(name)) {
                val type = types[name]
                val assigned = type?.let { copyForType(value, it) } ?: copyValue(value)
                values[name] = if (type != null) preserveAggregateStorage(values[name], assigned, type) else assigned
            }
            else if (parent != null && parent.contains(name)) parent.set(name, value)
            else throw RuntimeGoError("undefined: $name")
        }
    }

    private fun preserveAggregateStorage(previous: Any?, assigned: Any?, type: GoTypeSyntax): Any? = when (val actual = underlying(type)) {
        is ArrayGoType -> {
            val oldArray = previous as? GoArray
            val newArray = assigned as? GoArray
            if (oldArray == null || newArray == null || oldArray.values.size != newArray.values.size) assigned
            else {
                oldArray.values.indices.forEach { index ->
                    oldArray.values[index] = preserveAggregateStorage(oldArray.values[index], newArray.values[index], actual.element)
                }
                oldArray
            }
        }
        is StructGoType -> {
            val oldStruct = previous as? GoStruct
            val newStruct = assigned as? GoStruct
            if (oldStruct == null || newStruct == null) assigned
            else {
                structFieldSlots(actual).forEach { field ->
                    if (field.name.isNotEmpty() && oldStruct.fields.containsKey(field.storageKey) && newStruct.fields.containsKey(field.storageKey))
                        oldStruct.fields[field.storageKey] = preserveAggregateStorage(
                            oldStruct.fields[field.storageKey], newStruct.fields[field.storageKey], field.type
                        )
                }
                oldStruct
            }
        }
        else -> assigned
    }

    private fun elementPointer(values: MutableList<Any?>, index: Int, elementType: GoTypeSyntax): GoPointer =
        synchronized(elementPointers) {
            elementPointers.getOrPut(values) { mutableMapOf() }.getOrPut(index) {
                GoPointer.reference({ values[index] }, { values[index] = copyForType(it, elementType) }, elementType)
            }
        }

    private data class Lookup(val value: Any?)
    private data class FunctionValue(val function: FunctionDeclaration, val closure: Environment, val type: GoTypeSyntax? = null)
    private data class BuiltinValue(val name: String)
    private data class TypeValue(val type: GoTypeSyntax)
    private data class MethodValue(val function: FunctionDeclaration, val receiver: Any?)
    private data class MethodExpressionValue(val receiverType: GoTypeSyntax, val name: String, val type: GoTypeSyntax)
    private data class GoMultiValue(val values: List<Any?>)
    private data class GoReceiveResult(val value: Any?, val ok: Boolean)
    private data class MapLookupResult(val value: Any?, val ok: Boolean)
    private data class GoAssertionResult(val value: Any?, val ok: Boolean, val dynamicType: GoTypeSyntax)
    private data class GoInterfaceValue(val dynamicType: GoTypeSyntax, val value: Any?)
    private data class GoNilValue(val type: GoTypeSyntax)
    private data class GoComplex(val real: Double, val imaginary: Double, val type: GoTypeSyntax)
    private data class GoFloat(val value: Double, val type: GoTypeSyntax)
    private data class GoBoolean(val value: Boolean, val type: GoTypeSyntax)
    private data class GoInteger(val value: Long, val type: GoTypeSyntax)
    private data class RuntimeTarget(val get: () -> Any?, val set: (Any?) -> Unit, val type: GoTypeSyntax? = null)
    private data class RuntimeStructField(
        val name: String,
        val storageKey: String,
        val type: GoTypeSyntax,
        val embedded: Boolean
    )
    private class PanicState(var activePanic: PanicSignal? = null, var recoverAllowed: Boolean = false)
    private class PanicSignal(val value: Any?, message: String) : RuntimeGoError(message) {
        var recovered: Boolean = false
    }
    private data class SelectSelection(val caseIndex: Int, val received: GoReceiveResult?)
    private sealed interface SelectOperation { val caseIndex: Int }
    private data class SelectSend(override val caseIndex: Int, val channel: GoChannel, val value: Any?) : SelectOperation
    private data class SelectReceive(override val caseIndex: Int, val channel: GoChannel, val assignment: AssignmentStatement?) : SelectOperation
    private inner class GoArray(
        val elementType: GoTypeSyntax,
        val values: MutableList<Any?>,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null
    ) {
        fun pointerAt(index: Int): GoPointer {
            if (index !in values.indices) throw RuntimeGoError("array index out of range")
            return elementPointer(values, index, elementType)
        }
        override fun equals(other: Any?) = other is GoArray && namedType == other.namedType && values.size == other.values.size &&
            values.indices.all { goEqual(values[it], other.values[it]) }
        override fun hashCode() = values.hashCode()
    }
    private inner class GoSlice(
        val elementType: GoTypeSyntax,
        private val backing: MutableList<Any?>,
        private val start: Int,
        val length: Int,
        val capacity: Int,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null
    ) {
        fun get(index: Int): Any? {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            return backing[start + index]
        }
        fun set(index: Int, value: Any?) {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            backing[start + index] = copyForType(value, elementType)
        }
        fun pointerAt(index: Int): GoPointer {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            val absolute = start + index
            return elementPointer(backing, absolute, elementType)
        }
        fun subSlice(low: Int, high: Int, max: Int): GoSlice {
            if (low < 0 || high < low || max < high || max > capacity) throw RuntimeGoError("slice bounds out of range")
            return GoSlice(elementType, backing, start + low, high - low, max - low, namedType, type)
        }
        fun retype(element: GoTypeSyntax, name: String?, type: GoTypeSyntax) =
            GoSlice(element, backing, start, length, capacity, name, type)
        fun append(values: List<Any?>): GoSlice {
            val required = length.toLong() + values.size
            if (required > Int.MAX_VALUE) throw RuntimeGoError("slice length out of range")
            if (required <= capacity) {
                values.forEachIndexed { i, value -> backing[start + length + i] = copyForType(value, elementType) }
                return GoSlice(elementType, backing, start, length + values.size, capacity, namedType, type)
            }
            val grownCapacity = minOf(capacity.toLong() * 2, Int.MAX_VALUE.toLong())
            val newCapacity = maxOf(required, maxOf(1L, grownCapacity)).toInt()
            val newBacking = zeroedSliceBacking(newCapacity, elementType)
            repeat(length) { newBacking[it] = get(it) }
            values.forEachIndexed { i, value -> newBacking[length + i] = copyForType(value, elementType) }
            return GoSlice(elementType, newBacking, 0, length + values.size, newCapacity, namedType, type)
        }
        fun toList(): List<Any?> = (0 until length).map(::get)
    }
    private inner class GoMap(
        val keyType: GoTypeSyntax,
        val valueType: GoTypeSyntax,
        val elementZero: Any?,
        val values: MutableMap<GoMapKey, Any?>,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null
    ) {
        fun retype(key: GoTypeSyntax, value: GoTypeSyntax, name: String?, type: GoTypeSyntax) =
            GoMap(key, value, zeroValue(value), values, name, type)
    }
    private inner class GoMapKey(val value: Any?) {
        override fun equals(other: Any?) = other is GoMapKey && goEqual(value, other.value)
        override fun hashCode() = goHash(value)
    }
    private inner class GoStruct(
        val fields: MutableMap<String, Any?>,
        val namedType: String? = null,
        val fieldTypes: Map<String, GoTypeSyntax> = emptyMap(),
        val embeddedFields: Set<String> = emptySet(),
        val staticType: GoTypeSyntax? = null
    ) {
        private val addresses = mutableMapOf<String, GoPointer>()
        fun pointer(field: String): GoPointer = addresses.getOrPut(field) {
            GoPointer.reference({ fields[field] }, { fields[field] = copyForType(it, fieldTypes[field] ?: NamedGoType("<unknown>")) }, fieldTypes[field])
        }
        override fun equals(other: Any?): Boolean {
            if (other !is GoStruct || namedType != other.namedType) return false
            val comparableFields = fields.keys.filterNot(::isBlankStorageKey)
            if (comparableFields.toSet() != other.fields.keys.filterNot(::isBlankStorageKey).toSet()) return false
            return comparableFields.all { goEqual(fields[it], other.fields[it]) }
        }
        override fun hashCode(): Int = 31 * (namedType?.hashCode() ?: 0) +
            fields.filterKeys { !isBlankStorageKey(it) }.hashCode()
    }

    private fun isBlankStorageKey(key: String) = key.startsWith("\u0000blank:")
    private class GoPointer(private val location: GoLocation?, val pointeeType: GoTypeSyntax? = null) {
        val isNil: Boolean get() = location == null
        fun get(): Any? = location?.get() ?: if (isNil) throw RuntimeGoError("invalid memory address or nil pointer dereference") else null
        fun retype(type: GoTypeSyntax) = GoPointer(location, type)
        fun set(value: Any?) {
            val target = location ?: throw RuntimeGoError("invalid memory address or nil pointer dereference")
            target.set(value)
        }
        override fun equals(other: Any?) = other is GoPointer && when {
            isNil || other.isNil -> isNil && other.isNil
            else -> location === other.location
        }
        override fun hashCode() = if (isNil) 0 else System.identityHashCode(location)

        companion object {
            fun reference(get: () -> Any?, set: (Any?) -> Unit, pointeeType: GoTypeSyntax? = null) =
                GoPointer(GoLocation(get, set), pointeeType)
            fun cell(value: Any?, pointeeType: GoTypeSyntax? = null) = GoCell(value).let { cell -> reference({ cell.value }, { cell.value = it }, pointeeType) }
            fun nil(pointeeType: GoTypeSyntax) = GoPointer(null, pointeeType)
        }
    }
    private class GoLocation(val get: () -> Any?, val set: (Any?) -> Unit)
    private class GoCell(var value: Any?)
    private inner class GoChannel(
        val elementType: GoTypeSyntax,
        val capacity: Int,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null,
        val direction: ChannelDirection = ChannelDirection.SEND_RECEIVE,
        val queue: Channel<Any?> = Channel(capacity),
        private val buffered: AtomicInteger = AtomicInteger(0),
        private val identity: Any = Any()
    ) {
        fun retype(element: GoTypeSyntax, direction: ChannelDirection, name: String?, type: GoTypeSyntax) =
            GoChannel(element, capacity, name, type, direction, queue, buffered, identity)

        override fun equals(other: Any?) = other is GoChannel && identity === other.identity
        override fun hashCode() = System.identityHashCode(identity)
        suspend fun send(value: Any?) {
            try {
                queue.send(copyForType(value, elementType))
            } catch (_: kotlinx.coroutines.channels.ClosedSendChannelException) {
                throw RuntimeGoError("send on closed channel")
            }
            if (capacity > 0) buffered.incrementAndGet()
        }
        suspend fun receive(): GoReceiveResult {
            val result = queue.receiveCatching()
            return decode(result)
        }
        fun trySend(value: Any?): Boolean {
            val result = queue.trySend(copyForType(value, elementType))
            if (result.isClosed) throw RuntimeGoError("send on closed channel")
            return result.isSuccess.also { if (it && capacity > 0) buffered.incrementAndGet() }
        }
        fun recordSelectSend() { if (capacity > 0) buffered.incrementAndGet() }
        fun tryReceive(): GoReceiveResult? {
            val result = queue.tryReceive()
            if (result.isFailure && !result.isClosed) return null
            return decode(result)
        }
        fun decode(result: kotlinx.coroutines.channels.ChannelResult<Any?>): GoReceiveResult {
            if (result.isSuccess) {
                if (capacity > 0) buffered.decrementAndGet()
                return GoReceiveResult(copyForType(result.getOrThrow(), elementType), true)
            }
            return GoReceiveResult(zeroValue(elementType), false)
        }
        fun close() {
            if (!queue.close()) throw RuntimeGoError("close of closed channel")
        }
        fun len() = if (capacity == 0) 0L else buffered.get().coerceAtLeast(0).toLong()
    }
    private class ReturnSignal(val values: List<Any?>, val runeConstants: List<Boolean> = emptyList()) : RuntimeException(null, null, false, false)
    private class BreakSignal(val label: String?) : RuntimeException(null, null, false, false)
    private class ContinueSignal(val label: String?) : RuntimeException(null, null, false, false)
    private class GotoSignal(val label: String) : RuntimeException(null, null, false, false)
    private class FallthroughSignal : RuntimeException(null, null, false, false)

    companion object {
        private val integerTypeNames = setOf("int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune")
        private val errorInterfaceType = InterfaceGoType(listOf(InterfaceMethodSyntax("Error", emptyList(), listOf(NamedGoType("string")))))
        private val builtinTypes = setOf("bool", "byte", "complex64", "complex128", "error", "float32", "float64", "int", "int8", "int16", "int32", "int64", "rune", "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr")
    }
}
