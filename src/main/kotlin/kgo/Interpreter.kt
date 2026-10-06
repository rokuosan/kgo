package kgo

import java.math.BigInteger
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.cancel
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.selects.selectUnbiased
import java.util.concurrent.atomic.AtomicInteger

open class RuntimeGoError(message: String) : RuntimeException(message)

/** Runtime for the currently implemented Go 1.0 execution subset. */
class Interpreter(private val output: (String) -> Unit = { print(it) }) {
    private val functions = mutableMapOf<String, FunctionDeclaration>()
    private val methods = mutableMapOf<String, FunctionDeclaration>()
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val globals = Environment()
    private val typeDefinitions = mutableMapOf<String, GoTypeSyntax>()
    private val fmtAliases = mutableSetOf("fmt")
    private lateinit var goroutines: CoroutineScope

    fun run(file: GoFile) {
        runBlocking {
            goroutines = CoroutineScope(SupervisorJob() + Dispatchers.Default)
            try {
                file.declarations.filterIsInstance<ImportDeclaration>().flatMap { it.imports }.forEach { spec ->
                    val alias = when (spec.alias) {
                        ".", "_" -> null
                        null -> spec.path.removeSurrounding("\"").substringAfterLast('/')
                        else -> spec.alias
                    }
                    if (alias != null && spec.path.removeSurrounding("\"").substringAfterLast('/') == "fmt") fmtAliases += alias
                }
        file.declarations.filterIsInstance<FunctionDeclaration>().forEach { function ->
                    if (function.receiver != null) methods[methodKey(function.receiver.type, function.name)] = function
                    else if (function.name == "init") initFunctions += function
                    else functions[function.name] = function
                }
                file.declarations.filterIsInstance<TypeDeclaration>().forEach { typeDefinitions[it.name] = it.type }
                val packageConstants = file.declarations.filterIsInstance<ConstantDeclaration>()
                val packageVariables = file.declarations.filterIsInstance<VariableDeclaration>()
                packageConstants.forEach { declaration -> declaration.names.forEach { name -> globals.define(name, null, declaration.type) } }
                packageVariables.forEach { declaration -> declaration.names.forEach { name ->
                    globals.define(name, declaration.type?.let(::zeroValue), declaration.type)
                } }
                orderPackageDeclarations(packageConstants, { it.names }, { it.values }, includeFunctionDependencies = false)
                    .forEach { initializeConstant(it) }
                orderPackageDeclarations(packageVariables, { it.names }, { it.values }, includeFunctionDependencies = true)
                    .forEach { initialize(it.names, it.values, globals, it.type) }
                initFunctions.forEach { invoke(it, emptyList()) }
                val main = functions["main"] ?: throw RuntimeGoError("main function not found")
                invoke(main, emptyList())
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
            arguments.take(fixedCount) + GoSlice(sliceType.element, extras.mapTo(mutableListOf(), ::copyValue), 0, extras.size, extras.size)
        }
        val env = Environment(parent, panicState = panicState)
        function.receiver?.let { env.define(it.name ?: "", receiver, it.type) }
        function.parameters.zip(boundArguments).forEachIndexed { i, (name, value) ->
            name?.let { env.define(it, value, function.parameterTypes.getOrNull(i)) }
        }
        val priorRecoverAllowed = panicState.recoverAllowed
        panicState.recoverAllowed = deferredCall
        var defersRun = false
        return try {
            executeBlock(function.body, env, createScope = false)
            emptyList()
        } catch (returned: ReturnSignal) {
            returned.values.mapIndexed { i, value -> function.resultTypes.getOrNull(i)?.let { boxInterface(value, it) } ?: value }
        } catch (panic: PanicSignal) {
            panicState.activePanic = panic
            defersRun = true
            env.runDefers()
            if (panic.recovered) function.resultTypes.map(::zeroValue) else throw panic
        } catch (failure: RuntimeGoError) {
            val panic = PanicSignal(failure.message ?: "runtime panic", failure.message ?: "runtime panic")
            panicState.activePanic = panic
            defersRun = true
            env.runDefers()
            if (panic.recovered) function.resultTypes.map(::zeroValue) else throw panic
        } finally {
            if (!defersRun) env.runDefers()
            panicState.recoverAllowed = priorRecoverAllowed
        }
    }

    private suspend fun executeBlock(block: BlockStatement, parent: Environment, createScope: Boolean = true) {
        val env = if (createScope) parent.child() else parent
        var index = 0
        while (index < block.statements.size) {
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

    private suspend fun execute(statement: Statement, env: Environment, labels: Set<String> = emptySet()) {
        when (statement) {
            EmptyStatement -> Unit
            is LabeledStatement -> execute(statement.statement, env, labels + statement.label)
            is DeclarationStatement -> statement.declarations.forEach { declaration ->
                when (declaration) {
                    is VariableDeclaration -> initialize(declaration.names, declaration.values, env, declaration.type)
                    is ConstantDeclaration -> initializeConstantIn(declaration, env)
                    is TypeDeclaration -> typeDefinitions[declaration.name] = declaration.type
                    else -> throw RuntimeGoError("unsupported local declaration")
                }
            }
            is BlockStatement -> executeBlock(statement, env)
            is VariableStatement -> initialize(statement.names, statement.values, env, statement.type)
            is ReturnStatement -> throw ReturnSignal(statement.values.map { copyValue(evaluate(it, env)) })
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
                when (val channel = evaluate(statement.channel, env)) {
                    is GoChannel -> channel.send(evaluate(statement.value, env))
                    is GoNilValue -> if (underlying(channel.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("send on non-channel")
                    else -> throw RuntimeGoError("send on non-channel")
                }
            }
            is GoStatement -> {
                val call = statement.call as? CallExpression ?: throw RuntimeGoError("go statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = call.arguments.map { copyValue(evaluate(it, env)) }
                goroutines.launch { call(target, arguments, call.expandLastArgument, PanicState()) }
            }
            is DeferStatement -> {
                val call = statement.call as? CallExpression ?: throw RuntimeGoError("defer statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = call.arguments.map { copyValue(evaluate(it, env)) }
                env.defer { call(target, arguments, call.expandLastArgument, env.panicState, deferredCall = true) }
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
        val values = expandValues(evaluateRhs(statement.values, statement.targets.size, env), statement.targets.size)
        assignValues(statement.targets, statement.operator, values, env)
    }

    private suspend fun assignValues(targets: List<Expression>, operator: TokenKind, values: List<Any?>, env: Environment) {
        if (operator == TokenKind.DEFINE) {
            val names = targets.map { (it as? NameExpression)?.name ?: throw RuntimeGoError("short declaration targets must be names") }
            if (names.size != values.size) throw RuntimeGoError("assignment count mismatch")
            val declared = mutableSetOf<String>()
            names.zip(values).forEach { (name, value) ->
                if (name == "_") return@forEach
                if (!declared.add(name)) throw RuntimeGoError("$name repeated on left side of :=")
                if (env.containsLocal(name)) env.set(name, value) else env.define(name, value)
            }
            return
        }
        if (targets.size != values.size) throw RuntimeGoError("assignment count mismatch")
        val locations = targets.map { resolveTarget(it, env) }
        val previous = if (operator == TokenKind.ASSIGN) emptyList() else locations.map { it.get() }
        locations.indices.forEach { i ->
            val value = if (operator == TokenKind.ASSIGN) values[i] else binary(previous[i], compoundOperator(operator), values[i])
            locations[i].set(value)
        }
    }

    private suspend fun resolveTarget(target: Expression, env: Environment): RuntimeTarget = when (target) {
        is ParenthesizedExpression -> resolveTarget(target.expression, env)
        is NameExpression -> if (target.name == "_") RuntimeTarget({ null }, {})
            else RuntimeTarget({ env.get(target.name) }, { env.set(target.name, it) })
        is IndexExpression -> {
            val receiver = evaluate(target.receiver, env)
            val key = evaluate(target.index, env)
            when (receiver) {
                is GoSlice -> {
                    val index = number(key, "index").toInt()
                    RuntimeTarget({ receiver.get(index) }, { receiver.set(index, it) })
                }
                is GoArray -> {
                    val index = number(key, "index").toInt()
                    RuntimeTarget({ arrayElement(receiver, index.toLong()) }, { setArrayElement(receiver, index.toLong(), it) })
                }
                is GoPointer -> {
                    val index = number(key, "index").toInt()
                    RuntimeTarget({
                        val array = receiver.get() as? GoArray ?: throw RuntimeGoError("index requires pointer to array")
                        arrayElement(array, index.toLong())
                    }, {
                        val array = receiver.get() as? GoArray ?: throw RuntimeGoError("index assignment requires pointer to array")
                        setArrayElement(array, index.toLong(), it)
                    })
                }
                is GoMap -> {
                    val mapKey = mapKey(key)
                    RuntimeTarget(
                        { if (receiver.values.containsKey(mapKey)) receiver.values[mapKey] else receiver.elementZero },
                        { receiver.values[mapKey] = copyForType(it, receiver.valueType) }
                    )
                }
                is GoNilValue -> {
                    val mapType = underlying(receiver.type) as? MapGoType
                        ?: throw RuntimeGoError("cannot assign through index")
                    mapKey(key)
                    RuntimeTarget({ zeroValue(mapType.value) }, { throw RuntimeGoError("assignment to entry in nil map") })
                }
                else -> throw RuntimeGoError("cannot assign through index")
            }
        }
        is SelectorExpression -> {
            val receiver = evaluate(target.receiver, env)
            if (receiver is GoPointer) RuntimeTarget(
                {
                    val struct = receiver.get() as? GoStruct ?: throw RuntimeGoError("selector assignment requires a struct")
                    if (!struct.fields.containsKey(target.field)) throw RuntimeGoError("unknown struct field: ${target.field}")
                    struct.fields[target.field]
                },
                { value ->
                    val struct = receiver.get() as? GoStruct ?: throw RuntimeGoError("selector assignment requires a struct")
                    if (!struct.fields.containsKey(target.field)) throw RuntimeGoError("unknown struct field: ${target.field}")
                    struct.fields[target.field] = struct.fieldTypes[target.field]?.let { copyForType(value, it) } ?: copyValue(value)
                }
            ) else {
                val struct = receiver as? GoStruct ?: throw RuntimeGoError("selector assignment requires a struct")
                if (!struct.fields.containsKey(target.field)) throw RuntimeGoError("unknown struct field: ${target.field}")
                RuntimeTarget(
                    { struct.fields[target.field] },
                    { value -> struct.fields[target.field] = struct.fieldTypes[target.field]?.let { copyForType(value, it) } ?: copyValue(value) }
                )
            }
        }
        is UnaryExpression -> {
            if (target.operator != TokenKind.MUL) throw RuntimeGoError("invalid assignment target")
            val pointer = evaluate(target.operand, env) as? GoPointer ?: throw RuntimeGoError("dereference of non-pointer")
            RuntimeTarget({ pointer.get() }, { value ->
                pointer.set(copyForType(value, pointer.pointeeType ?: runtimeType(pointer.get()) ?: NamedGoType("<unknown>")))
            })
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
                    val receive = communication.expression as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("invalid select receive clause")
                    val channel = selectChannelOrNull(evaluate(receive.operand, env)) ?: return@mapIndexedNotNull null
                    SelectReceive(caseIndex, channel, null)
                }
                is AssignmentStatement -> {
                    val receive = communication.values.singleOrNull() as? UnaryExpression
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
        val selected = selectUnbiased<SelectSelection> {
            operations.forEach { operation ->
                when (operation) {
                    is SelectSend -> operation.channel.queue.onSend(operation.value) { SelectSelection(operation.caseIndex, null) }
                    is SelectReceive -> operation.channel.queue.onReceiveCatching { result ->
                        SelectSelection(operation.caseIndex, operation.channel.decode(result))
                    }
                }
            }
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
                statement.clauses[index].statements.forEach { execute(it, scope) }
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
        val selected = statement.clauses.indexOfFirst { clause ->
            clause.types?.any { type ->
                if (type == NamedGoType("nil")) value == null
                else dynamicType != null && matchesDynamicType(dynamicType, type)
            } == true
        }.let { if (it >= 0) it else statement.clauses.indexOfFirst { clause -> clause.types == null } }
        if (selected < 0) return
        val clause = statement.clauses[selected]
        val singleType = clause.types?.singleOrNull()?.takeUnless { it == NamedGoType("nil") }
        val caseValue = when {
            singleType == null -> value
            underlying(singleType) is InterfaceGoType -> value
            else -> (value as? GoInterfaceValue)?.value
        }
        val caseScope = scope.child()
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
        NamedGoType("byte") -> NamedGoType("uint8")
        NamedGoType("rune") -> NamedGoType("int32")
        is PointerGoType -> PointerGoType(canonicalAliasType(type.element))
        is SliceGoType -> SliceGoType(canonicalAliasType(type.element))
        is ArrayGoType -> ArrayGoType(type.length, canonicalAliasType(type.element))
        is MapGoType -> MapGoType(canonicalAliasType(type.key), canonicalAliasType(type.value))
        is ChannelGoType -> ChannelGoType(canonicalAliasType(type.element), type.direction)
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = canonicalAliasType(it.type)) },
            type.results.map(::canonicalAliasType)
        )
        is StructGoType -> StructGoType(type.fields.map { it.copy(type = canonicalAliasType(it.type)) })
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
        val evaluated = copyValue(evaluate(range.expression, env))
        val value = if (evaluated is GoPointer &&
            (evaluated.pointeeType?.let { underlying(it) is ArrayGoType } == true || (!evaluated.isNil && evaluated.get() is GoArray)))
            copyValue(evaluated.get()) else evaluated
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
            is String -> {
                var byteIndex = 0L
                var charIndex = 0
                while (charIndex < value.length) {
                    val cp = value.codePointAt(charIndex)
                    if (range.targets.isNotEmpty()) {
                        val values = listOf(byteIndex, GoInteger(cp.toLong(), NamedGoType("rune"))).take(range.targets.size)
                        assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, env)
                    }
                    try { executeBlock(body, env) }
                    catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                    catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                    byteIndex += when { cp <= 0x7f -> 1; cp <= 0x7ff -> 2; cp <= 0xffff -> 3; else -> 4 }
                    charIndex += Character.charCount(cp)
                }
            }
            is GoSlice -> rangeIndexed(value.length, range, body, env, labels) { i -> listOf(i.toLong(), value.get(i)) }
            is GoArray -> rangeIndexed(value.values.size, range, body, env, labels) { i -> listOf(i.toLong(), value.values[i]) }
            is GoMap -> {
                for ((key, entryValue) in value.values.entries.toList()) {
                    if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN,
                        listOf(copyValue(key.value), entryValue).take(range.targets.size), env)
                    try { executeBlock(body, env) }
                    catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                    catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                }
            }
            else -> throw RuntimeGoError("range over this value is not implemented")
        }
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
            if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values(i).take(range.targets.size), env)
            try { executeBlock(body, env) }
            catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
            catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
        }
    }

    private suspend fun initialize(names: List<String>, expressions: List<Expression>, env: Environment, type: GoTypeSyntax? = null) {
        val values = expandValues(evaluateRhs(expressions, names.size, env), names.size)
        if (values.isNotEmpty() && values.size != names.size) throw RuntimeGoError("initializer count mismatch")
        names.forEachIndexed { i, name ->
            val value = if (values.isNotEmpty()) values[i].let { if (type != null) convert(type, it) else it }
            else if (type != null) zeroValue(type) else 0L
            env.define(name, value, type)
        }
    }

    private suspend fun initializeConstant(declaration: ConstantDeclaration) {
        initializeConstantIn(declaration, globals)
    }

    private suspend fun initializeConstantIn(declaration: ConstantDeclaration, target: Environment) {
        val scope = target.child()
        scope.define("iota", declaration.iotaIndex.toLong())
        val values = expandValues(declaration.values.map { evaluate(it, scope) }, declaration.names.size)
        if (values.size != declaration.names.size) throw RuntimeGoError("constant initializer count mismatch")
        declaration.names.zip(values).forEach { (name, value) -> target.define(name, value, declaration.type) }
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
            val functionReferences = statementNames(function.body) - functionLocalNames(function)
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
        is SliceExpression -> expressionNames(expression.receiver) + listOfNotNull(expression.low, expression.high, expression.max).flatMap(::expressionNames)
        is TypeAssertionExpression -> expressionNames(expression.receiver)
        is TypeSwitchGuardExpression -> expressionNames(expression.receiver)
        is ParenthesizedExpression -> expressionNames(expression.expression)
        is CompositeLiteral -> expression.elements.flatMapTo(linkedSetOf()) { element ->
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

    private fun functionLocalNames(initial: Set<String>, body: BlockStatement): Set<String> {
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
        if (expressions.size == 1 && arity == 2 && expressions[0] is IndexExpression) {
            val index = expressions[0] as IndexExpression
            val receiver = evaluate(index.receiver, env)
            val key = evaluate(index.index, env)
            if (receiver is GoMap) {
                val mapKey = mapKey(key)
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
        is NameExpression -> when (expression.name) {
            "true" -> true
            "false" -> false
            "nil" -> null
            "make", "new", "close", "len", "cap", "append", "copy", "delete", "print", "println", "panic", "recover", "complex", "real", "imag" -> BuiltinValue(expression.name)
            in builtinTypes -> TypeValue(NamedGoType(expression.name))
            in typeDefinitions -> TypeValue(NamedGoType(expression.name))
            else -> env.lookup(expression.name)?.value ?: if (env.contains(expression.name)) null else functions[expression.name]
                ?.let { FunctionValue(it, globals) } ?: throw RuntimeGoError("undefined: ${expression.name}")
        }
        is LiteralExpression -> literal(expression.token)
        is ParenthesizedExpression -> evaluate(expression.expression, env)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.AND -> addressOf(expression.operand, env)
            TokenKind.MUL -> {
                val pointer = evaluate(expression.operand, env) as? GoPointer
                    ?: throw RuntimeGoError("dereference of non-pointer")
                pointer.get()
            }
            else -> unary(expression.operator, evaluate(expression.operand, env))
        }
        is BinaryExpression -> {
            val left = copyValue(evaluate(expression.left, env))
            if (expression.operator == TokenKind.LAND && left == false) false
            else if (expression.operator == TokenKind.LOR && left == true) true
            else binary(left, expression.operator, copyValue(evaluate(expression.right, env)))
        }
        is SelectorExpression -> {
            if (expression.receiver is NameExpression && expression.receiver.name in fmtAliases) BuiltinValue(expression.field)
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
                    val struct = dereference(receiver) as? GoStruct ?: throw RuntimeGoError("selector is not defined for this value")
                    if (struct.fields.containsKey(expression.field)) struct.fields[expression.field]
                    else {
                        val method = methods["${struct.namedType}.${expression.field}"]
                            ?: throw RuntimeGoError("unknown struct field or method: ${expression.field}")
                        val pointerReceiver = method.receiver?.type is PointerGoType
                        val boundReceiver = when {
                            pointerReceiver && receiver is GoPointer -> receiver
                            pointerReceiver -> GoPointer.cell(receiver, runtimeType(receiver))
                            receiver is GoPointer -> copyValue(dereference(receiver))
                            else -> copyValue(receiver)
                        }
                        MethodValue(method, boundReceiver)
                    }
                }
            }
        }
        is CallExpression -> call(expression, env)
        is IndexExpression -> index(evaluate(expression.receiver, env), evaluate(expression.index, env))
        is SliceExpression -> slice(evaluate(expression.receiver, env), expression.low?.let { evaluate(it, env) },
            expression.high?.let { evaluate(it, env) }, expression.max?.let { evaluate(it, env) })
        is TypeAssertionExpression -> {
            val assertion = assertType(evaluate(expression.receiver, env), expression.type)
            if (!assertion.ok) throw RuntimeGoError("type assertion failed: ${assertion.dynamicType} is not ${expression.type}")
            assertion.value
        }
        is TypeSwitchGuardExpression -> throw RuntimeGoError("type switch guard used outside a type switch")
        is TypeExpression -> TypeValue(expression.type)
        is CompositeLiteral -> composite(expression, env)
        is FunctionLiteralExpression -> {
            val declaration = FunctionDeclaration(
                "<function literal>", expression.parameters.map { it.name }, expression.body,
                expression.parameters.map { it.type }, expression.results, null, expression.variadic
            )
            FunctionValue(declaration, env)
        }
    }

    private suspend fun addressOf(expression: Expression, env: Environment): GoPointer = when (expression) {
        is NameExpression -> env.pointer(expression.name)
        is SelectorExpression -> {
            val receiver = dereference(evaluate(expression.receiver, env)) as? GoStruct
                ?: throw RuntimeGoError("address-of selector requires a struct")
            if (!receiver.fields.containsKey(expression.field)) throw RuntimeGoError("unknown struct field: ${expression.field}")
            receiver.pointer(expression.field)
        }
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

    private suspend fun call(call: CallExpression, env: Environment): Any? {
        val target = evaluate(call.function, env)
        val args = call.arguments.map { copyValue(evaluate(it, env)) }
        return call(target, args, call.expandLastArgument, env.panicState)
    }

    private suspend fun call(
        target: Any?,
        args: List<Any?>,
        expandLastArgument: Boolean = false,
        panicState: PanicState = PanicState(),
        deferredCall: Boolean = false
    ): Any? {
        val effectiveArgs = if (expandLastArgument) {
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
                    val type = if (args.filterIsInstance<GoFloat>().any { underlying(it.type) == NamedGoType("float32") })
                        NamedGoType("complex64") else NamedGoType("complex128")
                    return GoComplex(real(args[0]), real(args[1]), type)
                }
                "real" -> return when (val value = args.singleOrNull()) {
                    is GoComplex -> floatResult(value.real, value.type)
                    is GoFloat -> value.value
                    is GoInteger -> integerAsDouble(value)
                    is Double -> value
                    is Long -> value.toDouble()
                    else -> throw RuntimeGoError("real requires a numeric argument")
                }
                "imag" -> return when (val value = args.singleOrNull()) {
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
                    is String -> value.toByteArray(Charsets.UTF_8).size.toLong()
                    is GoSlice -> value.length.toLong()
                    is GoArray -> value.values.size.toLong()
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
                    is GoNilValue -> when (underlying(value.type)) {
                        is SliceGoType, is ChannelGoType -> 0L
                        else -> throw RuntimeGoError("cap is not defined for this value")
                    }
                    else -> throw RuntimeGoError("cap is not defined for this value")
                }
                "append" -> return append(effectiveArgs)
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
                val backing = MutableList(literal.elements.size) { zeroValue(type.element) }
                literal.elements.forEachIndexed { i, element ->
                    val at = element.key?.let { number(evaluate(it, env), "slice literal index").toInt() } ?: i
                    if (at < 0 || at >= backing.size) throw RuntimeGoError("slice literal index out of range")
                    backing[at] = copyForType(evaluate(element.value, env), type.element)
                }
                GoSlice(type.element, backing, 0, backing.size, backing.size)
            }
            is ArrayGoType -> {
                val size = number(evaluate(type.length, env), "array length").toInt()
                if (size < 0) throw RuntimeGoError("negative array length")
                val values = MutableList(size) { zeroValue(type.element) }
                literal.elements.forEachIndexed { i, element ->
                    val at = element.key?.let { number(evaluate(it, env), "array literal index").toInt() } ?: i
                    if (at !in values.indices) throw RuntimeGoError("array literal index out of range")
                    values[at] = copyForType(evaluate(element.value, env), type.element)
                }
                GoArray(type.element, values)
            }
            is MapGoType -> {
                val values = linkedMapOf<GoMapKey, Any?>()
                literal.elements.forEach { element ->
                    val key = element.key?.let { evaluate(it, env) } ?: throw RuntimeGoError("map literal element requires a key")
                    values[mapKey(key)] = copyForType(evaluate(element.value, env), type.value)
                }
                GoMap(type.key, type.value, zeroValue(type.value), values)
            }
            is StructGoType -> {
                val fields = linkedMapOf<String, Any?>()
                val fieldList = type.fields.flatMap { f -> f.names.ifEmpty { listOf((f.type as? NamedGoType)?.name ?: "") }.map { it to f.type } }
                fieldList.forEach { (name, fieldType) -> if (name.isNotEmpty()) fields[name] = zeroValue(fieldType) }
                literal.elements.forEachIndexed { i, element ->
                    val name = if (element.key == null) fieldList.getOrNull(i)?.first else (element.key as? NameExpression)?.name
                    if (name == null || name !in fields) throw RuntimeGoError("unknown struct literal field")
                    val value = evaluate(element.value, env)
                    fields[name] = fieldList.firstOrNull { it.first == name }?.second?.let { copyForType(value, it) } ?: copyValue(value)
                }
                val fieldTypes = fieldList.filter { it.first.isNotEmpty() }.toMap()
                GoStruct(fields, (literal.type as? NamedGoType)?.name, fieldTypes)
            }
            else -> throw RuntimeGoError("composite literal for this type is not implemented")
        }
    }

    private fun underlying(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        is NamedGoType -> when (type.name) {
            "byte" -> NamedGoType("uint8")
            "rune" -> NamedGoType("int32")
            else -> typeDefinitions[type.name]?.let(::underlying) ?: if (type.name == "error") errorInterfaceType else type
        }
        else -> type
    }

    private fun boxInterface(value: Any?, targetType: GoTypeSyntax): Any? {
        if ((underlying(targetType) as? InterfaceGoType) == null || value == null || value is GoInterfaceValue) return value
        val dynamicType = runtimeType(value) ?: return value
        return GoInterfaceValue(dynamicType, value)
    }

    private fun runtimeType(value: Any?): GoTypeSyntax? = when (value) {
        is GoInterfaceValue -> value.dynamicType
        is GoStruct -> value.namedType?.let(::NamedGoType)
        is GoPointer -> value.pointeeType?.let(::PointerGoType) ?: runtimeType(value.get())?.let(::PointerGoType)
        is GoNilValue -> value.type
        is GoComplex -> value.type
        is GoFloat -> value.type
        is GoInteger -> when (value.type) {
            NamedGoType("byte") -> NamedGoType("uint8")
            NamedGoType("rune") -> NamedGoType("int32")
            else -> value.type
        }
        is GoSlice -> SliceGoType(value.elementType)
        is GoMap -> MapGoType(value.keyType, value.valueType)
        is GoChannel -> ChannelGoType(value.elementType, ChannelDirection.SEND_RECEIVE)
        is FunctionValue -> FunctionGoType(value.function.parameterTypes.mapIndexed { i, type ->
            ParameterSyntax(value.function.parameters.getOrNull(i), type, value.function.variadic && i == value.function.parameterTypes.lastIndex)
        }, value.function.resultTypes)
        is Long -> NamedGoType("int")
        is Double -> NamedGoType("float64")
        is String -> NamedGoType("string")
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
            if (key !in seen) interfaceMethodsRuntime(embedded, seen + key).forEach { (name, signature) -> result.putIfAbsent(name, signature) }
        }
        iface.methods.forEach { method -> result[method.name] = FunctionGoType(method.parameters, method.results) }
        return result
    }

    private fun runtimeMethodSet(type: GoTypeSyntax): Map<String, FunctionGoType> {
        val actual = underlying(type)
        if (actual is InterfaceGoType) return interfaceMethodsRuntime(actual)
        val pointer = type is PointerGoType
        val baseName = when (val base = if (pointer) type.element else type) {
            is NamedGoType -> base.name
            else -> return emptyMap()
        }
        val result = linkedMapOf<String, FunctionGoType>()
        methods.values.forEach { method ->
            val receiverType = method.receiver?.type ?: return@forEach
            val receiverBase = if (receiverType is PointerGoType) receiverType.element else receiverType
            if (receiverBase != NamedGoType(baseName)) return@forEach
            if (receiverType is PointerGoType && !pointer) return@forEach
            result[method.name] = FunctionGoType(method.parameterTypes.mapIndexed { i, parameter ->
                ParameterSyntax(method.parameters.getOrNull(i), parameter, method.variadic && i == method.parameterTypes.lastIndex)
            }, method.resultTypes)
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
        is GoStruct -> GoStruct(value.fields.mapValuesTo(linkedMapOf()) { copyValue(it.value) }, value.namedType, value.fieldTypes)
        is GoArray -> GoArray(value.elementType, value.values.mapTo(mutableListOf(), ::copyValue))
        is GoInterfaceValue -> GoInterfaceValue(value.dynamicType, copyValue(value.value))
        else -> value
    }

    private fun copyForType(value: Any?, type: GoTypeSyntax): Any? {
        val actual = underlying(type)
        val copied = if (value == null) when (actual) {
            is PointerGoType -> GoPointer.nil(actual.element)
            is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType -> GoNilValue(type)
            else -> null
        } else if (actual is NamedGoType && (actual.name in integerTypeNames || actual.name in setOf("complex64", "complex128", "float32"))) convert(type, value)
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
            is GoMap -> mapKey(rawIndex).let { if (receiver.values.containsKey(it)) receiver.values[it] else receiver.elementZero }
            is GoNilValue -> (underlying(receiver.type) as? MapGoType)?.let { zeroValue(it.value) }
                ?: throw RuntimeGoError("cannot index this value")
            is GoStruct -> {
                val field = rawIndex as? String ?: throw RuntimeGoError("struct field must be a name")
                if (receiver.fields.containsKey(field)) receiver.fields[field] else throw RuntimeGoError("unknown struct field: $field")
            }
            is String -> {
                val i = number(rawIndex, "index").toInt()
                val bytes = receiver.toByteArray(Charsets.UTF_8)
                if (i !in bytes.indices) throw RuntimeGoError("string index out of range")
                (bytes[i].toInt() and 0xff).toLong()
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
        return GoSlice(array.elementType, array.values, low, high - low, max - low)
    }

    private fun slice(receiver: Any?, lowValue: Any?, highValue: Any?, maxValue: Any?): Any? {
        val low = lowValue?.let { number(it, "slice index").toInt() } ?: 0
        return when (receiver) {
            is GoSlice -> {
                val high = highValue?.let { number(it, "slice index").toInt() } ?: receiver.length
                val max = maxValue?.let { number(it, "slice index").toInt() } ?: receiver.capacity
                receiver.subSlice(low, high, max)
            }
            is GoArray -> {
                val high = highValue?.let { number(it, "slice index").toInt() } ?: receiver.values.size
                val max = maxValue?.let { number(it, "slice index").toInt() } ?: receiver.values.size
                sliceArray(receiver, low, high, max)
            }
            is GoPointer -> {
                val array = receiver.get() as? GoArray ?: throw RuntimeGoError("slice requires pointer to array")
                val high = highValue?.let { number(it, "slice index").toInt() } ?: array.values.size
                val max = maxValue?.let { number(it, "slice index").toInt() } ?: array.values.size
                sliceArray(array, low, high, max)
            }
            is String -> {
                val bytes = receiver.toByteArray(Charsets.UTF_8)
                val high = highValue?.let { number(it, "slice index").toInt() } ?: bytes.size
                if (low < 0 || high < low || high > bytes.size || maxValue != null) throw RuntimeGoError("string slice bounds out of range")
                String(bytes.copyOfRange(low, high), Charsets.UTF_8)
            }
            else -> throw RuntimeGoError("cannot slice this value")
        }
    }

    private fun convert(type: GoTypeSyntax, value: Any?): Any? = when (val target = underlying(type)) {
        is PointerGoType -> if (value == null) GoPointer.nil(target.element) else value
        is SliceGoType -> {
            if (value is String && isByteOrRuneType(target.element)) {
                val converted = if (isByteType(target.element))
                    value.toByteArray(Charsets.UTF_8).map { (it.toInt() and 0xff).toLong() }
                else value.codePoints().toArray().map(Int::toLong)
                val backing = converted.mapTo(mutableListOf()) { copyForType(it, target.element) }
                GoSlice(target.element, backing, 0, backing.size, backing.size)
            } else if (value == null || value is GoNilValue && underlying(value.type) is SliceGoType) GoNilValue(type)
            else throw RuntimeGoError("cannot convert value to $type")
        }
        is MapGoType, is ChannelGoType, is FunctionGoType ->
            if (value == null || value is GoNilValue) GoNilValue(type) else value
        is NamedGoType -> when (target.name) {
            "string" -> when (value) {
                is String -> value
                is Long -> codePointString(value)
                is GoInteger -> codePointString(value.value)
                is GoSlice -> when {
                    isByteType(value.elementType) -> String(value.toList().map { number(it, "string conversion").toInt().toByte() }.toByteArray(), Charsets.UTF_8)
                    isRuneType(value.elementType) -> value.toList().joinToString("") { codePointString(number(it, "string conversion")) }
                    else -> throw RuntimeGoError("cannot convert slice to string")
                }
                is GoNilValue -> if (isByteOrRuneSlice(value.type)) "" else throw RuntimeGoError("cannot convert to string")
                else -> throw RuntimeGoError("cannot convert to string")
            }
            "bool" -> value as? Boolean ?: throw RuntimeGoError("cannot convert to bool")
            "float32", "float64" -> when (value) {
                is Long -> if (target.name == "float32") GoFloat(value.toFloat().toDouble(), type) else value.toDouble()
                is GoInteger -> integerAsDouble(value).let { if (target.name == "float32") GoFloat(it.toFloat().toDouble(), type) else it }
                is Double -> if (target.name == "float32") GoFloat(value.toFloat().toDouble(), type) else value
                is GoFloat -> if (target.name == "float32") GoFloat(value.value.toFloat().toDouble(), type) else value.value
                is GoComplex -> if (target.name == "float32") GoFloat(value.real.toFloat().toDouble(), type) else value.real
                else -> throw RuntimeGoError("cannot convert to float")
            }
            "complex64", "complex128" -> {
                val real = when (value) { is Long -> value.toDouble(); is GoInteger -> integerAsDouble(value); is Double -> value; is GoFloat -> value.value; is GoComplex -> value.real; else -> throw RuntimeGoError("cannot convert to complex") }
                val imaginary = (value as? GoComplex)?.imaginary ?: 0.0
                val convertedType = type
                if (target.name == "complex64") GoComplex(real.toFloat().toDouble(), imaginary.toFloat().toDouble(), convertedType)
                else GoComplex(real, imaginary, convertedType)
            }
            in integerTypeNames -> {
                val converted = when (value) {
                    is Long -> value
                    is GoInteger -> value.value
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

    private fun shiftCount(value: Any?, number: Long): Long =
        if (value is GoInteger && isUnsignedInteger(value.type) && number < 0) Long.MAX_VALUE else number

    private fun integerAsDouble(value: GoInteger): Double = if (isUnsignedInteger(value.type) && value.value < 0)
        java.lang.Long.toUnsignedString(value.value).toDouble() else value.value.toDouble()

    private fun codePointString(value: Long): String {
        val codePoint = value.toInt()
        return if (value !in 0..Character.MAX_CODE_POINT.toLong() || codePoint in 0xd800..0xdfff)
            "\ufffd" else String(Character.toChars(codePoint))
    }

    private fun append(args: List<Any?>): GoSlice {
        val first = args.firstOrNull()
        val slice = when (first) {
            is GoSlice -> first
            is GoNilValue -> (underlying(first.type) as? SliceGoType)?.let {
                GoSlice(it.element, mutableListOf(), 0, 0, 0)
            } ?: throw RuntimeGoError("append requires a slice")
            else -> throw RuntimeGoError("append requires a slice")
        }
        return slice.append(args.drop(1))
    }

    private fun copy(args: List<Any?>): Long {
        val destination = args.getOrNull(0) as? GoSlice ?: when (val nilDestination = args.getOrNull(0)) {
            is GoNilValue -> if (underlying(nilDestination.type) is SliceGoType) return 0L
                else throw RuntimeGoError("copy destination must be a slice")
            else -> throw RuntimeGoError("copy destination must be a slice")
        }
        val values = when (val source = args.getOrNull(1)) {
            is GoSlice -> source.toList()
            is GoNilValue -> if (underlying(source.type) is SliceGoType) emptyList() else throw RuntimeGoError("copy source must be a slice or string")
            is GoArray -> source.values.toList()
            is String -> source.toByteArray(Charsets.UTF_8).map { (it.toInt() and 0xff).toLong() }
            else -> throw RuntimeGoError("copy source must be a slice or string")
        }
        val count = minOf(destination.length, values.size)
        repeat(count) { destination.set(it, values[it]) }
        return count.toLong()
    }

    private fun delete(args: List<Any?>) {
        val map = args.getOrNull(0) as? GoMap ?: when (val nilMap = args.getOrNull(0)) {
            is GoNilValue -> if (underlying(nilMap.type) is MapGoType) return else throw RuntimeGoError("delete requires a map")
            else -> throw RuntimeGoError("delete requires a map")
        }
        map.values.remove(mapKey(args.getOrNull(1)))
    }

    private fun mapKey(value: Any?): GoMapKey {
        if (!runtimeComparable(value)) throw RuntimeGoError("hash of unhashable type")
        return GoMapKey(copyValue(value))
    }

    private fun literal(token: Token): Any = when (token.kind) {
        TokenKind.INT -> integer(token.lexeme)
        TokenKind.FLOAT -> token.lexeme.toDoubleOrNull() ?: throw RuntimeGoError("invalid float ${token.lexeme}")
        TokenKind.IMAG -> GoComplex(0.0, imaginaryPart(token.lexeme.removeSuffix("i")), NamedGoType("complex128"))
        TokenKind.CHAR -> decodeQuoted(token.lexeme, '\'').codePointAt(0).toLong()
        TokenKind.STRING -> decodeString(token.lexeme)
        else -> throw RuntimeGoError("invalid literal")
    }

    private fun integer(text: String): Long = try {
        val n = when {
            text.startsWith("0x", true) -> BigInteger(text.substring(2), 16)
            text.length > 1 && text.startsWith("0") -> BigInteger(text.substring(1), 8)
            else -> BigInteger(text, 10)
        }
        n.longValueExact()
    } catch (_: Exception) { throw RuntimeGoError("integer literal overflows int: $text") }

    private suspend fun unary(operator: TokenKind, value: Any?): Any? = when (operator) {
        TokenKind.ADD -> value
        TokenKind.SUB -> when (value) {
            is Long -> -value
            is GoInteger -> value.copy(value = wrapInteger(-value.value, value.type))
            is Double -> -value
            is GoFloat -> value.copy(value = -value.value)
            is GoComplex -> value.copy(real = -value.real, imaginary = -value.imaginary)
            else -> typeError("unary -", value)
        }
        TokenKind.NOT -> !(value as? Boolean ?: typeError("!", value))
        TokenKind.XOR -> when (value) {
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

    private fun make(args: List<Any?>): Any? {
        val type = underlying((args.firstOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("make requires a type"))
        return when (type) {
            is ChannelGoType -> {
                val capacity = args.getOrNull(1)?.let { number(it, "channel capacity").toInt() } ?: 0
                if (capacity < 0) throw RuntimeGoError("negative channel capacity")
                GoChannel(type.element, zeroValue(type.element), capacity)
            }
            is SliceGoType -> {
                val length = args.getOrNull(1)?.let { number(it, "slice length").toInt() }
                    ?: throw RuntimeGoError("make slice requires a length")
                val capacity = args.getOrNull(2)?.let { number(it, "slice capacity").toInt() } ?: length
                if (length < 0 || capacity < length) throw RuntimeGoError("invalid slice length or capacity")
                GoSlice(type.element, MutableList(capacity) { zeroValue(type.element) }, 0, length, capacity)
            }
            is MapGoType -> {
                val size = args.getOrNull(1)?.let { number(it, "map size hint").toInt() } ?: 0
                if (size < 0) throw RuntimeGoError("negative map size hint")
                GoMap(type.key, type.value, zeroValue(type.value), linkedMapOf())
            }
            else -> throw RuntimeGoError("make for this type is not implemented")
        }
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
            "bool" -> false
            "string" -> ""
            in integerTypeNames -> GoInteger(0L, type)
            "float32" -> GoFloat(0.0, type)
            "float64" -> 0.0
            "complex64", "complex128" -> GoComplex(0.0, 0.0, type)
            else -> null
        }
        is ArrayGoType -> {
            val length = runCatching { integerLiteral(actual.length) }.getOrDefault(0L).toInt().coerceAtLeast(0)
            GoArray(actual.element, MutableList(length) { zeroValue(actual.element) })
        }
        is StructGoType -> {
            val fields = linkedMapOf<String, Any?>()
            val fieldTypes = linkedMapOf<String, GoTypeSyntax>()
            actual.fields.forEach { field ->
                val names = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                names.filter { it.isNotEmpty() }.forEach { fields[it] = zeroValue(field.type); fieldTypes[it] = field.type }
            }
            GoStruct(fields, (type as? NamedGoType)?.name, fieldTypes)
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

    private fun integerLiteral(expression: Expression): Long = when (expression) {
        is LiteralExpression -> integer(expression.token.lexeme)
        is ParenthesizedExpression -> integerLiteral(expression.expression)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.ADD -> integerLiteral(expression.operand)
            TokenKind.SUB -> -integerLiteral(expression.operand)
            TokenKind.XOR -> integerLiteral(expression.operand).inv()
            else -> throw RuntimeGoError("invalid integer constant expression")
        }
        is BinaryExpression -> {
            val left = integerLiteral(expression.left)
            val right = integerLiteral(expression.right)
            when (expression.operator) {
                TokenKind.ADD -> left + right
                TokenKind.SUB -> left - right
                TokenKind.MUL -> left * right
                TokenKind.QUO -> if (right == 0L) throw RuntimeGoError("division by zero in array length") else left / right
                TokenKind.REM -> if (right == 0L) throw RuntimeGoError("division by zero in array length") else left % right
                TokenKind.AND -> left and right
                TokenKind.OR -> left or right
                TokenKind.XOR -> left xor right
                TokenKind.AND_NOT -> left and right.inv()
                TokenKind.SHL -> left shl right.toInt()
                TokenKind.SHR -> left shr right.toInt()
                else -> throw RuntimeGoError("invalid integer constant expression")
            }
        }
        else -> throw RuntimeGoError("array length is not a constant integer expression")
    }

    private fun binary(left: Any?, op: TokenKind, right: Any?): Any? {
        if (op == TokenKind.EQL || op == TokenKind.NEQ) {
            val equal = goEqual(left, right)
            return if (op == TokenKind.EQL) equal else !equal
        }
        if (op == TokenKind.LAND || op == TokenKind.LOR) {
            val a = left as? Boolean ?: typeError("logical operator", left)
            val b = right as? Boolean ?: typeError("logical operator", right)
            return if (op == TokenKind.LAND) a && b else a || b
        }
        if (left is String && right is String) {
            if (op == TokenKind.ADD) return left + right
            val comparison = compareGoStrings(left, right)
            return when (op) {
                TokenKind.LSS -> comparison < 0
                TokenKind.LEQ -> comparison <= 0
                TokenKind.GTR -> comparison > 0
                TokenKind.GEQ -> comparison >= 0
                else -> throw RuntimeGoError("invalid string operator $op")
            }
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
            val float32Type = (left as? GoFloat)?.type?.takeIf { underlying(it) == NamedGoType("float32") }
                ?: (right as? GoFloat)?.type?.takeIf { underlying(it) == NamedGoType("float32") }
            fun result(value: Double): Any = if (float32Type == null) value else GoFloat(value.toFloat().toDouble(), float32Type)
            return when (op) {
                TokenKind.ADD -> result(a + b); TokenKind.SUB -> result(a - b); TokenKind.MUL -> result(a * b); TokenKind.QUO -> result(a / b)
                TokenKind.LSS -> a < b; TokenKind.LEQ -> a <= b; TokenKind.GTR -> a > b; TokenKind.GEQ -> a >= b
                else -> throw RuntimeGoError("invalid floating-point operator $op")
            }
        }
        val a = number(left, op.name); val b = number(right, op.name)
        val integerType = if (op == TokenKind.SHL || op == TokenKind.SHR)
            (left as? GoInteger)?.type else (left as? GoInteger)?.type ?: (right as? GoInteger)?.type
        val unsigned = integerType?.let(::isUnsignedInteger) == true
        val compare = if (unsigned) java.lang.Long.compareUnsigned(a, b) else a.compareTo(b)
        when (op) {
            TokenKind.LSS -> return compare < 0
            TokenKind.LEQ -> return compare <= 0
            TokenKind.GTR -> return compare > 0
            TokenKind.GEQ -> return compare >= 0
            else -> Unit
        }
        val bits = integerType?.let(::integerBitWidth) ?: Long.SIZE_BITS
        val shift = if (op == TokenKind.SHL || op == TokenKind.SHR) shiftCount(right, b) else 0L
        if ((op == TokenKind.SHL || op == TokenKind.SHR) && shift < 0) throw RuntimeGoError("negative shift count")
        val result = when (op) {
            TokenKind.ADD -> a + b
            TokenKind.SUB -> a - b
            TokenKind.MUL -> a * b
            TokenKind.QUO -> when {
                b == 0L -> throw RuntimeGoError("integer divide by zero")
                unsigned -> java.lang.Long.divideUnsigned(a, b)
                a == Long.MIN_VALUE && b == -1L -> Long.MIN_VALUE
                else -> a / b
            }
            TokenKind.REM -> when {
                b == 0L -> throw RuntimeGoError("integer divide by zero")
                unsigned -> java.lang.Long.remainderUnsigned(a, b)
                a == Long.MIN_VALUE && b == -1L -> 0L
                else -> a % b
            }
            TokenKind.AND -> a and b
            TokenKind.OR -> a or b
            TokenKind.XOR -> a xor b
            TokenKind.AND_NOT -> a and b.inv()
            TokenKind.SHL -> if (shift >= bits) 0L else a shl shift.toInt()
            TokenKind.SHR -> when {
                shift >= bits -> if (!unsigned && a < 0) -1L else 0L
                unsigned -> a ushr shift.toInt()
                else -> a shr shift.toInt()
            }
            else -> throw RuntimeGoError("invalid operator $op")
        }
        return integerType?.let { GoInteger(wrapInteger(result, it), it) } ?: result
    }

    private fun goEqual(left: Any?, right: Any?): Boolean {
        if (left is GoPointer && right == null) return left.isNil
        if (right is GoPointer && left == null) return right.isNil
        if (left is GoNilValue && right == null || right is GoNilValue && left == null) return true
        if (left is GoNilValue && right is GoNilValue) return left.type == right.type
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
        if (left is GoComplex && right is GoComplex) return left.real == right.real && left.imaginary == right.imaginary
        if (left is GoComplex || right is GoComplex) {
            val a = complexValue(left)
            val b = complexValue(right)
            return a.real == b.real && a.imaginary == b.imaginary
        }
        if (left is GoInteger || right is GoInteger) {
            val a = (left as? GoInteger)?.value ?: (left as? Long) ?: return false
            val b = (right as? GoInteger)?.value ?: (right as? Long) ?: return false
            return a == b
        }
        if (left is GoFloat || right is GoFloat) return real(left) == real(right)
        if (left is Double && right is Double) return left == right
        if (left is GoArray && right is GoArray)
            return left.values.size == right.values.size &&
                left.values.indices.all { goEqual(left.values[it], right.values[it]) }
        if (left is GoStruct && right is GoStruct)
            return left.namedType == right.namedType && left.fields.keys == right.fields.keys &&
                left.fields.keys.all { goEqual(left.fields[it], right.fields[it]) }
        return left == right
    }

    private fun compareGoStrings(left: String, right: String): Int {
        val leftBytes = left.toByteArray(Charsets.UTF_8)
        val rightBytes = right.toByteArray(Charsets.UTF_8)
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
        is GoInteger -> value.value
        else -> typeError(op, value)
    }
    private fun complexValue(value: Any?): GoComplex = when (value) {
        is GoComplex -> value
        is GoInteger -> GoComplex(integerAsDouble(value), 0.0, NamedGoType("complex128"))
        is Long -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is Double -> GoComplex(value, 0.0, NamedGoType("complex128"))
        else -> typeError("complex arithmetic", value)
    }
    private fun imaginaryPart(text: String): Double = when {
        text.startsWith("0x", true) -> integer(text).toDouble()
        text.length > 1 && text.startsWith("0") && text[1].isDigit() -> integer(text).toDouble()
        else -> text.toDoubleOrNull() ?: throw RuntimeGoError("invalid imaginary literal")
    }
    private fun real(value: Any?): Double = when (value) {
        is Long -> value.toDouble()
        is GoInteger -> integerAsDouble(value)
        is Double -> value
        is GoFloat -> value.value
        is GoComplex -> value.real
        else -> typeError("arithmetic", value)
    }
    private fun floatResult(value: Double, complexType: GoTypeSyntax): Any =
        if (underlying(complexType) == NamedGoType("complex64")) GoFloat(value.toFloat().toDouble(), NamedGoType("float32")) else value
    private fun truth(value: Any?) = value as? Boolean ?: typeError("condition", value)
    private fun stringify(value: Any?): String = when (value) {
        null -> "<nil>"
        is GoNilValue -> "<nil>"
        is GoInterfaceValue -> stringify(value.value)
        is GoComplex -> "(${value.real}${if (value.imaginary < 0) "" else "+"}${value.imaginary}i)"
        is GoFloat -> value.value.toString()
        is GoInteger -> if (isUnsignedInteger(value.type)) java.lang.Long.toUnsignedString(value.value) else value.value.toString()
        is GoPointer -> if (value.isNil) "<nil>" else "&${stringify(value.get())}"
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

    private fun decodeString(text: String): String = decodeQuoted(text, '"')
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
        private val addresses = mutableMapOf<String, GoPointer>()
        fun child() = Environment(this, deferredCalls, panicState)
        fun containsLocal(name: String) = values.containsKey(name)
        fun define(name: String, value: Any?, type: GoTypeSyntax? = null) {
            values[name] = type?.let { copyForType(value, it) } ?: copyValue(value)
            if (type != null) types[name] = type
        }
        fun get(name: String): Any? = lookup(name)?.value ?: if (contains(name)) null else throw RuntimeGoError("undefined: $name")
        fun lookup(name: String): Lookup? = if (values.containsKey(name)) Lookup(values[name]) else parent?.lookup(name)
        fun getOrNull(name: String): Any? = lookup(name)?.value
        fun contains(name: String): Boolean = values.containsKey(name) || parent?.contains(name) == true
        fun typeOf(name: String): GoTypeSyntax? = types[name] ?: parent?.typeOf(name)
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
            if (values.containsKey(name)) values[name] = types[name]?.let { copyForType(value, it) } ?: copyValue(value)
            else if (parent != null && parent.contains(name)) parent.set(name, value)
            else throw RuntimeGoError("undefined: $name")
        }
    }

    private data class Lookup(val value: Any?)
    private data class FunctionValue(val function: FunctionDeclaration, val closure: Environment)
    private data class BuiltinValue(val name: String)
    private data class TypeValue(val type: GoTypeSyntax)
    private data class MethodValue(val function: FunctionDeclaration, val receiver: Any?)
    private data class GoMultiValue(val values: List<Any?>)
    private data class GoReceiveResult(val value: Any?, val ok: Boolean)
    private data class MapLookupResult(val value: Any?, val ok: Boolean)
    private data class GoAssertionResult(val value: Any?, val ok: Boolean, val dynamicType: GoTypeSyntax)
    private data class GoInterfaceValue(val dynamicType: GoTypeSyntax, val value: Any?)
    private data class GoNilValue(val type: GoTypeSyntax)
    private data class GoComplex(val real: Double, val imaginary: Double, val type: GoTypeSyntax)
    private data class GoFloat(val value: Double, val type: GoTypeSyntax)
    private data class GoInteger(val value: Long, val type: GoTypeSyntax)
    private data class RuntimeTarget(val get: () -> Any?, val set: (Any?) -> Unit)
    private class PanicState(var activePanic: PanicSignal? = null, var recoverAllowed: Boolean = false)
    private class PanicSignal(val value: Any?, message: String) : RuntimeGoError(message) {
        var recovered: Boolean = false
    }
    private data class SelectSelection(val caseIndex: Int, val received: GoReceiveResult?)
    private sealed interface SelectOperation { val caseIndex: Int }
    private data class SelectSend(override val caseIndex: Int, val channel: GoChannel, val value: Any?) : SelectOperation
    private data class SelectReceive(override val caseIndex: Int, val channel: GoChannel, val assignment: AssignmentStatement?) : SelectOperation
    private inner class GoArray(val elementType: GoTypeSyntax, val values: MutableList<Any?>) {
        private val addresses = mutableMapOf<Int, GoPointer>()
        fun pointerAt(index: Int): GoPointer {
            if (index !in values.indices) throw RuntimeGoError("array index out of range")
            return addresses.getOrPut(index) { GoPointer.reference({ values[index] }, { values[index] = copyForType(it, elementType) }, elementType) }
        }
        override fun equals(other: Any?) = other is GoArray && values.size == other.values.size &&
            values.indices.all { goEqual(values[it], other.values[it]) }
        override fun hashCode() = values.hashCode()
    }
    private inner class GoSlice(val elementType: GoTypeSyntax, private val backing: MutableList<Any?>, private val start: Int, val length: Int, val capacity: Int) {
        private val addresses = mutableMapOf<Int, GoPointer>()
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
            return addresses.getOrPut(index) { GoPointer.reference({ backing[absolute] }, { backing[absolute] = copyForType(it, elementType) }, elementType) }
        }
        fun subSlice(low: Int, high: Int, max: Int): GoSlice {
            if (low < 0 || high < low || max < high || max > capacity) throw RuntimeGoError("slice bounds out of range")
            return GoSlice(elementType, backing, start + low, high - low, max - low)
        }
        fun append(values: List<Any?>): GoSlice {
            if (length + values.size <= capacity) {
                values.forEachIndexed { i, value -> backing[start + length + i] = copyForType(value, elementType) }
                return GoSlice(elementType, backing, start, length + values.size, capacity)
            }
            val newCapacity = maxOf(length + values.size, maxOf(1, capacity * 2))
            val newBacking = MutableList(newCapacity) { zeroValue(elementType) }
            repeat(length) { newBacking[it] = get(it) }
            values.forEachIndexed { i, value -> newBacking[length + i] = copyForType(value, elementType) }
            return GoSlice(elementType, newBacking, 0, length + values.size, newCapacity)
        }
        fun toList(): List<Any?> = (0 until length).map(::get)
    }
    private inner class GoMap(val keyType: GoTypeSyntax, val valueType: GoTypeSyntax, val elementZero: Any?, val values: MutableMap<GoMapKey, Any?>)
    private inner class GoMapKey(val value: Any?) {
        override fun equals(other: Any?) = other is GoMapKey && goEqual(value, other.value)
        override fun hashCode() = goHash(value)
    }
    private inner class GoStruct(
        val fields: MutableMap<String, Any?>,
        val namedType: String? = null,
        val fieldTypes: Map<String, GoTypeSyntax> = emptyMap()
    ) {
        private val addresses = mutableMapOf<String, GoPointer>()
        fun pointer(field: String): GoPointer = addresses.getOrPut(field) {
            GoPointer.reference({ fields[field] }, { fields[field] = copyForType(it, fieldTypes[field] ?: NamedGoType("<unknown>")) }, fieldTypes[field])
        }
        override fun equals(other: Any?) = other is GoStruct && namedType == other.namedType && fields.keys == other.fields.keys &&
            fields.keys.all { goEqual(fields[it], other.fields[it]) }
        override fun hashCode() = 31 * (namedType?.hashCode() ?: 0) + fields.hashCode()
    }
    private class GoPointer(private val location: GoLocation?, val pointeeType: GoTypeSyntax? = null) {
        val isNil: Boolean get() = location == null
        fun get(): Any? = location?.get() ?: if (isNil) throw RuntimeGoError("invalid memory address or nil pointer dereference") else null
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
    private inner class GoChannel(val elementType: GoTypeSyntax, private val elementZero: Any?, val capacity: Int) {
        val queue = Channel<Any?>(capacity)
        private val buffered = AtomicInteger(0)
        suspend fun send(value: Any?) {
            queue.send(copyForType(value, elementType))
            if (capacity > 0) buffered.incrementAndGet()
        }
        suspend fun receive(): GoReceiveResult {
            val result = queue.receiveCatching()
            return decode(result)
        }
        fun trySend(value: Any?): Boolean = queue.trySend(copyForType(value, elementType)).isSuccess.also { if (it && capacity > 0) buffered.incrementAndGet() }
        fun tryReceive(): GoReceiveResult? {
            val result = queue.tryReceive()
            if (result.isFailure && !result.isClosed) return null
            return decode(result)
        }
        fun decode(result: kotlinx.coroutines.channels.ChannelResult<Any?>): GoReceiveResult {
            if (result.isSuccess) {
                if (capacity > 0) buffered.updateAndGet { maxOf(0, it - 1) }
                return GoReceiveResult(result.getOrThrow(), true)
            }
            return GoReceiveResult(elementZero, false)
        }
        fun close() { queue.close() }
        fun len() = if (capacity == 0) 0L else buffered.get().toLong()
    }
    private class ReturnSignal(val values: List<Any?>) : RuntimeException(null, null, false, false)
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
