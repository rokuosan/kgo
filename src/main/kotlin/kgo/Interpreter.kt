package kgo

import java.math.BigInteger
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.cancel
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.selects.selectUnbiased
import java.util.concurrent.atomic.AtomicInteger

class RuntimeGoError(message: String) : RuntimeException(message)

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
                file.declarations.forEach { declaration ->
                    when (declaration) {
                        is FunctionDeclaration, is TypeDeclaration -> Unit
                        is VariableDeclaration -> initialize(declaration.names, declaration.values, globals, declaration.type)
                        is ConstantDeclaration -> initializeConstant(declaration)
                        is ImportDeclaration -> Unit
                    }
                }
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
        expandedVariadic: Boolean = false
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
            arguments.take(fixedCount) + GoSlice(sliceType.element, extras.toMutableList(), 0, extras.size, extras.size)
        }
        val env = Environment(parent)
        function.receiver?.let { env.define(it.name ?: "", receiver) }
        function.parameters.zip(boundArguments).forEach { (name, value) -> name?.let { env.define(it, value) } }
        return try {
            executeBlock(function.body, env)
            emptyList()
        } catch (returned: ReturnSignal) {
            returned.values
        } finally {
            env.runDefers()
        }
    }

    private suspend fun executeBlock(block: BlockStatement, parent: Environment) {
        val env = parent.child()
        for (statement in block.statements) execute(statement, env)
    }

    private suspend fun execute(statement: Statement, env: Environment) {
        when (statement) {
            EmptyStatement -> Unit
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
            is ReturnStatement -> throw ReturnSignal(statement.values.map { evaluate(it, env) })
            is ExpressionStatement -> evaluate(statement.expression, env)
            is AssignmentStatement -> assign(statement, env)
            is IncrementStatement -> {
                val old = number(readTarget(statement.target, env), "increment")
                writeTarget(statement.target, old + statement.delta, env)
            }
            is IfStatement -> {
                val scope = env.child()
                statement.init?.let { execute(it, scope) }
                if (truth(evaluate(statement.condition, scope))) executeBlock(statement.thenBranch, scope)
                else statement.elseBranch?.let { execute(it, scope) }
            }
            is ForStatement -> {
                val scope = env.child()
                if (statement.rangeClause != null) {
                    executeRange(statement.rangeClause, statement.body, scope)
                } else {
                    statement.init?.let { execute(it, scope) }
                    while (statement.condition == null || truth(evaluate(statement.condition, scope))) {
                        try { executeBlock(statement.body, scope) }
                        catch (_: ContinueSignal) { }
                        catch (_: BreakSignal) { break }
                        statement.post?.let { execute(it, scope) }
                    }
                }
            }
            is SendStatement -> {
                val channel = evaluate(statement.channel, env) as? GoChannel ?: throw RuntimeGoError("send on non-channel")
                channel.send(evaluate(statement.value, env))
            }
            is GoStatement -> {
                val call = statement.call as? CallExpression ?: throw RuntimeGoError("go statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = call.arguments.map { evaluate(it, env) }
                goroutines.launch { call(target, arguments, call.expandLastArgument) }
            }
            is DeferStatement -> {
                val call = statement.call as? CallExpression ?: throw RuntimeGoError("defer statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = call.arguments.map { evaluate(it, env) }
                env.defer { call(target, arguments, call.expandLastArgument) }
            }
            is BranchStatement -> when (statement.kind) {
                TokenKind.BREAK -> throw BreakSignal()
                TokenKind.CONTINUE -> throw ContinueSignal()
                TokenKind.FALLTHROUGH -> throw FallthroughSignal()
                else -> throw RuntimeGoError("invalid branch statement")
            }
            is SelectStatement -> executeSelect(statement, env)
            is SwitchStatement -> executeSwitch(statement, env)
        }
    }

    private suspend fun assign(statement: AssignmentStatement, env: Environment) {
        val values = expandValues(evaluateRhs(statement.values, statement.targets.size, env), statement.targets.size)
        assignValues(statement.targets, statement.operator, values, env)
    }

    private suspend fun assignValues(targets: List<Expression>, operator: TokenKind, values: List<Any?>, env: Environment) {
        if (operator == TokenKind.DEFINE) {
            val names = targets.map { (it as? NameExpression)?.name ?: throw RuntimeGoError("short declaration targets must be names") }
            if (names.size != values.size) throw RuntimeGoError("assignment count mismatch")
            names.zip(values).filter { it.first != "_" }.forEach { (name, value) -> env.define(name, value) }
            return
        }
        if (targets.size != values.size) throw RuntimeGoError("assignment count mismatch")
        targets.zip(values).forEach { (target, value) ->
            if (target is NameExpression && target.name == "_") return@forEach
            val result = if (operator == TokenKind.ASSIGN) value else {
                val left = readTarget(target, env)
                binary(left, compoundOperator(operator), value)
            }
            writeTarget(target, result, env)
        }
    }

    private suspend fun readTarget(target: Expression, env: Environment): Any? = when (target) {
        is NameExpression -> env.get(target.name)
        is IndexExpression -> index(evaluate(target.receiver, env), evaluate(target.index, env))
        is SelectorExpression -> evaluate(target, env)
        is UnaryExpression -> if (target.operator == TokenKind.MUL) evaluate(target, env)
            else throw RuntimeGoError("invalid assignment target")
        else -> throw RuntimeGoError("invalid assignment target")
    }

    private suspend fun writeTarget(target: Expression, value: Any?, env: Environment) {
        when (target) {
            is NameExpression -> env.set(target.name, value)
            is IndexExpression -> {
                val receiver = evaluate(target.receiver, env)
                val key = evaluate(target.index, env)
                when (receiver) {
                    is GoSlice -> receiver.set(number(key, "index").toInt(), value)
                    is GoArray -> receiver.values[number(key, "index").toInt()] = value
                    is GoMap -> receiver.values[key] = value
                    else -> throw RuntimeGoError("cannot assign through index")
                }
            }
            is SelectorExpression -> {
                val receiver = evaluate(target.receiver, env)
                val struct = dereference(receiver) as? GoStruct ?: throw RuntimeGoError("selector assignment requires a struct")
                if (!struct.fields.containsKey(target.field)) throw RuntimeGoError("unknown struct field: ${target.field}")
                struct.fields[target.field] = value
            }
            is UnaryExpression -> {
                if (target.operator != TokenKind.MUL) throw RuntimeGoError("invalid assignment target")
                val pointer = evaluate(target.operand, env) as? GoPointer ?: throw RuntimeGoError("dereference of non-pointer")
                pointer.set(value)
            }
            else -> throw RuntimeGoError("invalid assignment target")
        }
    }

    private suspend fun executeSelect(statement: SelectStatement, env: Environment) {
        val operations = statement.cases.mapIndexedNotNull { caseIndex, clause ->
            when (val communication = clause.communication) {
                null -> null
                is SendStatement -> {
                    val channel = evaluate(communication.channel, env) as? GoChannel ?: throw RuntimeGoError("select send on non-channel")
                    SelectSend(caseIndex, channel, evaluate(communication.value, env))
                }
                is ExpressionStatement -> {
                    val receive = communication.expression as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("invalid select receive clause")
                    val channel = evaluate(receive.operand, env) as? GoChannel ?: throw RuntimeGoError("select receive from non-channel")
                    SelectReceive(caseIndex, channel, null)
                }
                is AssignmentStatement -> {
                    val receive = communication.values.singleOrNull() as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("select assignment must receive from a channel")
                    val channel = evaluate(receive.operand, env) as? GoChannel ?: throw RuntimeGoError("select receive from non-channel")
                    SelectReceive(caseIndex, channel, communication)
                }
                else -> throw RuntimeGoError("invalid select communication clause")
            }
        }
        val defaultIndex = statement.cases.indexOfFirst { it.communication == null }
        for (operation in operations.shuffled()) {
            when (operation) {
                is SelectSend -> if (operation.channel.trySend(operation.value)) {
                    executeSelectedCase(statement.cases[operation.caseIndex], env)
                    return
                }
                is SelectReceive -> operation.channel.tryReceive()?.let { received ->
                    operation.assignment?.let { assignValues(it.targets, it.operator, expandValues(listOf(received), it.targets.size), env) }
                    executeSelectedCase(statement.cases[operation.caseIndex], env)
                    return
                }
            }
        }
        if (defaultIndex >= 0) {
            executeSelectedCase(statement.cases[defaultIndex], env)
            return
        }
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
        if (receive?.assignment != null) {
            assignValues(receive.assignment.targets, receive.assignment.operator,
                expandValues(listOf(selected.received), receive.assignment.targets.size), env)
        }
        executeSelectedCase(clause, env)
    }

    private suspend fun executeSelectedCase(clause: SelectCase, env: Environment) {
        try { for (statement in clause.statements) execute(statement, env) }
        catch (_: BreakSignal) { }
    }

    private suspend fun executeSwitch(statement: SwitchStatement, env: Environment) {
        val scope = env.child()
        statement.init?.let { execute(it, scope) }
        val tag = statement.tag?.let { evaluate(it, scope) } ?: true
        var selected = -1
        for ((clauseIndex, clause) in statement.clauses.withIndex()) {
            if (clause.expressions?.any { evaluate(it, scope) == tag } == true) {
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
            } catch (_: BreakSignal) {
                return
            }
        }
    }

    private suspend fun executeRange(range: RangeClause, body: BlockStatement, env: Environment) {
        val value = evaluate(range.expression, env)
        when (value) {
            is GoChannel -> while (true) {
                val received = value.receive()
                if (!received.ok) break
                if (range.targets.isNotEmpty()) {
                    val values = listOf(received.value).take(range.targets.size)
                    assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, env)
                }
                try { executeBlock(body, env) }
                catch (_: ContinueSignal) { }
                catch (_: BreakSignal) { break }
            }
            is String -> {
                var byteIndex = 0L
                var charIndex = 0
                while (charIndex < value.length) {
                    val cp = value.codePointAt(charIndex)
                    if (range.targets.isNotEmpty()) {
                        val values = listOf(byteIndex, cp.toLong()).take(range.targets.size)
                        assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, env)
                    }
                    try { executeBlock(body, env) }
                    catch (_: ContinueSignal) { }
                    catch (_: BreakSignal) { break }
                    byteIndex += when { cp <= 0x7f -> 1; cp <= 0x7ff -> 2; cp <= 0xffff -> 3; else -> 4 }
                    charIndex += Character.charCount(cp)
                }
            }
            is GoSlice -> rangeIndexed(value.length, range, body, env) { i -> listOf(i.toLong(), value.get(i)) }
            is GoArray -> rangeIndexed(value.values.size, range, body, env) { i -> listOf(i.toLong(), value.values[i]) }
            is GoMap -> {
                for ((key, entryValue) in value.values.entries.toList()) {
                    if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN,
                        listOf(key, entryValue).take(range.targets.size), env)
                    try { executeBlock(body, env) }
                    catch (_: ContinueSignal) { }
                    catch (_: BreakSignal) { break }
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
        values: (Int) -> List<Any?>
    ) {
        for (i in 0 until length) {
            if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values(i).take(range.targets.size), env)
            try { executeBlock(body, env) }
            catch (_: ContinueSignal) { }
            catch (_: BreakSignal) { break }
        }
    }

    private suspend fun initialize(names: List<String>, expressions: List<Expression>, env: Environment, type: GoTypeSyntax? = null) {
        val values = expandValues(evaluateRhs(expressions, names.size, env), names.size)
        if (values.isNotEmpty() && values.size != names.size) throw RuntimeGoError("initializer count mismatch")
        names.forEachIndexed { i, name ->
            val value = if (values.isNotEmpty()) values[i].let { if (type != null) convert(type, it) else it }
            else if (type != null) zeroValue(type) else 0L
            env.define(name, value)
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
        declaration.names.zip(values).forEach { (name, value) -> target.define(name, value) }
    }

    private suspend fun evaluateRhs(expressions: List<Expression>, arity: Int, env: Environment): List<Any?> {
        if (expressions.size == 1 && arity == 2 && expressions[0] is IndexExpression) {
            val index = expressions[0] as IndexExpression
            val receiver = evaluate(index.receiver, env)
            val key = evaluate(index.index, env)
            if (receiver is GoMap) {
                val found = receiver.values.containsKey(key)
                return listOf(MapLookupResult(if (found) receiver.values[key] else receiver.elementZero, found))
            }
        }
        return expressions.map { evaluate(it, env) }
    }

    private suspend fun evaluate(expression: Expression, env: Environment): Any? = when (expression) {
        is NameExpression -> when (expression.name) {
            "true" -> true
            "false" -> false
            "nil" -> null
            "make", "new", "close", "len", "cap", "append", "copy", "delete", "print", "println", "panic" -> BuiltinValue(expression.name)
            in builtinTypes -> TypeValue(NamedGoType(expression.name))
            in typeDefinitions -> TypeValue(NamedGoType(expression.name))
            else -> env.lookup(expression.name)?.value ?: if (env.contains(expression.name)) null else functions[expression.name]
                ?.let { FunctionValue(it, globals) } ?: throw RuntimeGoError("undefined: ${expression.name}")
        }
        is LiteralExpression -> literal(expression.token)
        is ParenthesizedExpression -> evaluate(expression.expression, env)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.AND -> addressOf(expression.operand, env)
            TokenKind.MUL -> (evaluate(expression.operand, env) as? GoPointer)?.get()
                ?: throw RuntimeGoError("dereference of non-pointer or nil")
            else -> unary(expression.operator, evaluate(expression.operand, env))
        }
        is BinaryExpression -> {
            val left = evaluate(expression.left, env)
            if (expression.operator == TokenKind.LAND && left == false) false
            else if (expression.operator == TokenKind.LOR && left == true) true
            else binary(left, expression.operator, evaluate(expression.right, env))
        }
        is SelectorExpression -> {
            if (expression.receiver is NameExpression && expression.receiver.name in fmtAliases) BuiltinValue(expression.field)
            else {
                val receiver = evaluate(expression.receiver, env)
                val struct = dereference(receiver) as? GoStruct ?: throw RuntimeGoError("selector is not defined for this value")
                if (struct.fields.containsKey(expression.field)) struct.fields[expression.field]
                else {
                    val method = methods["${struct.namedType}.${expression.field}"]
                        ?: throw RuntimeGoError("unknown struct field or method: ${expression.field}")
                    val pointerReceiver = method.receiver?.type is PointerGoType
                    val boundReceiver = when {
                        pointerReceiver && receiver is GoPointer -> receiver
                        pointerReceiver -> GoPointer.cell(receiver)
                        receiver is GoPointer -> copyValue(dereference(receiver))
                        else -> copyValue(receiver)
                    }
                    MethodValue(method, boundReceiver)
                }
            }
        }
        is CallExpression -> call(expression, env)
        is IndexExpression -> index(evaluate(expression.receiver, env), evaluate(expression.index, env))
        is SliceExpression -> slice(evaluate(expression.receiver, env), expression.low?.let { evaluate(it, env) },
            expression.high?.let { evaluate(it, env) }, expression.max?.let { evaluate(it, env) })
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
                else -> throw RuntimeGoError("address-of index requires an array or slice element")
            }
        }
        is UnaryExpression -> if (expression.operator == TokenKind.MUL) {
            evaluate(expression.operand, env) as? GoPointer ?: throw RuntimeGoError("cannot take address through a non-pointer")
        } else throw RuntimeGoError("expression is not addressable")
        is CompositeLiteral -> GoPointer.cell(composite(expression, env))
        else -> throw RuntimeGoError("expression is not addressable")
    }

    private suspend fun call(call: CallExpression, env: Environment): Any? {
        val target = evaluate(call.function, env)
        val args = call.arguments.map { evaluate(it, env) }
        return call(target, args, call.expandLastArgument)
    }

    private suspend fun call(target: Any?, args: List<Any?>, expandLastArgument: Boolean = false): Any? {
        val effectiveArgs = if (expandLastArgument) {
            val last = args.lastOrNull()
            args.dropLast(1) + when (last) {
                is GoSlice -> last.toList()
                null -> emptyList()
                else -> throw RuntimeGoError("... argument must be a slice")
            }
        } else args
        when (target) {
            is FunctionValue -> {
                val values = invoke(target.function, args, parent = target.closure, expandedVariadic = expandLastArgument)
                return if (values.isEmpty()) null else if (values.size == 1) values.single() else GoMultiValue(values)
            }
            is MethodValue -> {
                val values = invoke(target.function, args, target.receiver, expandedVariadic = expandLastArgument)
                return if (values.isEmpty()) null else if (values.size == 1) values.single() else GoMultiValue(values)
            }
            is BuiltinValue -> when (target.name) {
                "print", "println" -> {
                    output(effectiveArgs.joinToString(if (target.name == "println") " " else "") { stringify(it) } + if (target.name == "println") "\n" else "")
                    return null
                }
                "panic" -> throw RuntimeGoError(args.firstOrNull()?.toString() ?: "panic")
                "make" -> return make(args)
                "new" -> {
                    val type = (args.singleOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("new requires a type")
                    return GoPointer.cell(zeroValue(type))
                }
                "close" -> { (args.singleOrNull() as? GoChannel)?.close() ?: throw RuntimeGoError("close of non-channel"); return null }
                "len" -> return when (val value = args.singleOrNull()) {
                    is String -> value.toByteArray(Charsets.UTF_8).size.toLong()
                    is GoSlice -> value.length.toLong()
                    is GoArray -> value.values.size.toLong()
                    is GoMap -> value.values.size.toLong()
                    is GoChannel -> value.len()
                    else -> throw RuntimeGoError("len is not defined for this value")
                }
                "cap" -> return when (val value = args.singleOrNull()) {
                    is GoChannel -> value.capacity.toLong()
                    is GoSlice -> value.capacity.toLong()
                    is GoArray -> value.values.size.toLong()
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
                    backing[at] = evaluate(element.value, env)
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
                    values[at] = evaluate(element.value, env)
                }
                GoArray(type.element, values)
            }
            is MapGoType -> {
                val values = linkedMapOf<Any?, Any?>()
                literal.elements.forEach { element ->
                    val key = element.key?.let { evaluate(it, env) } ?: throw RuntimeGoError("map literal element requires a key")
                    values[key] = evaluate(element.value, env)
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
                    fields[name] = evaluate(element.value, env)
                }
                GoStruct(fields, (literal.type as? NamedGoType)?.name)
            }
            else -> throw RuntimeGoError("composite literal for this type is not implemented")
        }
    }

    private fun underlying(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        is NamedGoType -> typeDefinitions[type.name]?.let(::underlying) ?: type
        else -> type
    }

    private fun methodKey(type: GoTypeSyntax, name: String): String {
        val base = if (type is PointerGoType) type.element else type
        return "${(base as? NamedGoType)?.name ?: base}.$name"
    }

    private fun dereference(value: Any?): Any? = if (value is GoPointer) value.get() else value

    private fun copyValue(value: Any?): Any? = when (value) {
        is GoStruct -> GoStruct(value.fields.toMutableMap(), value.namedType)
        is GoArray -> GoArray(value.elementType, value.values.toMutableList())
        else -> value
    }

    private fun index(receiver: Any?, rawIndex: Any?): Any? {
        return when (receiver) {
            is GoSlice -> receiver.get(number(rawIndex, "index").toInt())
            is GoArray -> receiver.values.getOrNull(number(rawIndex, "index").toInt()) ?: throw RuntimeGoError("array index out of range")
            is GoMap -> if (receiver.values.containsKey(rawIndex)) receiver.values[rawIndex] else receiver.elementZero
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
                GoSlice(receiver.elementType, receiver.values, low, high - low, max - low)
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
        is NamedGoType -> when (target.name) {
            "string" -> when (value) { is String -> value; is Long -> String(Character.toChars(value.toInt())); else -> throw RuntimeGoError("cannot convert to string") }
            "bool" -> value as? Boolean ?: throw RuntimeGoError("cannot convert to bool")
            "float32", "float64" -> real(value)
            "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune" -> when (value) { is Long -> value; is Double -> value.toLong(); else -> throw RuntimeGoError("cannot convert to integer") }
            else -> value
        }
        else -> value
    }

    private fun append(args: List<Any?>): GoSlice {
        val slice = args.firstOrNull() as? GoSlice ?: throw RuntimeGoError("append requires a slice")
        return slice.append(args.drop(1))
    }

    private fun copy(args: List<Any?>): Long {
        val destination = args.getOrNull(0) as? GoSlice ?: throw RuntimeGoError("copy destination must be a slice")
        val values = when (val source = args.getOrNull(1)) {
            is GoSlice -> source.toList()
            is GoArray -> source.values.toList()
            is String -> source.toByteArray(Charsets.UTF_8).map { (it.toInt() and 0xff).toLong() }
            else -> throw RuntimeGoError("copy source must be a slice or string")
        }
        val count = minOf(destination.length, values.size)
        repeat(count) { destination.set(it, values[it]) }
        return count.toLong()
    }

    private fun delete(args: List<Any?>) {
        val map = args.getOrNull(0) as? GoMap ?: throw RuntimeGoError("delete requires a map")
        map.values.remove(args.getOrNull(1))
    }

    private fun literal(token: Token): Any = when (token.kind) {
        TokenKind.INT -> integer(token.lexeme)
        TokenKind.FLOAT -> token.lexeme.toDoubleOrNull() ?: throw RuntimeGoError("invalid float ${token.lexeme}")
        TokenKind.IMAG -> token.lexeme.removeSuffix("i").toDoubleOrNull() ?: throw RuntimeGoError("invalid imaginary literal")
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
        TokenKind.SUB -> when (value) { is Long -> -value; is Double -> -value; else -> typeError("unary -", value) }
        TokenKind.NOT -> !(value as? Boolean ?: typeError("!", value))
        TokenKind.XOR -> number(value, "^").inv()
        TokenKind.AND -> throw RuntimeGoError("pointers are not implemented")
        TokenKind.MUL -> throw RuntimeGoError("pointer dereference is not implemented")
        TokenKind.ARROW -> (value as? GoChannel)?.receive() ?: throw RuntimeGoError("receive from non-channel")
        else -> value
    }

    private fun make(args: List<Any?>): Any? {
        val type = underlying((args.firstOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("make requires a type"))
        return when (type) {
            is ChannelGoType -> {
                val capacity = args.getOrNull(1)?.let { number(it, "channel capacity").toInt() } ?: 0
                if (capacity < 0) throw RuntimeGoError("negative channel capacity")
                GoChannel(zeroValue(type.element), capacity)
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
            "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune" -> 0L
            "float32", "float64" -> 0.0
            "complex64", "complex128" -> 0.0
            else -> null
        }
        is ArrayGoType -> {
            val length = runCatching { integerLiteral(actual.length) }.getOrDefault(0L).toInt().coerceAtLeast(0)
            GoArray(actual.element, MutableList(length) { zeroValue(actual.element) })
        }
        is StructGoType -> {
            val fields = linkedMapOf<String, Any?>()
            actual.fields.forEach { field ->
                val names = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                names.filter { it.isNotEmpty() }.forEach { fields[it] = zeroValue(field.type) }
            }
            GoStruct(fields, (type as? NamedGoType)?.name)
        }
        else -> null
    }

    private fun embeddedFieldName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is PointerGoType -> embeddedFieldName(type.element)
        else -> ""
    }

    private fun integerLiteral(expression: Expression): Long = when (expression) {
        is LiteralExpression -> integer(expression.token.lexeme)
        else -> 0L
    }

    private fun binary(left: Any?, op: TokenKind, right: Any?): Any? {
        if (op == TokenKind.EQL || op == TokenKind.NEQ) return if (op == TokenKind.EQL) left == right else left != right
        if (op == TokenKind.LAND || op == TokenKind.LOR) {
            val a = left as? Boolean ?: typeError("logical operator", left)
            val b = right as? Boolean ?: typeError("logical operator", right)
            return if (op == TokenKind.LAND) a && b else a || b
        }
        if ((left is String) && (right is String) && op == TokenKind.ADD) return left + right
        if (left is Double || right is Double) {
            val a = real(left); val b = real(right)
            return when (op) {
                TokenKind.ADD -> a + b; TokenKind.SUB -> a - b; TokenKind.MUL -> a * b; TokenKind.QUO -> a / b
                TokenKind.LSS -> a < b; TokenKind.LEQ -> a <= b; TokenKind.GTR -> a > b; TokenKind.GEQ -> a >= b
                else -> throw RuntimeGoError("invalid floating-point operator $op")
            }
        }
        val a = number(left, op.name); val b = number(right, op.name)
        return when (op) {
            TokenKind.ADD -> a + b; TokenKind.SUB -> a - b; TokenKind.MUL -> a * b
            TokenKind.QUO -> if (b == 0L) throw RuntimeGoError("integer divide by zero") else a / b
            TokenKind.REM -> if (b == 0L) throw RuntimeGoError("integer divide by zero") else a % b
            TokenKind.AND -> a and b; TokenKind.OR -> a or b; TokenKind.XOR -> a xor b
            TokenKind.AND_NOT -> a and b.inv(); TokenKind.SHL -> a shl b.toInt(); TokenKind.SHR -> a shr b.toInt()
            TokenKind.LSS -> a < b; TokenKind.LEQ -> a <= b; TokenKind.GTR -> a > b; TokenKind.GEQ -> a >= b
            else -> throw RuntimeGoError("invalid operator $op")
        }
    }

    private fun number(value: Any?, op: String): Long = value as? Long ?: typeError(op, value)
    private fun real(value: Any?): Double = when (value) { is Long -> value.toDouble(); is Double -> value; else -> typeError("arithmetic", value) }
    private fun truth(value: Any?) = value as? Boolean ?: typeError("condition", value)
    private fun stringify(value: Any?): String = when (value) {
        null -> "<nil>"
        is GoPointer -> "&${stringify(value.get())}"
        is FunctionValue -> "<function ${value.function.name}>"
        is GoSlice -> value.toList().joinToString(prefix = "[", postfix = "]") { stringify(it) }
        is GoArray -> value.values.joinToString(prefix = "[", postfix = "]") { stringify(it) }
        is GoMap -> value.values.entries.joinToString(prefix = "map[", postfix = "]") { "${stringify(it.key)}:${stringify(it.value)}" }
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

    private class Environment(
        private val parent: Environment? = null,
        private val deferredCalls: MutableList<suspend () -> Unit> = mutableListOf()
    ) {
        private val values = mutableMapOf<String, Any?>()
        private val addresses = mutableMapOf<String, GoPointer>()
        fun child() = Environment(this, deferredCalls)
        fun define(name: String, value: Any?) { values[name] = value }
        fun get(name: String): Any? = lookup(name)?.value ?: if (contains(name)) null else throw RuntimeGoError("undefined: $name")
        fun lookup(name: String): Lookup? = if (values.containsKey(name)) Lookup(values[name]) else parent?.lookup(name)
        fun getOrNull(name: String): Any? = lookup(name)?.value
        fun contains(name: String): Boolean = values.containsKey(name) || parent?.contains(name) == true
        fun pointer(name: String): GoPointer {
            val owner = owner(name) ?: throw RuntimeGoError("undefined: $name")
            return owner.addresses.getOrPut(name) { GoPointer.reference({ owner.get(name) }, { owner.set(name, it) }) }
        }
        private fun owner(name: String): Environment? = if (values.containsKey(name)) this else parent?.owner(name)
        fun defer(action: suspend () -> Unit) { deferredCalls += action }
        suspend fun runDefers() {
            for (action in deferredCalls.asReversed()) action()
            deferredCalls.clear()
        }
        fun set(name: String, value: Any?) {
            if (values.containsKey(name)) values[name] = value
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
    private data class SelectSelection(val caseIndex: Int, val received: GoReceiveResult?)
    private sealed interface SelectOperation { val caseIndex: Int }
    private data class SelectSend(override val caseIndex: Int, val channel: GoChannel, val value: Any?) : SelectOperation
    private data class SelectReceive(override val caseIndex: Int, val channel: GoChannel, val assignment: AssignmentStatement?) : SelectOperation
    private class GoArray(val elementType: GoTypeSyntax, val values: MutableList<Any?>) {
        private val addresses = mutableMapOf<Int, GoPointer>()
        fun pointerAt(index: Int): GoPointer {
            if (index !in values.indices) throw RuntimeGoError("array index out of range")
            return addresses.getOrPut(index) { GoPointer.reference({ values[index] }, { values[index] = it }) }
        }
    }
    private inner class GoSlice(val elementType: GoTypeSyntax, private val backing: MutableList<Any?>, private val start: Int, val length: Int, val capacity: Int) {
        private val addresses = mutableMapOf<Int, GoPointer>()
        fun get(index: Int): Any? {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            return backing[start + index]
        }
        fun set(index: Int, value: Any?) {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            backing[start + index] = value
        }
        fun pointerAt(index: Int): GoPointer {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            val absolute = start + index
            return addresses.getOrPut(index) { GoPointer.reference({ backing[absolute] }, { backing[absolute] = it }) }
        }
        fun subSlice(low: Int, high: Int, max: Int): GoSlice {
            if (low < 0 || high < low || max < high || max > capacity) throw RuntimeGoError("slice bounds out of range")
            return GoSlice(elementType, backing, start + low, high - low, max - low)
        }
        fun append(values: List<Any?>): GoSlice {
            if (length + values.size <= capacity) {
                values.forEachIndexed { i, value -> backing[start + length + i] = value }
                return GoSlice(elementType, backing, start, length + values.size, capacity)
            }
            val newCapacity = maxOf(length + values.size, maxOf(1, capacity * 2))
            val newBacking = MutableList(newCapacity) { zeroValue(elementType) }
            repeat(length) { newBacking[it] = get(it) }
            values.forEachIndexed { i, value -> newBacking[length + i] = value }
            return GoSlice(elementType, newBacking, 0, length + values.size, newCapacity)
        }
        fun toList(): List<Any?> = (0 until length).map(::get)
    }
    private class GoMap(val keyType: GoTypeSyntax, val valueType: GoTypeSyntax, val elementZero: Any?, val values: MutableMap<Any?, Any?>)
    private class GoStruct(val fields: MutableMap<String, Any?>, val namedType: String? = null) {
        private val addresses = mutableMapOf<String, GoPointer>()
        fun pointer(field: String): GoPointer = addresses.getOrPut(field) {
            GoPointer.reference({ fields[field] }, { fields[field] = it })
        }
    }
    private class GoPointer(private val location: GoLocation) {
        fun get(): Any? = location.get()
        fun set(value: Any?) = location.set(value)
        override fun equals(other: Any?) = other is GoPointer && location === other.location
        override fun hashCode() = System.identityHashCode(location)

        companion object {
            fun reference(get: () -> Any?, set: (Any?) -> Unit) = GoPointer(GoLocation(get, set))
            fun cell(value: Any?) = GoCell(value).let { cell -> reference({ cell.value }, { cell.value = it }) }
        }
    }
    private class GoLocation(val get: () -> Any?, val set: (Any?) -> Unit)
    private class GoCell(var value: Any?)
    private class GoChannel(private val elementZero: Any?, val capacity: Int) {
        val queue = Channel<Any?>(capacity)
        private val buffered = AtomicInteger(0)
        suspend fun send(value: Any?) {
            queue.send(value)
            if (capacity > 0) buffered.incrementAndGet()
        }
        suspend fun receive(): GoReceiveResult {
            val result = queue.receiveCatching()
            return decode(result)
        }
        fun trySend(value: Any?): Boolean = queue.trySend(value).isSuccess.also { if (it && capacity > 0) buffered.incrementAndGet() }
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
    private class BreakSignal : RuntimeException(null, null, false, false)
    private class ContinueSignal : RuntimeException(null, null, false, false)
    private class FallthroughSignal : RuntimeException(null, null, false, false)

    companion object {
        private val builtinTypes = setOf("bool", "byte", "complex64", "complex128", "error", "float32", "float64", "int", "int8", "int16", "int32", "int64", "rune", "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr")
    }
}
