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
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val globals = Environment()
    private val typeDefinitions = mutableMapOf<String, GoTypeSyntax>()
    private lateinit var goroutines: CoroutineScope

    fun run(file: GoFile) {
        runBlocking {
            goroutines = CoroutineScope(SupervisorJob() + Dispatchers.Default)
            try {
                file.declarations.filterIsInstance<FunctionDeclaration>().forEach { function ->
                    if (function.name == "init") initFunctions += function else functions[function.name] = function
                }
                file.declarations.filterIsInstance<TypeDeclaration>().forEach { typeDefinitions[it.name] = it.type }
                file.declarations.forEach { declaration ->
                    when (declaration) {
                        is FunctionDeclaration, is TypeDeclaration -> Unit
                        is VariableDeclaration -> initialize(declaration.names, declaration.values, globals)
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

    private suspend fun invoke(function: FunctionDeclaration, arguments: List<Any?>): List<Any?> {
        if (function.parameters.size != arguments.size) {
            throw RuntimeGoError("${function.name} expects ${function.parameters.size} arguments, got ${arguments.size}")
        }
        val env = Environment(globals)
        function.parameters.zip(arguments).forEach { (name, value) -> env.define(name, value) }
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
            is BlockStatement -> executeBlock(statement, env)
            is VariableStatement -> initialize(statement.names, statement.values, env)
            is ReturnStatement -> throw ReturnSignal(statement.values.map { evaluate(it, env) })
            is ExpressionStatement -> evaluate(statement.expression, env)
            is AssignmentStatement -> assign(statement, env)
            is IncrementStatement -> {
                val name = (statement.target as? NameExpression)?.name ?: throw RuntimeGoError("increment target must be a variable")
                val old = number(env.get(name), name)
                env.set(name, old + statement.delta)
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
                goroutines.launch { call(target, arguments) }
            }
            is DeferStatement -> {
                val call = statement.call as? CallExpression ?: throw RuntimeGoError("defer statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = call.arguments.map { evaluate(it, env) }
                env.defer { call(target, arguments) }
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
        val values = expandValues(statement.values.map { evaluate(it, env) }, statement.targets.size)
        assignValues(statement.targets, statement.operator, values, env)
    }

    private fun assignValues(targets: List<Expression>, operator: TokenKind, values: List<Any?>, env: Environment) {
        if (operator == TokenKind.DEFINE) {
            val names = targets.map { (it as? NameExpression)?.name ?: throw RuntimeGoError("short declaration targets must be names") }
            if (names.size != values.size) throw RuntimeGoError("assignment count mismatch")
            names.zip(values).forEach { (name, value) -> env.define(name, value) }
            return
        }
        if (targets.size != values.size) throw RuntimeGoError("assignment count mismatch")
        targets.zip(values).forEach { (target, value) ->
            val name = (target as? NameExpression)?.name ?: throw RuntimeGoError("assignment target must be a variable")
            val result = if (operator == TokenKind.ASSIGN) value else {
                val left = env.get(name)
                binary(left, compoundOperator(operator), value)
            }
            env.set(name, result)
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
            else -> throw RuntimeGoError("range over this value is not implemented")
        }
    }

    private suspend fun initialize(names: List<String>, expressions: List<Expression>, env: Environment) {
        val values = expandValues(expressions.map { evaluate(it, env) }, names.size)
        if (values.isNotEmpty() && values.size != names.size) throw RuntimeGoError("initializer count mismatch")
        names.forEachIndexed { i, name -> env.define(name, values.getOrNull(i) ?: 0L) }
    }

    private suspend fun initializeConstant(declaration: ConstantDeclaration) {
        val scope = globals.child()
        scope.define("iota", declaration.iotaIndex.toLong())
        val values = expandValues(declaration.values.map { evaluate(it, scope) }, declaration.names.size)
        if (values.size != declaration.names.size) throw RuntimeGoError("constant initializer count mismatch")
        declaration.names.zip(values).forEach { (name, value) -> globals.define(name, value) }
    }

    private suspend fun evaluate(expression: Expression, env: Environment): Any? = when (expression) {
        is NameExpression -> when (expression.name) {
            "true" -> true
            "false" -> false
            "nil" -> null
            "make", "new", "close", "len", "cap", "print", "println", "panic" -> BuiltinValue(expression.name)
            else -> env.lookup(expression.name)?.value ?: if (env.contains(expression.name)) null else if (functions.containsKey(expression.name)) FunctionValue(expression.name) else throw RuntimeGoError("undefined: ${expression.name}")
        }
        is LiteralExpression -> literal(expression.token)
        is ParenthesizedExpression -> evaluate(expression.expression, env)
        is UnaryExpression -> unary(expression.operator, evaluate(expression.operand, env))
        is BinaryExpression -> {
            val left = evaluate(expression.left, env)
            if (expression.operator == TokenKind.LAND && left == false) false
            else if (expression.operator == TokenKind.LOR && left == true) true
            else binary(left, expression.operator, evaluate(expression.right, env))
        }
        is SelectorExpression -> {
            if (expression.receiver is NameExpression && expression.receiver.name == "fmt") BuiltinValue(expression.field)
            else throw RuntimeGoError("selector expressions are not implemented")
        }
        is CallExpression -> call(expression, env)
        is IndexExpression -> throw RuntimeGoError("index expressions are not implemented")
        is TypeExpression -> TypeValue(expression.type)
    }

    private suspend fun call(call: CallExpression, env: Environment): Any? {
        val target = evaluate(call.function, env)
        val args = call.arguments.map { evaluate(it, env) }
        return call(target, args)
    }

    private suspend fun call(target: Any?, args: List<Any?>): Any? {
        when (target) {
            is FunctionValue -> {
                val values = invoke(functions[target.name] ?: throw RuntimeGoError("undefined function ${target.name}"), args)
                return if (values.isEmpty()) null else if (values.size == 1) values.single() else GoMultiValue(values)
            }
            is BuiltinValue -> when (target.name) {
                "print", "println" -> {
                    output(args.joinToString(if (target.name == "println") " " else "") { stringify(it) } + if (target.name == "println") "\n" else "")
                    return null
                }
                "panic" -> throw RuntimeGoError(args.firstOrNull()?.toString() ?: "panic")
                "make" -> return make(args)
                "new" -> return null
                "close" -> { (args.singleOrNull() as? GoChannel)?.close() ?: throw RuntimeGoError("close of non-channel"); return null }
                "len" -> return when (val value = args.singleOrNull()) {
                    is String -> value.codePointCount(0, value.length).toLong()
                    is GoChannel -> value.len()
                    else -> throw RuntimeGoError("len is not defined for this value")
                }
                "cap" -> return when (val value = args.singleOrNull()) {
                    is GoChannel -> value.capacity.toLong()
                    else -> throw RuntimeGoError("cap is not defined for this value")
                }
                "Print", "Fprint" -> {
                    output(args.drop(if (target.name == "Fprint") 1 else 0).joinToString("") { stringify(it) })
                    return null
                }
                "Println", "Fprintln" -> {
                    output(args.drop(if (target.name == "Fprintln") 1 else 0).joinToString(" ") { stringify(it) } + "\n")
                    return null
                }
            }
        }
        throw RuntimeGoError("cannot call value")
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
        val type = (args.firstOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("make requires a type")
        return when (type) {
            is ChannelGoType -> {
                val capacity = args.getOrNull(1)?.let { number(it, "channel capacity").toInt() } ?: 0
                if (capacity < 0) throw RuntimeGoError("negative channel capacity")
                GoChannel(zeroValue(type.element), capacity)
            }
            else -> throw RuntimeGoError("make for this type is not implemented")
        }
    }

    private fun expandValues(values: List<Any?>, targets: Int): List<Any?> {
        if (values.size == 1) {
            val only = values.single()
            if (only is GoReceiveResult && targets == 2) return listOf(only.value, only.ok)
            if (only is GoReceiveResult) return listOf(only.value)
            if (only is GoMultiValue) return only.values
            return listOf(only)
        }
        return values.map { if (it is GoReceiveResult) it.value else it }
    }

    private fun zeroValue(type: GoTypeSyntax): Any? = when (type) {
        is NamedGoType -> when (type.name) {
            "bool" -> false
            "string" -> ""
            "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune" -> 0L
            "float32", "float64" -> 0.0
            "complex64", "complex128" -> 0.0
            else -> null
        }
        else -> null
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
    private fun stringify(value: Any?): String = when (value) { null -> "<nil>"; is FunctionValue -> "<function ${value.name}>"; else -> value.toString() }
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
        fun child() = Environment(this, deferredCalls)
        fun define(name: String, value: Any?) { values[name] = value }
        fun get(name: String): Any? = lookup(name)?.value ?: if (contains(name)) null else throw RuntimeGoError("undefined: $name")
        fun lookup(name: String): Lookup? = if (values.containsKey(name)) Lookup(values[name]) else parent?.lookup(name)
        fun getOrNull(name: String): Any? = lookup(name)?.value
        fun contains(name: String): Boolean = values.containsKey(name) || parent?.contains(name) == true
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
    private data class FunctionValue(val name: String)
    private data class BuiltinValue(val name: String)
    private data class TypeValue(val type: GoTypeSyntax)
    private data class GoMultiValue(val values: List<Any?>)
    private data class GoReceiveResult(val value: Any?, val ok: Boolean)
    private data class SelectSelection(val caseIndex: Int, val received: GoReceiveResult?)
    private sealed interface SelectOperation { val caseIndex: Int }
    private data class SelectSend(override val caseIndex: Int, val channel: GoChannel, val value: Any?) : SelectOperation
    private data class SelectReceive(override val caseIndex: Int, val channel: GoChannel, val assignment: AssignmentStatement?) : SelectOperation
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
}
