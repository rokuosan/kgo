package kgo

import java.math.BigInteger

class RuntimeGoError(message: String) : RuntimeException(message)

/** Runtime for the currently implemented Go 1.0 execution subset. */
class Interpreter(private val output: (String) -> Unit = ::println) {
    private val functions = mutableMapOf<String, FunctionDeclaration>()
    private val globals = Environment()

    fun run(file: GoFile) {
        file.declarations.forEach { declaration ->
            when (declaration) {
                is FunctionDeclaration -> functions[declaration.name] = declaration
                is VariableDeclaration -> initialize(declaration.names, declaration.values, globals)
                is ImportDeclaration -> Unit
            }
        }
        val main = functions["main"] ?: throw RuntimeGoError("main function not found")
        invoke(main, emptyList())
    }

    private fun invoke(function: FunctionDeclaration, arguments: List<Any?>): List<Any?> {
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
        }
    }

    private fun executeBlock(block: BlockStatement, parent: Environment) {
        val env = Environment(parent)
        for (statement in block.statements) execute(statement, env)
    }

    private fun execute(statement: Statement, env: Environment) {
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
                val scope = Environment(env)
                statement.init?.let { execute(it, scope) }
                if (truth(evaluate(statement.condition, scope))) executeBlock(statement.thenBranch, scope)
                else statement.elseBranch?.let { execute(it, scope) }
            }
            is ForStatement -> {
                val scope = Environment(env)
                statement.init?.let { execute(it, scope) }
                while (statement.condition == null || truth(evaluate(statement.condition, scope))) {
                    try { executeBlock(statement.body, scope) }
                    catch (_: ContinueSignal) { }
                    catch (_: BreakSignal) { break }
                    statement.post?.let { execute(it, scope) }
                }
            }
            is SendStatement -> throw RuntimeGoError("channel send requires channel runtime support")
        }
    }

    private fun assign(statement: AssignmentStatement, env: Environment) {
        val values = statement.values.map { evaluate(it, env) }
        if (statement.operator == TokenKind.DEFINE) {
            val names = statement.targets.map { (it as? NameExpression)?.name ?: throw RuntimeGoError("short declaration targets must be names") }
            if (names.size != values.size) throw RuntimeGoError("assignment count mismatch")
            names.zip(values).forEach { (name, value) -> env.define(name, value) }
            return
        }
        if (statement.targets.size != values.size) throw RuntimeGoError("assignment count mismatch")
        statement.targets.zip(values).forEach { (target, value) ->
            val name = (target as? NameExpression)?.name ?: throw RuntimeGoError("assignment target must be a variable")
            val result = if (statement.operator == TokenKind.ASSIGN) value else {
                val left = env.get(name)
                binary(left, compoundOperator(statement.operator), value)
            }
            env.set(name, result)
        }
    }

    private fun initialize(names: List<String>, expressions: List<Expression>, env: Environment) {
        val values = expressions.map { evaluate(it, env) }
        if (values.isNotEmpty() && values.size != names.size) throw RuntimeGoError("initializer count mismatch")
        names.forEachIndexed { i, name -> env.define(name, values.getOrNull(i) ?: 0L) }
    }

    private fun evaluate(expression: Expression, env: Environment): Any? = when (expression) {
        is NameExpression -> when (expression.name) {
            "true" -> true
            "false" -> false
            "nil" -> null
            else -> env.getOrNull(expression.name) ?: if (functions.containsKey(expression.name)) FunctionValue(expression.name) else throw RuntimeGoError("undefined: ${expression.name}")
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
    }

    private fun call(call: CallExpression, env: Environment): Any? {
        val args = call.arguments.map { evaluate(it, env) }
        val fn = call.function
        if (fn is NameExpression) {
            when (fn.name) {
                "print", "println" -> { output(args.joinToString(if (fn.name == "println") " " else "") { stringify(it) } + if (fn.name == "println") "\n" else ""); return null }
                "panic" -> throw RuntimeGoError(args.firstOrNull()?.toString() ?: "panic")
                else -> functions[fn.name]?.let { return invoke(it, args) }
            }
        }
        if (fn is SelectorExpression && fn.receiver is NameExpression && fn.receiver.name == "fmt") {
            when (fn.field) {
                "Print", "Fprint" -> { output(args.drop(if (fn.field == "Fprint") 1 else 0).joinToString("") { stringify(it) }); return null }
                "Println", "Fprintln" -> { output(args.drop(if (fn.field == "Fprintln") 1 else 0).joinToString(" ") { stringify(it) } + "\n"); return null }
            }
        }
        val value = evaluate(fn, env)
        if (value is FunctionValue) return invoke(functions.getValue(value.name), args)
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

    private fun unary(operator: TokenKind, value: Any?): Any? = when (operator) {
        TokenKind.ADD -> value
        TokenKind.SUB -> when (value) { is Long -> -value; is Double -> -value; else -> typeError("unary -", value) }
        TokenKind.NOT -> !(value as? Boolean ?: typeError("!", value))
        TokenKind.XOR -> number(value, "^").inv()
        TokenKind.AND -> throw RuntimeGoError("pointers are not implemented")
        TokenKind.MUL -> throw RuntimeGoError("pointer dereference is not implemented")
        TokenKind.ARROW -> throw RuntimeGoError("channel receive requires channel runtime support")
        else -> value
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

    private class Environment(private val parent: Environment? = null) {
        private val values = mutableMapOf<String, Any?>()
        fun define(name: String, value: Any?) { values[name] = value }
        fun get(name: String): Any? = getOrNull(name) ?: throw RuntimeGoError("undefined: $name")
        fun getOrNull(name: String): Any? = if (values.containsKey(name)) values[name] else parent?.getOrNull(name)
        fun set(name: String, value: Any?) {
            if (values.containsKey(name)) values[name] = value
            else if (parent != null && parent.contains(name)) parent.set(name, value)
            else throw RuntimeGoError("undefined: $name")
        }
        private fun contains(name: String): Boolean = values.containsKey(name) || parent?.contains(name) == true
    }

    private data class FunctionValue(val name: String)
    private data class BuiltinValue(val name: String)
    private class ReturnSignal(val values: List<Any?>) : RuntimeException(null, null, false, false)
    private class BreakSignal : RuntimeException(null, null, false, false)
    private class ContinueSignal : RuntimeException(null, null, false, false)
}
