package kgo

class ParseError(message: String, val position: Position) : RuntimeException(
    "${position.line}:${position.column}: $message"
)

/** Recursive-descent parser for the executable Go 1.0 core. */
class Parser(private val tokens: List<Token>) {
    private var index = 0

    fun parseFile(): GoFile {
        expect(TokenKind.PACKAGE)
        val packageName = expect(TokenKind.IDENT).lexeme
        semicolon()
        val declarations = mutableListOf<Declaration>()
        while (!at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            when {
                match(TokenKind.IMPORT) -> declarations += parseImport()
                match(TokenKind.FUNC) -> declarations += parseFunction()
                match(TokenKind.VAR) -> declarations += parseVariables()
                else -> fail("expected top-level declaration")
            }
        }
        return GoFile(packageName, declarations)
    }

    private fun parseImport(): ImportDeclaration {
        val paths = mutableListOf<String>()
        if (match(TokenKind.LPAREN)) {
            while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
                if (match(TokenKind.SEMICOLON)) continue
                if (at(TokenKind.IDENT)) take() // optional import name
                paths += expect(TokenKind.STRING).lexeme
                semicolon()
            }
            expect(TokenKind.RPAREN); optionalSemicolon()
        } else {
            if (at(TokenKind.IDENT)) take()
            paths += expect(TokenKind.STRING).lexeme
            semicolon()
        }
        return ImportDeclaration(paths)
    }

    private fun parseFunction(): FunctionDeclaration {
        val name = expect(TokenKind.IDENT).lexeme
        expect(TokenKind.LPAREN)
        val parameters = mutableListOf<String>()
        if (!at(TokenKind.RPAREN)) {
            do {
                parameters += expect(TokenKind.IDENT).lexeme
                // Type syntax is consumed here; type checking is a later front-end layer.
                if (at(TokenKind.IDENT)) take()
                while (match(TokenKind.LBRACK)) { expect(TokenKind.RBRACK); if (at(TokenKind.IDENT)) take() }
            } while (match(TokenKind.COMMA) && !at(TokenKind.RPAREN))
        }
        expect(TokenKind.RPAREN)
        // Go function result types are accepted syntactically and ignored by this first AST layer.
        if (at(TokenKind.IDENT)) take()
        val body = parseBlock()
        optionalSemicolon()
        return FunctionDeclaration(name, parameters, body)
    }

    private fun parseVariables(): VariableDeclaration {
        val variables = parseVariableSpec()
        return VariableDeclaration(variables.first, variables.second)
    }

    private fun parseVariableStatement(): VariableStatement {
        val variables = parseVariableSpec()
        return VariableStatement(variables.first, variables.second)
    }

    private fun parseVariableSpec(): Pair<List<String>, List<Expression>> {
        val names = mutableListOf(expect(TokenKind.IDENT).lexeme)
        while (match(TokenKind.COMMA)) names += expect(TokenKind.IDENT).lexeme
        if (match(TokenKind.DEFINE) || match(TokenKind.ASSIGN)) {
            return names to expressionList()
        }
        // Optional declared type (the static type system will validate it in a later stage).
        if (at(TokenKind.IDENT)) take() else fail("expected a type or initializer")
        return names to emptyList()
    }

    private fun parseBlock(): BlockStatement {
        expect(TokenKind.LBRACE)
        val statements = mutableListOf<Statement>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) { statements += EmptyStatement; continue }
            statements += parseStatement()
            if (!match(TokenKind.SEMICOLON) && !at(TokenKind.RBRACE)) fail("expected semicolon or '}'")
        }
        expect(TokenKind.RBRACE)
        return BlockStatement(statements)
    }

    private fun parseStatement(): Statement = when {
        at(TokenKind.LBRACE) -> parseBlock()
        match(TokenKind.RETURN) -> ReturnStatement(if (at(TokenKind.SEMICOLON) || at(TokenKind.RBRACE)) emptyList() else expressionList())
        match(TokenKind.VAR) -> parseVariableStatement()
        match(TokenKind.IF) -> parseIf()
        match(TokenKind.FOR) -> parseFor()
        else -> parseSimpleStatement()
    }

    private fun parseIf(): IfStatement {
        val first = parseSimpleStatement()
        val init: Statement?
        val condition: Expression
        if (match(TokenKind.SEMICOLON)) {
            init = first
            condition = expression()
        } else {
            init = null
            condition = asExpression(first)
        }
        val body = parseBlock()
        val elseBranch = if (match(TokenKind.ELSE)) {
            if (match(TokenKind.IF)) parseIf() else parseBlock()
        } else null
        return IfStatement(init, condition, body, elseBranch)
    }

    private fun parseFor(): ForStatement {
        if (at(TokenKind.LBRACE)) return ForStatement(null, null, null, parseBlock())
        if (match(TokenKind.SEMICOLON)) {
            val condition = if (at(TokenKind.SEMICOLON)) null else expression()
            expect(TokenKind.SEMICOLON)
            val post = if (at(TokenKind.LBRACE)) null else parseSimpleStatement()
            return ForStatement(null, condition, post, parseBlock())
        }
        val first = parseSimpleStatement()
        if (match(TokenKind.SEMICOLON)) {
            val condition = if (at(TokenKind.SEMICOLON)) null else expression()
            expect(TokenKind.SEMICOLON)
            val post = if (at(TokenKind.LBRACE)) null else parseSimpleStatement()
            return ForStatement(first, condition, post, parseBlock())
        }
        return ForStatement(null, asExpression(first), null, parseBlock())
    }

    private fun parseSimpleStatement(): Statement {
        val left = expressionList()
        if (match(TokenKind.INC)) return IncrementStatement(left.singleOrFail(), 1)
        if (match(TokenKind.DEC)) return IncrementStatement(left.singleOrFail(), -1)
        if (current().kind in assignmentOperators) {
            val operator = take().kind
            return AssignmentStatement(left, operator, expressionList())
        }
        if (match(TokenKind.ARROW)) return SendStatement(left.singleOrFail(), expression())
        return if (left.size == 1) ExpressionStatement(left.single()) else fail("expression list needs an assignment")
    }

    private fun expressionList(): List<Expression> {
        val expressions = mutableListOf(expression())
        while (match(TokenKind.COMMA)) expressions += expression()
        return expressions
    }

    private fun expression(minPrecedence: Int = 1): Expression {
        var left = unary()
        while (true) {
            val precedence = precedence(current().kind)
            if (precedence < minPrecedence) break
            val operator = take().kind
            val right = expression(precedence + 1)
            left = BinaryExpression(left, operator, right)
        }
        return left
    }

    private fun unary(): Expression {
        if (current().kind in unaryOperators) return UnaryExpression(take().kind, unary())
        return primary()
    }

    private fun primary(): Expression {
        var expr: Expression = when (current().kind) {
            TokenKind.IDENT -> NameExpression(take().lexeme)
            TokenKind.INT, TokenKind.FLOAT, TokenKind.IMAG, TokenKind.CHAR, TokenKind.STRING -> LiteralExpression(take())
            TokenKind.LPAREN -> { take(); val inner = expression(); expect(TokenKind.RPAREN); ParenthesizedExpression(inner) }
            else -> fail("expected expression")
        }
        while (true) {
            expr = when {
                match(TokenKind.PERIOD) -> SelectorExpression(expr, expect(TokenKind.IDENT).lexeme)
                match(TokenKind.LBRACK) -> { val i = expression(); expect(TokenKind.RBRACK); IndexExpression(expr, i) }
                match(TokenKind.LPAREN) -> {
                    val args = if (at(TokenKind.RPAREN)) emptyList() else expressionList()
                    expect(TokenKind.RPAREN)
                    CallExpression(expr, args)
                }
                else -> return expr
            }
        }
    }

    private fun asExpression(statement: Statement): Expression =
        (statement as? ExpressionStatement)?.expression ?: fail("expected condition expression")

    private fun semicolon() { expect(TokenKind.SEMICOLON) }
    private fun optionalSemicolon() { match(TokenKind.SEMICOLON) }
    private fun at(kind: TokenKind) = current().kind == kind
    private fun match(kind: TokenKind): Boolean = if (at(kind)) { take(); true } else false
    private fun expect(kind: TokenKind): Token = if (at(kind)) take() else fail("expected $kind, found ${current().kind}")
    private fun take() = tokens[index++]
    private fun current() = tokens[index.coerceAtMost(tokens.lastIndex)]
    private fun fail(message: String): Nothing = throw ParseError(message, current().position)
    private fun List<Expression>.singleOrFail() = if (size == 1) single() else fail("expected one expression")

    companion object {
        // Filled with legal assignment forms; communication statements are added with channel support.
        private val assignmentOperators = setOf(TokenKind.ASSIGN, TokenKind.DEFINE, TokenKind.ADD_ASSIGN,
            TokenKind.SUB_ASSIGN, TokenKind.MUL_ASSIGN, TokenKind.QUO_ASSIGN, TokenKind.REM_ASSIGN,
            TokenKind.AND_ASSIGN, TokenKind.OR_ASSIGN, TokenKind.XOR_ASSIGN, TokenKind.SHL_ASSIGN,
            TokenKind.SHR_ASSIGN, TokenKind.AND_NOT_ASSIGN)
        private val unaryOperators = setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.NOT, TokenKind.XOR, TokenKind.AND, TokenKind.MUL, TokenKind.ARROW)
        private fun precedence(kind: TokenKind) = when (kind) {
            TokenKind.LOR -> 1
            TokenKind.LAND -> 2
            TokenKind.EQL, TokenKind.NEQ, TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ -> 3
            TokenKind.ADD, TokenKind.SUB, TokenKind.OR, TokenKind.XOR -> 4
            TokenKind.MUL, TokenKind.QUO, TokenKind.REM, TokenKind.SHL, TokenKind.SHR, TokenKind.AND, TokenKind.AND_NOT -> 5
            else -> 0
        }
    }
}
