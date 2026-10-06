package kgo

class ParseError(message: String, val position: Position) : RuntimeException(
    "${position.line}:${position.column}: $message"
)

/** Recursive-descent parser for the executable Go 1.0 core. */
class Parser(private val tokens: List<Token>) {
    private var index = 0
    private var allowCompositeLiteral = true

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
                match(TokenKind.CONST) -> declarations += parseConstants()
                match(TokenKind.TYPE) -> declarations += parseTypes()
                else -> fail("expected top-level declaration")
            }
        }
        return GoFile(packageName, declarations)
    }

    private fun parseImport(): ImportDeclaration {
        val imports = mutableListOf<ImportSpecSyntax>()
        if (match(TokenKind.LPAREN)) {
            while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
                if (match(TokenKind.SEMICOLON)) continue
                val alias = if (at(TokenKind.IDENT) || at(TokenKind.PERIOD)) take().lexeme else null
                imports += ImportSpecSyntax(alias, expect(TokenKind.STRING).lexeme)
                semicolon()
            }
            expect(TokenKind.RPAREN); optionalSemicolon()
        } else {
            val alias = if (at(TokenKind.IDENT) || at(TokenKind.PERIOD)) take().lexeme else null
            imports += ImportSpecSyntax(alias, expect(TokenKind.STRING).lexeme)
            semicolon()
        }
        return ImportDeclaration(imports)
    }

    private fun parseFunction(): FunctionDeclaration {
        val receiver = if (match(TokenKind.LPAREN)) {
            val receiverName = expect(TokenKind.IDENT).lexeme
            val receiverType = parseType()
            expect(TokenKind.RPAREN)
            ParameterSyntax(receiverName, receiverType)
        } else null
        val name = expect(TokenKind.IDENT).lexeme
        val parameters = parseParameters()
        val results = parseResults()
        val body = parseBlock()
        optionalSemicolon()
        return FunctionDeclaration(name, parameters.map { it.name }, body, parameters.map { it.type }, results, receiver,
            parameters.lastOrNull()?.variadic == true)
    }

    private fun parseParameters(): List<ParameterSyntax> {
        expect(TokenKind.LPAREN)
        val parameters = mutableListOf<ParameterSyntax>()
        while (!at(TokenKind.RPAREN)) {
            val names = mutableListOf<String>()
            val first: String?
            if (at(TokenKind.IDENT)) {
                first = take().lexeme
                names += first
                while (at(TokenKind.COMMA) && isNamedParameterGroup()) {
                    take()
                    names += expect(TokenKind.IDENT).lexeme
                }
            } else first = null
            val variadic = match(TokenKind.ELLIPSIS)
            val rawType = if (typeStart(current().kind)) parseType() else {
                if (first == null || names.size != 1) fail("expected parameter type")
                names.clear()
                NamedGoType(first)
            }
            val type = if (variadic) SliceGoType(rawType) else rawType
            if (names.isEmpty()) parameters += ParameterSyntax(null, type, variadic)
            else names.forEach { parameters += ParameterSyntax(it, type, variadic) }
            if (!match(TokenKind.COMMA)) break
        }
        expect(TokenKind.RPAREN)
        if (parameters.dropLast(1).any { it.variadic }) fail("variadic parameter must be last")
        return parameters
    }

    private fun isNamedParameterGroup(): Boolean {
        var look = index + 1
        if (tokens.getOrNull(look)?.kind != TokenKind.IDENT) return false
        look++
        while (tokens.getOrNull(look)?.kind == TokenKind.COMMA && tokens.getOrNull(look + 1)?.kind == TokenKind.IDENT) look += 2
        return tokens.getOrNull(look)?.kind?.let(::typeStart) == true
    }

    private fun parseResults(): List<GoTypeSyntax> {
        if (at(TokenKind.LPAREN)) return parseParameters().map { it.type }
        return if (typeStart(current().kind)) listOf(parseType()) else emptyList()
    }

    private fun parseVariables(): List<VariableDeclaration> {
        if (!match(TokenKind.LPAREN)) return listOf(parseVariableSpec())
        val declarations = mutableListOf<VariableDeclaration>()
        while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            declarations += parseVariableSpec()
        }
        expect(TokenKind.RPAREN)
        optionalSemicolon()
        return declarations
    }

    private fun parseConstants(): List<ConstantDeclaration> {
        val grouped = match(TokenKind.LPAREN)
        val declarations = mutableListOf<ConstantDeclaration>()
        var previousType: GoTypeSyntax? = null
        var previousValues: List<Expression> = emptyList()
        while (true) {
            if (grouped && match(TokenKind.SEMICOLON)) {
                if (at(TokenKind.RPAREN)) break
                continue
            }
            val names = parseNameList()
            var type: GoTypeSyntax? = null
            if (typeStart(current().kind) && !at(TokenKind.ASSIGN)) type = parseType()
            val values = if (match(TokenKind.ASSIGN)) expressionList() else previousValues
            if (type == null) type = previousType
            declarations += ConstantDeclaration(names, values, type, declarations.size)
            previousType = type
            previousValues = values
            if (!grouped) break
            semicolon()
            if (at(TokenKind.RPAREN)) break
        }
        if (grouped) { expect(TokenKind.RPAREN); optionalSemicolon() } else semicolon()
        return declarations
    }

    private fun parseTypes(): List<TypeDeclaration> {
        if (!match(TokenKind.LPAREN)) {
            val declaration = TypeDeclaration(expect(TokenKind.IDENT).lexeme, parseType())
            semicolon()
            return listOf(declaration)
        }
        val declarations = mutableListOf<TypeDeclaration>()
        while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            declarations += TypeDeclaration(expect(TokenKind.IDENT).lexeme, parseType())
            semicolon()
        }
        expect(TokenKind.RPAREN)
        optionalSemicolon()
        return declarations
    }

    private fun parseVariableSpec(): VariableDeclaration {
        val names = parseNameList()
        val type = if (typeStart(current().kind) && !at(TokenKind.ASSIGN)) parseType() else null
        val values = if (match(TokenKind.ASSIGN)) expressionList() else emptyList()
        if (type == null && values.isEmpty()) fail("expected a type or initializer")
        semicolon()
        return VariableDeclaration(names, values, type)
    }

    private fun parseVariableStatement(): VariableStatement {
        val names = parseNameList()
        val type = if (typeStart(current().kind) && !at(TokenKind.DEFINE) && !at(TokenKind.ASSIGN)) parseType() else null
        val values = if (match(TokenKind.DEFINE) || match(TokenKind.ASSIGN)) expressionList() else emptyList()
        if (type == null && values.isEmpty()) fail("expected a type or initializer")
        return VariableStatement(names, values, type)
    }

    private fun parseNameList(): List<String> {
        val names = mutableListOf(expect(TokenKind.IDENT).lexeme)
        while (match(TokenKind.COMMA)) names += expect(TokenKind.IDENT).lexeme
        return names
    }

    private fun parseBlock(): BlockStatement {
        expect(TokenKind.LBRACE)
        val statements = mutableListOf<Statement>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) { statements += EmptyStatement; continue }
            val statement = parseStatement()
            statements += statement
            if (!match(TokenKind.SEMICOLON) && !at(TokenKind.RBRACE) && statement !is DeclarationStatement) {
                fail("expected semicolon or '}'")
            }
        }
        expect(TokenKind.RBRACE)
        return BlockStatement(statements)
    }

    private fun parseStatement(): Statement {
        if (at(TokenKind.IDENT) && tokens.getOrNull(index + 1)?.kind == TokenKind.COLON) {
            val label = take().lexeme
            take()
            return LabeledStatement(label, parseStatement())
        }
        return when {
        at(TokenKind.LBRACE) -> parseBlock()
        match(TokenKind.RETURN) -> ReturnStatement(if (at(TokenKind.SEMICOLON) || at(TokenKind.RBRACE)) emptyList() else expressionList())
        match(TokenKind.VAR) -> DeclarationStatement(parseVariables())
        match(TokenKind.CONST) -> DeclarationStatement(parseConstants())
        match(TokenKind.TYPE) -> DeclarationStatement(parseTypes())
        match(TokenKind.IF) -> parseIf()
        match(TokenKind.FOR) -> parseFor()
        match(TokenKind.GO) -> GoStatement(expression())
        match(TokenKind.DEFER) -> DeferStatement(expression())
        match(TokenKind.BREAK) -> BranchStatement(TokenKind.BREAK, if (at(TokenKind.IDENT)) take().lexeme else null)
        match(TokenKind.CONTINUE) -> BranchStatement(TokenKind.CONTINUE, if (at(TokenKind.IDENT)) take().lexeme else null)
        match(TokenKind.GOTO) -> BranchStatement(TokenKind.GOTO, expect(TokenKind.IDENT).lexeme)
        match(TokenKind.FALLTHROUGH) -> BranchStatement(TokenKind.FALLTHROUGH, null)
        match(TokenKind.SELECT) -> parseSelect()
        match(TokenKind.SWITCH) -> parseSwitch()
        else -> parseSimpleStatement()
        }
    }

    private fun parseSwitch(): SwitchStatement {
        var init: Statement? = null
        var tag: Expression? = null
        if (!at(TokenKind.LBRACE)) {
            val first = expressionHeader { parseSimpleStatement() }
            if (match(TokenKind.SEMICOLON)) {
                init = first
                if (!at(TokenKind.LBRACE)) tag = expressionHeader { expression() }
            } else {
                tag = asExpression(first)
            }
        }
        expect(TokenKind.LBRACE)
        val clauses = mutableListOf<SwitchClause>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            val expressions = when {
                match(TokenKind.CASE) -> expressionList()
                match(TokenKind.DEFAULT) -> null
                else -> fail("expected case or default in switch")
            }
            expect(TokenKind.COLON)
            val statements = mutableListOf<Statement>()
            while (!at(TokenKind.CASE) && !at(TokenKind.DEFAULT) && !at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
                if (match(TokenKind.SEMICOLON)) continue
                statements += parseStatement()
                if (!match(TokenKind.SEMICOLON) && !at(TokenKind.CASE) && !at(TokenKind.DEFAULT) && !at(TokenKind.RBRACE))
                    fail("expected semicolon in switch clause")
            }
            clauses += SwitchClause(expressions, statements)
        }
        expect(TokenKind.RBRACE)
        return SwitchStatement(init, tag, clauses)
    }

    private fun parseSelect(): SelectStatement {
        expect(TokenKind.LBRACE)
        val cases = mutableListOf<SelectCase>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            val communication = when {
                match(TokenKind.CASE) -> parseSimpleStatement()
                match(TokenKind.DEFAULT) -> null
                else -> fail("expected case or default in select")
            }
            expect(TokenKind.COLON)
            val statements = mutableListOf<Statement>()
            while (!at(TokenKind.CASE) && !at(TokenKind.DEFAULT) && !at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
                if (match(TokenKind.SEMICOLON)) continue
                statements += parseStatement()
                if (!match(TokenKind.SEMICOLON) && !at(TokenKind.CASE) && !at(TokenKind.DEFAULT) && !at(TokenKind.RBRACE))
                    fail("expected semicolon in select clause")
            }
            cases += SelectCase(communication, statements)
        }
        expect(TokenKind.RBRACE)
        return SelectStatement(cases)
    }

    private fun parseIf(): IfStatement {
        val first = expressionHeader { parseSimpleStatement() }
        val init: Statement?
        val condition: Expression
        if (match(TokenKind.SEMICOLON)) {
            init = first
            condition = expressionHeader { expression() }
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
        if (match(TokenKind.RANGE)) {
            val expression = expressionHeader { expression() }
            return ForStatement(null, null, null, parseBlock(), RangeClause(emptyList(), null, expression))
        }
        if (match(TokenKind.SEMICOLON)) {
            val condition = if (at(TokenKind.SEMICOLON)) null else expressionHeader { expression() }
            expect(TokenKind.SEMICOLON)
            val post = if (at(TokenKind.LBRACE)) null else parseSimpleStatement()
            return ForStatement(null, condition, post, parseBlock())
        }
        val start = index
        val possibleTargets = expressionHeader { expressionList() }
        val possibleOperator = if (current().kind == TokenKind.DEFINE || current().kind == TokenKind.ASSIGN) take().kind else null
        if (possibleOperator != null && match(TokenKind.RANGE)) {
            val expression = expressionHeader { expression() }
            return ForStatement(null, null, null, parseBlock(), RangeClause(possibleTargets, possibleOperator, expression))
        }
        if (possibleOperator == null && match(TokenKind.RANGE)) {
            val expression = expressionHeader { expression() }
            return ForStatement(null, null, null, parseBlock(), RangeClause(possibleTargets, null, expression))
        }
        index = start
        val first = expressionHeader { parseSimpleStatement() }
        if (match(TokenKind.SEMICOLON)) {
            val condition = if (at(TokenKind.SEMICOLON)) null else expressionHeader { expression() }
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
            TokenKind.IDENT -> {
                val name = take().lexeme
                if (allowCompositeLiteral && at(TokenKind.PERIOD) && tokens.getOrNull(index + 1)?.kind == TokenKind.IDENT) {
                    take()
                    val typeName = take().lexeme
                    if (at(TokenKind.LBRACE)) parseCompositeLiteral(QualifiedGoType(name, typeName))
                    else SelectorExpression(NameExpression(name), typeName)
                } else if (allowCompositeLiteral && at(TokenKind.LBRACE)) parseCompositeLiteral(NamedGoType(name))
                else NameExpression(name)
            }
            TokenKind.INT, TokenKind.FLOAT, TokenKind.IMAG, TokenKind.CHAR, TokenKind.STRING -> LiteralExpression(take())
            TokenKind.CHAN, TokenKind.ARROW, TokenKind.MUL, TokenKind.LBRACK, TokenKind.MAP, TokenKind.STRUCT -> {
                val type = parseType()
                if (allowCompositeLiteral && at(TokenKind.LBRACE)) parseCompositeLiteral(type) else TypeExpression(type)
            }
            TokenKind.FUNC -> {
                take()
                val parameters = parseParameters()
                val results = parseResults()
                FunctionLiteralExpression(parameters, results, parseBlock(), parameters.lastOrNull()?.variadic == true)
            }
            TokenKind.LPAREN -> { take(); val inner = expressionWithComposite { expression() }; expect(TokenKind.RPAREN); ParenthesizedExpression(inner) }
            else -> fail("expected expression")
        }
        while (true) {
            expr = when {
                match(TokenKind.PERIOD) -> SelectorExpression(expr, expect(TokenKind.IDENT).lexeme)
                match(TokenKind.LBRACK) -> {
                    val low = if (at(TokenKind.COLON) || at(TokenKind.RBRACK)) null else expression()
                    if (match(TokenKind.COLON)) {
                        val high = if (at(TokenKind.COLON) || at(TokenKind.RBRACK)) null else expression()
                        val max = if (match(TokenKind.COLON)) expression() else null
                        expect(TokenKind.RBRACK)
                        SliceExpression(expr, low, high, max)
                    } else {
                        expect(TokenKind.RBRACK)
                        IndexExpression(expr, low ?: fail("missing index expression"))
                    }
                }
                match(TokenKind.LPAREN) -> {
                    val args = if (at(TokenKind.RPAREN)) emptyList() else expressionWithComposite { expressionList() }
                    val expand = match(TokenKind.ELLIPSIS)
                    expect(TokenKind.RPAREN)
                    CallExpression(expr, args, expand)
                }
                else -> return expr
            }
        }
    }

    private fun parseCompositeLiteral(type: GoTypeSyntax): CompositeLiteral {
        expect(TokenKind.LBRACE)
        val elements = mutableListOf<CompositeElement>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            val first = expression()
            if (match(TokenKind.COLON)) elements += CompositeElement(first, expression())
            else elements += CompositeElement(null, first)
            if (!match(TokenKind.COMMA) && !at(TokenKind.RBRACE)) fail("expected ',' or '}' in composite literal")
        }
        expect(TokenKind.RBRACE)
        return CompositeLiteral(type, elements)
    }

    private fun <T> expressionHeader(block: () -> T): T {
        return withCompositeLiterals(false, block)
    }

    private fun <T> expressionWithComposite(block: () -> T): T = withCompositeLiterals(true, block)

    private fun <T> withCompositeLiterals(enabled: Boolean, block: () -> T): T {
        val previous = allowCompositeLiteral
        allowCompositeLiteral = enabled
        return try { block() } finally { allowCompositeLiteral = previous }
    }

    private fun parseType(): GoTypeSyntax = when {
        match(TokenKind.MUL) -> PointerGoType(parseType())
        match(TokenKind.LBRACK) -> {
            if (match(TokenKind.RBRACK)) SliceGoType(parseType())
            else {
                val length = expression()
                expect(TokenKind.RBRACK)
                ArrayGoType(length, parseType())
            }
        }
        match(TokenKind.MAP) -> {
            expect(TokenKind.LBRACK)
            val key = parseType()
            expect(TokenKind.RBRACK)
            MapGoType(key, parseType())
        }
        match(TokenKind.CHAN) -> {
            val direction = if (match(TokenKind.ARROW)) ChannelDirection.SEND_ONLY else ChannelDirection.SEND_RECEIVE
            ChannelGoType(parseType(), direction)
        }
        match(TokenKind.ARROW) -> {
            expect(TokenKind.CHAN)
            ChannelGoType(parseType(), ChannelDirection.RECEIVE_ONLY)
        }
        match(TokenKind.STRUCT) -> parseStructType()
        match(TokenKind.INTERFACE) -> parseInterfaceType()
        match(TokenKind.FUNC) -> {
            val parameters = parseParameters()
            FunctionGoType(parameters, parseResults())
        }
        at(TokenKind.IDENT) -> {
            val name = take().lexeme
            if (match(TokenKind.PERIOD)) QualifiedGoType(name, expect(TokenKind.IDENT).lexeme) else NamedGoType(name)
        }
        else -> fail("expected type")
    }

    private fun parseStructType(): StructGoType {
        expect(TokenKind.LBRACE)
        val fields = mutableListOf<StructFieldSyntax>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            val names: List<String>
            val type: GoTypeSyntax
            if (at(TokenKind.MUL)) {
                names = emptyList()
                type = parseType()
            } else {
                val first = expect(TokenKind.IDENT).lexeme
                val fieldNames = mutableListOf(first)
                while (match(TokenKind.COMMA)) fieldNames += expect(TokenKind.IDENT).lexeme
                if (typeStart(current().kind)) {
                    names = fieldNames
                    type = parseType()
                } else {
                    names = emptyList()
                    type = NamedGoType(first)
                }
            }
            val tag = if (at(TokenKind.STRING)) take().lexeme else null
            fields += StructFieldSyntax(names, type, tag)
            if (!match(TokenKind.SEMICOLON) && !at(TokenKind.RBRACE)) fail("expected semicolon or '}' in struct type")
        }
        expect(TokenKind.RBRACE)
        return StructGoType(fields)
    }

    private fun parseInterfaceType(): InterfaceGoType {
        expect(TokenKind.LBRACE)
        val methods = mutableListOf<InterfaceMethodSyntax>()
        val embedded = mutableListOf<GoTypeSyntax>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            val name = expect(TokenKind.IDENT).lexeme
            if (at(TokenKind.LPAREN)) {
                val parameters = parseParameters()
                methods += InterfaceMethodSyntax(name, parameters, parseResults())
            } else {
                embedded += NamedGoType(name)
            }
            if (!match(TokenKind.SEMICOLON) && !at(TokenKind.RBRACE)) fail("expected semicolon or '}' in interface type")
        }
        expect(TokenKind.RBRACE)
        return InterfaceGoType(methods, embedded)
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
        private fun typeStart(kind: TokenKind) = kind in setOf(TokenKind.IDENT, TokenKind.MUL, TokenKind.LBRACK, TokenKind.MAP, TokenKind.CHAN, TokenKind.ARROW, TokenKind.STRUCT, TokenKind.INTERFACE, TokenKind.FUNC)
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
