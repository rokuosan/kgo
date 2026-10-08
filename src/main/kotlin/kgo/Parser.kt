package kgo

class ParseError(message: String, val position: Position) : RuntimeException(
    "${position.line}:${position.column}: $message"
)

/** Recursive-descent parser for the executable Go 1.0 core. */
class Parser(private val tokens: List<Token>) {
    private var index = 0
    private var allowCompositeLiteral = true
    private var parsingTopLevelDeclaration = false

    fun parseFile(): GoFile {
        expect(TokenKind.PACKAGE)
        val packageToken = expect(TokenKind.IDENT)
        if (packageToken.lexeme == "_") throw ParseError("package name cannot be blank", packageToken.position)
        semicolon()
        val declarations = mutableListOf<Declaration>()
        while (match(TokenKind.IMPORT)) {
            declarations += parseImport()
        }
        while (!at(TokenKind.EOF)) {
            when {
                match(TokenKind.FUNC) -> declarations += parseTopLevelDeclaration(::parseFunction)
                match(TokenKind.VAR) -> declarations += parseTopLevelDeclaration(::parseVariables)
                match(TokenKind.CONST) -> declarations += parseTopLevelDeclaration(::parseConstants)
                match(TokenKind.TYPE) -> declarations += parseTopLevelDeclaration(::parseTypes)
                else -> fail("expected top-level declaration")
            }
        }
        return GoFile(packageToken.lexeme, declarations)
    }

    private fun parseImport(): ImportDeclaration {
        val imports = mutableListOf<ImportSpecSyntax>()
        if (match(TokenKind.LPAREN)) {
            while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
                if (match(TokenKind.SEMICOLON)) continue
                val alias = if (at(TokenKind.IDENT) || at(TokenKind.PERIOD)) take().lexeme else null
                imports += ImportSpecSyntax(alias, expect(TokenKind.STRING).lexeme)
                semicolonOrClose(TokenKind.RPAREN)
            }
            expect(TokenKind.RPAREN); semicolon()
        } else {
            val alias = if (at(TokenKind.IDENT) || at(TokenKind.PERIOD)) take().lexeme else null
            imports += ImportSpecSyntax(alias, expect(TokenKind.STRING).lexeme)
            semicolon()
        }
        return ImportDeclaration(imports)
    }

    private fun parseFunction(): FunctionDeclaration {
        val receiver = if (match(TokenKind.LPAREN)) {
            val receiverName: String?
            val receiverType: GoTypeSyntax
            if (match(TokenKind.MUL)) {
                receiverName = null
                receiverType = PointerGoType(parseType())
            } else {
                val first = expect(TokenKind.IDENT).lexeme
                if (current().kind == TokenKind.RPAREN) {
                    receiverName = null
                    receiverType = NamedGoType(first)
                } else {
                    receiverName = first
                    receiverType = parseType()
                }
            }
            expect(TokenKind.RPAREN)
            ParameterSyntax(receiverName, receiverType)
        } else null
        val name = expect(TokenKind.IDENT).lexeme
        val parameters = parseParameters()
        val resultParameters = parseResults()
        val body = if (at(TokenKind.LBRACE)) parseBlock() else null
        optionalSemicolon()
        return FunctionDeclaration(name, parameters.map { it.name }, body, parameters.map { it.type },
            resultParameters.map { it.type }, receiver, parameters.lastOrNull()?.variadic == true,
            resultParameters.map { it.name })
    }

    private fun <T> parseTopLevelDeclaration(parse: () -> T): T {
        val previous = parsingTopLevelDeclaration
        parsingTopLevelDeclaration = true
        return try { parse() } finally { parsingTopLevelDeclaration = previous }
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
        if (parameters.any { it.name != null } && parameters.any { it.name == null })
            fail("parameter names must be either all present or all absent")
        return parameters
    }

    private fun isNamedParameterGroup(): Boolean {
        var look = index + 1
        if (tokens.getOrNull(look)?.kind != TokenKind.IDENT) return false
        look++
        while (tokens.getOrNull(look)?.kind == TokenKind.COMMA && tokens.getOrNull(look + 1)?.kind == TokenKind.IDENT) look += 2
        return tokens.getOrNull(look)?.kind?.let(::typeStart) == true
    }

    private fun parseResults(): List<ParameterSyntax> {
        val results = if (at(TokenKind.LPAREN)) parseParameters()
            else if (typeStart(current().kind)) listOf(ParameterSyntax(null, parseType()))
            else emptyList()
        if (results.any { it.variadic }) fail("result parameter cannot be variadic")
        return results
    }

    private fun parseVariables(): List<VariableDeclaration> {
        if (!match(TokenKind.LPAREN)) return listOf(parseVariableSpec())
        val declarations = mutableListOf<VariableDeclaration>()
        while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            declarations += parseVariableSpec(grouped = true)
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
            val repeatsPrevious = !match(TokenKind.ASSIGN)
            val values = if (!repeatsPrevious) expressionList() else {
                if (!grouped || declarations.isEmpty() || previousValues.isEmpty())
                    fail("missing initializer in const declaration")
                previousValues
            }
            if (repeatsPrevious) type = previousType
            declarations += ConstantDeclaration(names, values, type, declarations.size)
            previousType = type
            previousValues = values
            if (!grouped) break
            semicolonOrClose(TokenKind.RPAREN)
            if (at(TokenKind.RPAREN)) break
        }
        if (grouped) { expect(TokenKind.RPAREN); optionalSemicolon() } else optionalSemicolon()
        return declarations
    }

    private fun parseTypes(): List<TypeDeclaration> {
        if (!match(TokenKind.LPAREN)) {
            val declaration = parseTypeDeclaration()
            optionalSemicolon()
            return listOf(declaration)
        }
        val declarations = mutableListOf<TypeDeclaration>()
        while (!at(TokenKind.RPAREN) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            declarations += parseTypeDeclaration()
            semicolonOrClose(TokenKind.RPAREN)
        }
        expect(TokenKind.RPAREN)
        optionalSemicolon()
        return declarations
    }

    private fun parseTypeDeclaration(): TypeDeclaration {
        val name = expect(TokenKind.IDENT).lexeme
        if ((at(TokenKind.STRUCT) || at(TokenKind.INTERFACE)) && tokens.getOrNull(index + 1)?.kind != TokenKind.LBRACE) {
            return when (take().kind) {
                TokenKind.STRUCT -> TypeDeclaration(name, StructGoType(emptyList()), incomplete = true)
                TokenKind.INTERFACE -> TypeDeclaration(name, InterfaceGoType(emptyList()), incomplete = true)
                else -> error("unreachable")
            }
        }
        return TypeDeclaration(name, parseType())
    }

    private fun parseVariableSpec(grouped: Boolean = false): VariableDeclaration {
        val names = parseNameList()
        val type = if (typeStart(current().kind) && !at(TokenKind.ASSIGN)) parseType() else null
        val values = if (match(TokenKind.ASSIGN)) expressionList() else emptyList()
        if (type == null && values.isEmpty()) fail("expected a type or initializer")
        if (grouped) semicolonOrClose(TokenKind.RPAREN) else optionalSemicolon()
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
        if (at(TokenKind.RBRACE) || at(TokenKind.CASE) || at(TokenKind.DEFAULT)) return EmptyStatement
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

    private fun parseSwitch(): Statement {
        var init: Statement? = null
        var tag: Expression? = null
        var typeGuard: TypeSwitchGuard? = null
        if (!at(TokenKind.LBRACE)) {
            val first = expressionHeader { parseSimpleStatement() }
            if (match(TokenKind.SEMICOLON)) {
                init = first
                if (!at(TokenKind.LBRACE)) {
                    val second = expressionHeader { parseSimpleStatement() }
                    typeGuard = parseTypeSwitchGuard(second)
                    if (typeGuard == null) tag = asExpression(second)
                }
            } else {
                typeGuard = parseTypeSwitchGuard(first)
                if (typeGuard == null) tag = asExpression(first)
            }
        }
        if (typeGuard != null) return parseTypeSwitch(init, typeGuard)
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

    private fun parseTypeSwitchGuard(statement: Statement): TypeSwitchGuard? = when (statement) {
        is ExpressionStatement -> (statement.expression as? TypeSwitchGuardExpression)?.let { TypeSwitchGuard(null, it.receiver) }
        is AssignmentStatement -> {
            if (statement.operator != TokenKind.DEFINE || statement.targets.size != 1 || statement.values.size != 1) null
            else {
                val name = (statement.targets.single() as? NameExpression)?.name ?: fail("type switch guard must declare an identifier")
                val guard = statement.values.single() as? TypeSwitchGuardExpression
                if (guard == null) null else TypeSwitchGuard(name, guard.receiver)
            }
        }
        else -> null
    }

    private fun parseTypeSwitch(init: Statement?, guard: TypeSwitchGuard): TypeSwitchStatement {
        expect(TokenKind.LBRACE)
        val clauses = mutableListOf<TypeSwitchClause>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            if (match(TokenKind.SEMICOLON)) continue
            val types = when {
                match(TokenKind.CASE) -> {
                    val cases = mutableListOf(parseType())
                    while (match(TokenKind.COMMA)) cases += parseType()
                    cases
                }
                match(TokenKind.DEFAULT) -> null
                else -> fail("expected case or default in type switch")
            }
            expect(TokenKind.COLON)
            val statements = mutableListOf<Statement>()
            while (!at(TokenKind.CASE) && !at(TokenKind.DEFAULT) && !at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
                if (match(TokenKind.SEMICOLON)) continue
                statements += parseStatement()
                if (!match(TokenKind.SEMICOLON) && !at(TokenKind.CASE) && !at(TokenKind.DEFAULT) && !at(TokenKind.RBRACE))
                    fail("expected semicolon in type switch clause")
            }
            clauses += TypeSwitchClause(types, statements)
        }
        expect(TokenKind.RBRACE)
        return TypeSwitchStatement(init, guard, clauses)
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
        if (match(TokenKind.RANGE)) fail("range clause requires at least one iteration variable")
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
            val expression = rangeExpression()
            return ForStatement(null, null, null, parseBlock(), RangeClause(possibleTargets, possibleOperator, expression))
        }
        if (possibleOperator == null && match(TokenKind.RANGE))
            fail("range variables require = or :=")
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
        if (at(TokenKind.SEMICOLON)) return EmptyStatement
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
            TokenKind.CHAN, TokenKind.ARROW, TokenKind.MUL, TokenKind.LBRACK, TokenKind.MAP, TokenKind.STRUCT, TokenKind.INTERFACE -> {
                val type = parseType()
                if (allowCompositeLiteral && at(TokenKind.LBRACE)) parseCompositeLiteral(type) else TypeExpression(type)
            }
            TokenKind.FUNC -> {
                take()
                val parameters = parseParameters()
                val results = parseResults()
                if (at(TokenKind.LBRACE)) FunctionLiteralExpression(parameters, results.map { it.type }, parseBlock(),
                    parameters.lastOrNull()?.variadic == true, results.map { it.name })
                else if (at(TokenKind.LPAREN) || at(TokenKind.RPAREN))
                    TypeExpression(FunctionGoType(parameters, results.map { it.type }))
                else fail("expected function body or conversion")
            }
            TokenKind.LPAREN -> { take(); val inner = expressionWithComposite { expression() }; expect(TokenKind.RPAREN); ParenthesizedExpression(inner) }
            else -> fail("expected expression")
        }
        while (true) {
            expr = when {
                match(TokenKind.PERIOD) -> if (match(TokenKind.LPAREN)) {
                    if (match(TokenKind.TYPE)) {
                        expect(TokenKind.RPAREN)
                        TypeSwitchGuardExpression(expr)
                    } else {
                        val assertedType = parseType()
                        expect(TokenKind.RPAREN)
                        TypeAssertionExpression(expr, assertedType)
                    }
                } else SelectorExpression(expr, expect(TokenKind.IDENT).lexeme)
                match(TokenKind.LBRACK) -> {
                    val low = if (at(TokenKind.COLON) || at(TokenKind.RBRACK)) null else expression()
                    if (match(TokenKind.COLON)) {
                        val high = if (at(TokenKind.COLON) || at(TokenKind.RBRACK)) null else expression()
                        expect(TokenKind.RBRACK)
                        SliceExpression(expr, low, high)
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
        return CompositeLiteral(type, parseCompositeElements())
    }

    private fun parseElidedCompositeLiteral(): ElidedCompositeLiteral = ElidedCompositeLiteral(parseCompositeElements())

    private fun parseCompositeElements(): List<CompositeElement> {
        expect(TokenKind.LBRACE)
        val elements = mutableListOf<CompositeElement>()
        while (!at(TokenKind.RBRACE) && !at(TokenKind.EOF)) {
            val first = if (at(TokenKind.LBRACE)) parseElidedCompositeLiteral() else expression()
            if (match(TokenKind.COLON)) elements += CompositeElement(first, parseCompositeElementValue())
            else elements += CompositeElement(null, first)
            if (!match(TokenKind.COMMA) && !at(TokenKind.RBRACE)) fail("expected ',' or '}' in composite literal")
        }
        expect(TokenKind.RBRACE)
        return elements
    }

    private fun parseCompositeElementValue(): Expression = if (at(TokenKind.LBRACE)) {
        parseElidedCompositeLiteral()
    } else expression()

    private fun <T> expressionHeader(block: () -> T): T {
        return withCompositeLiterals(false, block)
    }

    private fun rangeExpression(): Expression = if (rangeExpressionStartsWithUnambiguousCompositeType())
        expressionWithComposite { expression() } else expressionHeader { expression() }

    private fun rangeExpressionStartsWithUnambiguousCompositeType(): Boolean {
        var tokenIndex = index
        while (tokens.getOrNull(tokenIndex)?.kind in setOf(
                TokenKind.ADD, TokenKind.SUB, TokenKind.NOT, TokenKind.XOR,
                TokenKind.MUL, TokenKind.AND, TokenKind.ARROW
            )) {
            tokenIndex++
        }
        return tokens.getOrNull(tokenIndex)?.kind in setOf(TokenKind.LBRACK, TokenKind.MAP, TokenKind.STRUCT)
    }

    private fun <T> expressionWithComposite(block: () -> T): T = withCompositeLiterals(true, block)

    private fun <T> withCompositeLiterals(enabled: Boolean, block: () -> T): T {
        val previous = allowCompositeLiteral
        allowCompositeLiteral = enabled
        return try { block() } finally { allowCompositeLiteral = previous }
    }

    private fun parseType(): GoTypeSyntax = when {
        match(TokenKind.LPAREN) -> parseType().also { expect(TokenKind.RPAREN) }
        match(TokenKind.MUL) -> PointerGoType(parseType())
        match(TokenKind.LBRACK) -> {
            if (match(TokenKind.RBRACK)) SliceGoType(parseType())
            else if (match(TokenKind.ELLIPSIS)) {
                expect(TokenKind.RBRACK)
                ArrayGoType(null, parseType())
            }
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
            FunctionGoType(parameters, parseResults().map { it.type })
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
                if (match(TokenKind.PERIOD)) {
                    names = emptyList()
                    type = QualifiedGoType(first, expect(TokenKind.IDENT).lexeme)
                } else {
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
            }
            val tag = if (at(TokenKind.STRING)) canonicalGoStringLiteral(take().lexeme) else null
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
            val typeName = if (match(TokenKind.PERIOD)) QualifiedGoType(name, expect(TokenKind.IDENT).lexeme)
                else NamedGoType(name)
            if (typeName is NamedGoType && at(TokenKind.LPAREN)) {
                val parameters = parseParameters()
                methods += InterfaceMethodSyntax(typeName.name, parameters, parseResults().map { it.type })
            } else {
                embedded += typeName
            }
            if (!match(TokenKind.SEMICOLON) && !at(TokenKind.RBRACE)) fail("expected semicolon or '}' in interface type")
        }
        expect(TokenKind.RBRACE)
        return InterfaceGoType(methods, embedded)
    }

    private fun asExpression(statement: Statement): Expression =
        (statement as? ExpressionStatement)?.expression ?: fail("expected condition expression")

    private fun semicolon() { expect(TokenKind.SEMICOLON) }
    private fun semicolonOrClose(close: TokenKind) {
        if (!match(TokenKind.SEMICOLON) && !at(close)) fail("expected semicolon or $close")
    }
    private fun optionalSemicolon() {
        if (parsingTopLevelDeclaration) semicolon() else match(TokenKind.SEMICOLON)
    }
    private fun at(kind: TokenKind) = current().kind == kind
    private fun match(kind: TokenKind): Boolean = if (at(kind)) { take(); true } else false
    private fun expect(kind: TokenKind): Token = if (at(kind)) take() else fail("expected $kind, found ${current().kind}")
    private fun take() = tokens[index++]
    private fun current() = tokens[index.coerceAtMost(tokens.lastIndex)]
    private fun fail(message: String): Nothing = throw ParseError(message, current().position)
    private fun List<Expression>.singleOrFail() = if (size == 1) single() else fail("expected one expression")

    companion object {
        // Sends are parsed as communication statements; these are assignment operators.
        private val assignmentOperators = setOf(TokenKind.ASSIGN, TokenKind.DEFINE, TokenKind.ADD_ASSIGN,
            TokenKind.SUB_ASSIGN, TokenKind.MUL_ASSIGN, TokenKind.QUO_ASSIGN, TokenKind.REM_ASSIGN,
            TokenKind.AND_ASSIGN, TokenKind.OR_ASSIGN, TokenKind.XOR_ASSIGN, TokenKind.SHL_ASSIGN,
            TokenKind.SHR_ASSIGN, TokenKind.AND_NOT_ASSIGN)
        private val unaryOperators = setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.NOT, TokenKind.XOR, TokenKind.AND, TokenKind.MUL, TokenKind.ARROW)
        private fun typeStart(kind: TokenKind) = kind in setOf(TokenKind.IDENT, TokenKind.LPAREN, TokenKind.MUL, TokenKind.LBRACK, TokenKind.MAP, TokenKind.CHAN, TokenKind.ARROW, TokenKind.STRUCT, TokenKind.INTERFACE, TokenKind.FUNC)
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
