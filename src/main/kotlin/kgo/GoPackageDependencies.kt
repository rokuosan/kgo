package kgo

/** Collect package-level names referenced by a function during package initialization analysis. */
internal object GoPackageDependencies {
    fun functionReferences(
        function: FunctionDeclaration,
        resolveType: (GoTypeSyntax) -> GoTypeSyntax? = { it },
        callReferences: (Expression, Set<String>) -> Set<String> = { _, _ -> emptySet() }
    ): Set<String> {
        val locals = function.parameters.filterNotNull().toMutableSet()
        function.receiver?.name?.let(locals::add)
        function.resultNames.filterNotNull().forEach(locals::add)
        return function.body?.let { blockReferences(it, locals, resolveType, callReferences) } ?: emptySet()
    }

    fun expressionReferences(
        expression: Expression,
        resolveType: (GoTypeSyntax) -> GoTypeSyntax? = { it },
        callReferences: (Expression, Set<String>) -> Set<String> = { _, _ -> emptySet() }
    ): Set<String> = expressionReferences(expression, emptySet(), resolveType, null, callReferences)

    fun functionLiteralReferences(
        parameters: List<ParameterSyntax>,
        resultNames: List<String?>,
        body: BlockStatement,
        captured: Set<String> = emptySet(),
        resolveType: (GoTypeSyntax) -> GoTypeSyntax? = { it },
        callReferences: (Expression, Set<String>) -> Set<String> = { _, _ -> emptySet() }
    ): Set<String> {
        val locals = (captured + parameters.mapNotNull { it.name } + resultNames.filterNotNull()).toMutableSet()
        return blockReferences(body, locals, resolveType, callReferences)
    }

    private fun blockReferences(
        block: BlockStatement,
        inherited: Set<String>,
        resolveType: (GoTypeSyntax) -> GoTypeSyntax?,
        callReferences: (Expression, Set<String>) -> Set<String> = { _, _ -> emptySet() }
    ): Set<String> {
        val locals = inherited.toMutableSet()
        val references = linkedSetOf<String>()
        block.statements.forEach { references += statementReferences(it, locals, resolveType, callReferences) }
        return references
    }

    private fun statementReferences(
        statement: Statement,
        locals: MutableSet<String>,
        resolveType: (GoTypeSyntax) -> GoTypeSyntax?,
        callReferences: (Expression, Set<String>) -> Set<String> = { _, _ -> emptySet() }
    ): Set<String> = when (statement) {
        EmptyStatement -> emptySet()
        is LabeledStatement -> statementReferences(statement.statement, locals, resolveType, callReferences)
        is DeclarationStatement -> buildSet {
            statement.declarations.forEach { declaration -> when (declaration) {
                is VariableDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is ConstantDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is TypeDeclaration -> locals += declaration.name
                else -> Unit
            } }
        }
        is BlockStatement -> blockReferences(statement, locals, resolveType, callReferences)
        is VariableStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }.toSet() - locals)
            locals += statement.names.filter { it != "_" }
        }
        is ReturnStatement -> statement.values.flatMapTo(linkedSetOf()) { expressionReferences(it, locals, resolveType, callReferences = callReferences) } - locals
        is ExpressionStatement -> expressionReferences(statement.expression, locals, resolveType, callReferences = callReferences) - locals
        is SendStatement -> (expressionReferences(statement.channel, locals, resolveType, callReferences = callReferences) + expressionReferences(statement.value, locals, resolveType, callReferences = callReferences)) - locals
        is GoStatement -> expressionReferences(statement.call, locals, resolveType, callReferences = callReferences) - locals
        is DeferStatement -> expressionReferences(statement.call, locals, resolveType, callReferences = callReferences) - locals
        is BranchStatement -> emptySet()
        is AssignmentStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }.toSet() - locals)
            if (statement.operator == TokenKind.DEFINE) {
                locals += statement.targets.mapNotNull { (it as? NameExpression)?.name }.filter { it != "_" }
            } else addAll(statement.targets.flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }.toSet() - locals)
        }
        is IncrementStatement -> expressionReferences(statement.target, locals, resolveType, callReferences = callReferences) - locals
        is IfStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, resolveType, callReferences) }
            references += expressionReferences(statement.condition, scoped, resolveType, callReferences = callReferences) - scoped
            references += blockReferences(statement.thenBranch, scoped, resolveType, callReferences)
            statement.elseBranch?.let { references += statementReferences(it, scoped.toMutableSet(), resolveType, callReferences) }
            references
        }
        is ForStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, resolveType, callReferences) }
            statement.condition?.let { references += expressionReferences(it, scoped, resolveType, callReferences = callReferences) - scoped }
            statement.post?.let { references += statementReferences(it, scoped, resolveType, callReferences) }
            statement.rangeClause?.let { range ->
                references += expressionReferences(range.expression, scoped, resolveType, callReferences = callReferences) - scoped
                if (range.operator != TokenKind.DEFINE)
                    references += range.targets.flatMap { expressionReferences(it, scoped, resolveType, callReferences = callReferences) }.toSet() - scoped
            }
            val bodyLocals = scoped.toMutableSet()
            statement.rangeClause?.takeIf { it.operator == TokenKind.DEFINE }?.targets
                ?.mapNotNullTo(bodyLocals) { (it as? NameExpression)?.name }
            references += blockReferences(statement.body, bodyLocals, resolveType, callReferences)
            references
        }
        is SwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, resolveType, callReferences) }
            statement.tag?.let { references += expressionReferences(it, scoped, resolveType, callReferences = callReferences) - scoped }
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                clause.expressions?.forEach { references += expressionReferences(it, caseLocals, resolveType, callReferences = callReferences) - caseLocals }
                val body = BlockStatement(clause.statements)
                references += blockReferences(body, caseLocals, resolveType, callReferences)
            }
            references
        }
        is TypeSwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, resolveType, callReferences) }
            references += expressionReferences(statement.guard.expression, scoped, resolveType, callReferences = callReferences) - scoped
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                statement.guard.name?.takeIf { it != "_" }?.let(caseLocals::add)
                references += blockReferences(BlockStatement(clause.statements), caseLocals, resolveType, callReferences)
            }
            references
        }
        is SelectStatement -> {
            val references = linkedSetOf<String>()
            statement.cases.forEach { clause ->
                val caseLocals = locals.toMutableSet()
                clause.communication?.let { references += statementReferences(it, caseLocals, resolveType, callReferences) }
                references += blockReferences(BlockStatement(clause.statements), caseLocals, resolveType, callReferences)
            }
            references
        }
    }

    private fun expressionReferences(
        expression: Expression,
        locals: Set<String> = emptySet(),
        resolveType: (GoTypeSyntax) -> GoTypeSyntax?,
        expectedType: GoTypeSyntax? = null,
        callReferences: (Expression, Set<String>) -> Set<String> = { _, _ -> emptySet() }
    ): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> expressionReferences(expression.operand, locals, resolveType, callReferences = callReferences)
        is BinaryExpression -> expressionReferences(expression.left, locals, resolveType, callReferences = callReferences) +
            expressionReferences(expression.right, locals, resolveType, callReferences = callReferences)
        is CallExpression -> expressionReferences(expression.function, locals, resolveType, callReferences = callReferences) +
            expression.arguments.flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }
        is SelectorExpression -> expressionReferences(expression.receiver, locals, resolveType, callReferences = callReferences) +
            callReferences(expression, locals)
        is IndexExpression -> expressionReferences(expression.receiver, locals, resolveType, callReferences = callReferences) +
            expressionReferences(expression.index, locals, resolveType, callReferences = callReferences)
        is SliceExpression -> expressionReferences(expression.receiver, locals, resolveType, callReferences = callReferences) +
            listOfNotNull(expression.low, expression.high).flatMap { expressionReferences(it, locals, resolveType, callReferences = callReferences) }
        is TypeAssertionExpression -> expressionReferences(expression.receiver, locals, resolveType, callReferences = callReferences)
        is TypeSwitchGuardExpression -> expressionReferences(expression.receiver, locals, resolveType, callReferences = callReferences)
        is ParenthesizedExpression -> expressionReferences(expression.expression, locals, resolveType, callReferences = callReferences)
        is CompositeLiteral -> compositeElementsReferences(expression.elements, resolveType(expression.type), locals, resolveType, callReferences)
        is ElidedCompositeLiteral -> compositeElementsReferences(expression.elements, expectedType, locals, resolveType, callReferences)
        is FunctionLiteralExpression -> functionLiteralReferences(expression.parameters, expression.resultNames,
            expression.body, locals, resolveType, callReferences)
    }

    private fun compositeElementsReferences(
        elements: List<CompositeElement>,
        type: GoTypeSyntax?,
        locals: Set<String>,
        resolveType: (GoTypeSyntax) -> GoTypeSyntax?,
        callReferences: (Expression, Set<String>) -> Set<String>
    ): Set<String> {
        val resolvedType = type?.let { resolveType(it) ?: it }
        val actual = when (resolvedType) {
            is PointerGoType -> resolvedType.element
            else -> resolvedType
        }
        val fields = (actual as? StructGoType)?.fields?.flatMap { field ->
            field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }.map { it to field.type }
        }.orEmpty()
        return elements.flatMapIndexed { index, element ->
            val valueType = when (actual) {
                is ArrayGoType -> actual.element
                is SliceGoType -> actual.element
                is MapGoType -> actual.value
                is StructGoType -> {
                    val fieldName = (element.key as? NameExpression)?.name
                    if (fieldName == null) fields.getOrNull(index)?.second
                    else fields.firstOrNull { it.first == fieldName }?.second
                }
                else -> null
            }
            buildList {
                if (actual !is StructGoType) element.key?.let { add(it to (actual as? MapGoType)?.key) }
                add(element.value to valueType)
            }.flatMap { (expression, expectedType) ->
                expressionReferences(expression, locals, resolveType, expectedType, callReferences)
            }
        }.toSet()
    }

    private fun embeddedFieldName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> type.name
        is PointerGoType -> embeddedFieldName(type.element)
        else -> ""
    }
}
