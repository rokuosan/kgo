package kgo

/** Collect package-level names referenced by a function during package initialization analysis. */
internal object GoPackageDependencies {
    fun functionReferences(
        function: FunctionDeclaration,
        compositeType: (CompositeLiteral) -> GoTypeSyntax? = { it.type }
    ): Set<String> {
        val locals = function.parameters.filterNotNull().toMutableSet()
        function.receiver?.name?.let(locals::add)
        function.resultNames.filterNotNull().forEach(locals::add)
        return function.body?.let { blockReferences(it, locals, compositeType) } ?: emptySet()
    }

    fun functionLiteralReferences(
        parameters: List<ParameterSyntax>,
        resultNames: List<String?>,
        body: BlockStatement,
        captured: Set<String> = emptySet(),
        compositeType: (CompositeLiteral) -> GoTypeSyntax? = { it.type }
    ): Set<String> {
        val locals = (captured + parameters.mapNotNull { it.name } + resultNames.filterNotNull()).toMutableSet()
        return blockReferences(body, locals, compositeType)
    }

    private fun blockReferences(
        block: BlockStatement,
        inherited: Set<String>,
        compositeType: (CompositeLiteral) -> GoTypeSyntax?
    ): Set<String> {
        val locals = inherited.toMutableSet()
        val references = linkedSetOf<String>()
        block.statements.forEach { references += statementReferences(it, locals, compositeType) }
        return references
    }

    private fun statementReferences(
        statement: Statement,
        locals: MutableSet<String>,
        compositeType: (CompositeLiteral) -> GoTypeSyntax?
    ): Set<String> = when (statement) {
        EmptyStatement -> emptySet()
        is LabeledStatement -> statementReferences(statement.statement, locals, compositeType)
        is DeclarationStatement -> buildSet {
            statement.declarations.forEach { declaration -> when (declaration) {
                is VariableDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals, compositeType) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is ConstantDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals, compositeType) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is TypeDeclaration -> locals += declaration.name
                else -> Unit
            } }
        }
        is BlockStatement -> blockReferences(statement, locals, compositeType)
        is VariableStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals, compositeType) }.toSet() - locals)
            locals += statement.names.filter { it != "_" }
        }
        is ReturnStatement -> statement.values.flatMapTo(linkedSetOf()) { expressionReferences(it, locals, compositeType) } - locals
        is ExpressionStatement -> expressionReferences(statement.expression, locals, compositeType) - locals
        is SendStatement -> (expressionReferences(statement.channel, locals, compositeType) + expressionReferences(statement.value, locals, compositeType)) - locals
        is GoStatement -> expressionReferences(statement.call, locals, compositeType) - locals
        is DeferStatement -> expressionReferences(statement.call, locals, compositeType) - locals
        is BranchStatement -> emptySet()
        is AssignmentStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals, compositeType) }.toSet() - locals)
            if (statement.operator == TokenKind.DEFINE) {
                locals += statement.targets.mapNotNull { (it as? NameExpression)?.name }.filter { it != "_" }
            } else addAll(statement.targets.flatMap { expressionReferences(it, locals, compositeType) }.toSet() - locals)
        }
        is IncrementStatement -> expressionReferences(statement.target, locals, compositeType) - locals
        is IfStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, compositeType) }
            references += expressionReferences(statement.condition, scoped, compositeType) - scoped
            references += blockReferences(statement.thenBranch, scoped, compositeType)
            statement.elseBranch?.let { references += statementReferences(it, scoped.toMutableSet(), compositeType) }
            references
        }
        is ForStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, compositeType) }
            statement.condition?.let { references += expressionReferences(it, scoped, compositeType) - scoped }
            statement.post?.let { references += statementReferences(it, scoped, compositeType) }
            statement.rangeClause?.let { range ->
                references += expressionReferences(range.expression, scoped, compositeType) - scoped
                if (range.operator != TokenKind.DEFINE)
                    references += range.targets.flatMap { expressionReferences(it, scoped, compositeType) }.toSet() - scoped
            }
            val bodyLocals = scoped.toMutableSet()
            statement.rangeClause?.takeIf { it.operator == TokenKind.DEFINE }?.targets
                ?.mapNotNullTo(bodyLocals) { (it as? NameExpression)?.name }
            references += blockReferences(statement.body, bodyLocals, compositeType)
            references
        }
        is SwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, compositeType) }
            statement.tag?.let { references += expressionReferences(it, scoped, compositeType) - scoped }
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                clause.expressions?.forEach { references += expressionReferences(it, caseLocals, compositeType) - caseLocals }
                val body = BlockStatement(clause.statements)
                references += blockReferences(body, caseLocals, compositeType)
            }
            references
        }
        is TypeSwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, compositeType) }
            references += expressionReferences(statement.guard.expression, scoped, compositeType) - scoped
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                statement.guard.name?.takeIf { it != "_" }?.let(caseLocals::add)
                references += blockReferences(BlockStatement(clause.statements), caseLocals, compositeType)
            }
            references
        }
        is SelectStatement -> {
            val references = linkedSetOf<String>()
            statement.cases.forEach { clause ->
                val caseLocals = locals.toMutableSet()
                clause.communication?.let { references += statementReferences(it, caseLocals, compositeType) }
                references += blockReferences(BlockStatement(clause.statements), caseLocals, compositeType)
            }
            references
        }
    }

    private fun expressionReferences(
        expression: Expression,
        locals: Set<String> = emptySet(),
        compositeType: (CompositeLiteral) -> GoTypeSyntax?,
        expectedType: GoTypeSyntax? = null
    ): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> expressionReferences(expression.operand, locals, compositeType)
        is BinaryExpression -> expressionReferences(expression.left, locals, compositeType) + expressionReferences(expression.right, locals, compositeType)
        is CallExpression -> expressionReferences(expression.function, locals, compositeType) + expression.arguments.flatMap { expressionReferences(it, locals, compositeType) }
        is SelectorExpression -> expressionReferences(expression.receiver, locals, compositeType)
        is IndexExpression -> expressionReferences(expression.receiver, locals, compositeType) + expressionReferences(expression.index, locals, compositeType)
        is SliceExpression -> expressionReferences(expression.receiver, locals, compositeType) +
            listOfNotNull(expression.low, expression.high).flatMap { expressionReferences(it, locals, compositeType) }
        is TypeAssertionExpression -> expressionReferences(expression.receiver, locals, compositeType)
        is TypeSwitchGuardExpression -> expressionReferences(expression.receiver, locals, compositeType)
        is ParenthesizedExpression -> expressionReferences(expression.expression, locals, compositeType)
        is CompositeLiteral -> compositeElementsReferences(expression.elements, compositeType(expression), locals, compositeType)
        is ElidedCompositeLiteral -> compositeElementsReferences(expression.elements, expectedType, locals, compositeType)
        is FunctionLiteralExpression -> functionLiteralReferences(expression.parameters, expression.resultNames, expression.body, locals, compositeType)
    }

    private fun compositeElementsReferences(
        elements: List<CompositeElement>,
        type: GoTypeSyntax?,
        locals: Set<String>,
        compositeType: (CompositeLiteral) -> GoTypeSyntax?
    ): Set<String> {
        val resolvedType = type?.let { compositeType(CompositeLiteral(it, emptyList())) ?: it }
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
            listOfNotNull(element.key.takeUnless { actual is StructGoType }, element.value)
                .flatMap { expressionReferences(it, locals, compositeType, valueType) }
        }.toSet()
    }

    private fun embeddedFieldName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> type.name
        is PointerGoType -> embeddedFieldName(type.element)
        else -> ""
    }
}
