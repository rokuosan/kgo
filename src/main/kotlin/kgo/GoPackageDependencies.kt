package kgo

/** Collect package-level names referenced by a function during package initialization analysis. */
internal object GoPackageDependencies {
    fun functionReferences(
        function: FunctionDeclaration,
        isStructLiteral: (CompositeLiteral) -> Boolean = { it.type is StructGoType }
    ): Set<String> {
        val locals = function.parameters.filterNotNull().toMutableSet()
        function.receiver?.name?.let(locals::add)
        function.resultNames.filterNotNull().forEach(locals::add)
        return function.body?.let { blockReferences(it, locals, isStructLiteral) } ?: emptySet()
    }

    fun functionLiteralReferences(
        parameters: List<ParameterSyntax>,
        resultNames: List<String?>,
        body: BlockStatement,
        captured: Set<String> = emptySet(),
        isStructLiteral: (CompositeLiteral) -> Boolean = { it.type is StructGoType }
    ): Set<String> {
        val locals = (captured + parameters.mapNotNull { it.name } + resultNames.filterNotNull()).toMutableSet()
        return blockReferences(body, locals, isStructLiteral)
    }

    private fun blockReferences(
        block: BlockStatement,
        inherited: Set<String>,
        isStructLiteral: (CompositeLiteral) -> Boolean
    ): Set<String> {
        val locals = inherited.toMutableSet()
        val references = linkedSetOf<String>()
        block.statements.forEach { references += statementReferences(it, locals, isStructLiteral) }
        return references
    }

    private fun statementReferences(
        statement: Statement,
        locals: MutableSet<String>,
        isStructLiteral: (CompositeLiteral) -> Boolean
    ): Set<String> = when (statement) {
        EmptyStatement -> emptySet()
        is LabeledStatement -> statementReferences(statement.statement, locals, isStructLiteral)
        is DeclarationStatement -> buildSet {
            statement.declarations.forEach { declaration -> when (declaration) {
                is VariableDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals, isStructLiteral) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is ConstantDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals, isStructLiteral) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is TypeDeclaration -> locals += declaration.name
                else -> Unit
            } }
        }
        is BlockStatement -> blockReferences(statement, locals, isStructLiteral)
        is VariableStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals, isStructLiteral) }.toSet() - locals)
            locals += statement.names.filter { it != "_" }
        }
        is ReturnStatement -> statement.values.flatMapTo(linkedSetOf()) { expressionReferences(it, locals, isStructLiteral) } - locals
        is ExpressionStatement -> expressionReferences(statement.expression, locals, isStructLiteral) - locals
        is SendStatement -> (expressionReferences(statement.channel, locals, isStructLiteral) + expressionReferences(statement.value, locals, isStructLiteral)) - locals
        is GoStatement -> expressionReferences(statement.call, locals, isStructLiteral) - locals
        is DeferStatement -> expressionReferences(statement.call, locals, isStructLiteral) - locals
        is BranchStatement -> emptySet()
        is AssignmentStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals, isStructLiteral) }.toSet() - locals)
            if (statement.operator == TokenKind.DEFINE) {
                locals += statement.targets.mapNotNull { (it as? NameExpression)?.name }.filter { it != "_" }
            } else addAll(statement.targets.flatMap { expressionReferences(it, locals, isStructLiteral) }.toSet() - locals)
        }
        is IncrementStatement -> expressionReferences(statement.target, locals, isStructLiteral) - locals
        is IfStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, isStructLiteral) }
            references += expressionReferences(statement.condition, scoped, isStructLiteral) - scoped
            references += blockReferences(statement.thenBranch, scoped, isStructLiteral)
            statement.elseBranch?.let { references += statementReferences(it, scoped.toMutableSet(), isStructLiteral) }
            references
        }
        is ForStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, isStructLiteral) }
            statement.condition?.let { references += expressionReferences(it, scoped, isStructLiteral) - scoped }
            statement.post?.let { references += statementReferences(it, scoped, isStructLiteral) }
            statement.rangeClause?.let { range ->
                references += expressionReferences(range.expression, scoped, isStructLiteral) - scoped
                if (range.operator != TokenKind.DEFINE)
                    references += range.targets.flatMap { expressionReferences(it, scoped, isStructLiteral) }.toSet() - scoped
            }
            val bodyLocals = scoped.toMutableSet()
            statement.rangeClause?.takeIf { it.operator == TokenKind.DEFINE }?.targets
                ?.mapNotNullTo(bodyLocals) { (it as? NameExpression)?.name }
            references += blockReferences(statement.body, bodyLocals, isStructLiteral)
            references
        }
        is SwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, isStructLiteral) }
            statement.tag?.let { references += expressionReferences(it, scoped, isStructLiteral) - scoped }
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                clause.expressions?.forEach { references += expressionReferences(it, caseLocals, isStructLiteral) - caseLocals }
                val body = BlockStatement(clause.statements)
                references += blockReferences(body, caseLocals, isStructLiteral)
            }
            references
        }
        is TypeSwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped, isStructLiteral) }
            references += expressionReferences(statement.guard.expression, scoped, isStructLiteral) - scoped
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                statement.guard.name?.takeIf { it != "_" }?.let(caseLocals::add)
                references += blockReferences(BlockStatement(clause.statements), caseLocals, isStructLiteral)
            }
            references
        }
        is SelectStatement -> {
            val references = linkedSetOf<String>()
            statement.cases.forEach { clause ->
                val caseLocals = locals.toMutableSet()
                clause.communication?.let { references += statementReferences(it, caseLocals, isStructLiteral) }
                references += blockReferences(BlockStatement(clause.statements), caseLocals, isStructLiteral)
            }
            references
        }
    }

    private fun expressionReferences(
        expression: Expression,
        locals: Set<String> = emptySet(),
        isStructLiteral: (CompositeLiteral) -> Boolean
    ): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> expressionReferences(expression.operand, locals, isStructLiteral)
        is BinaryExpression -> expressionReferences(expression.left, locals, isStructLiteral) + expressionReferences(expression.right, locals, isStructLiteral)
        is CallExpression -> expressionReferences(expression.function, locals, isStructLiteral) + expression.arguments.flatMap { expressionReferences(it, locals, isStructLiteral) }
        is SelectorExpression -> expressionReferences(expression.receiver, locals, isStructLiteral)
        is IndexExpression -> expressionReferences(expression.receiver, locals, isStructLiteral) + expressionReferences(expression.index, locals, isStructLiteral)
        is SliceExpression -> expressionReferences(expression.receiver, locals, isStructLiteral) +
            listOfNotNull(expression.low, expression.high).flatMap { expressionReferences(it, locals, isStructLiteral) }
        is TypeAssertionExpression -> expressionReferences(expression.receiver, locals, isStructLiteral)
        is TypeSwitchGuardExpression -> expressionReferences(expression.receiver, locals, isStructLiteral)
        is ParenthesizedExpression -> expressionReferences(expression.expression, locals, isStructLiteral)
        is CompositeLiteral -> expression.elements.flatMap {
            listOfNotNull(it.key.takeUnless { isStructLiteral(expression) }, it.value)
                .flatMap { value -> expressionReferences(value, locals, isStructLiteral) }
        }.toSet()
        is ElidedCompositeLiteral -> expression.elements.flatMap {
            listOfNotNull(it.key, it.value).flatMap { value -> expressionReferences(value, locals, isStructLiteral) }
        }.toSet()
        is FunctionLiteralExpression -> functionLiteralReferences(expression.parameters, expression.resultNames, expression.body, locals, isStructLiteral)
    }
}
