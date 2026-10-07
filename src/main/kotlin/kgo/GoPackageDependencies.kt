package kgo

/** Collect package-level names referenced by a function during package initialization analysis. */
internal object GoPackageDependencies {
    fun functionReferences(function: FunctionDeclaration): Set<String> {
        val locals = function.parameters.filterNotNull().toMutableSet()
        function.receiver?.name?.let(locals::add)
        function.resultNames.filterNotNull().forEach(locals::add)
        return function.body?.let { blockReferences(it, locals) } ?: emptySet()
    }

    fun functionLiteralReferences(
        parameters: List<ParameterSyntax>,
        resultNames: List<String?>,
        body: BlockStatement,
        captured: Set<String> = emptySet()
    ): Set<String> {
        val locals = (captured + parameters.mapNotNull { it.name } + resultNames.filterNotNull()).toMutableSet()
        return blockReferences(body, locals)
    }

    private fun blockReferences(block: BlockStatement, inherited: Set<String>): Set<String> {
        val locals = inherited.toMutableSet()
        val references = linkedSetOf<String>()
        block.statements.forEach { references += statementReferences(it, locals) }
        return references
    }

    private fun statementReferences(statement: Statement, locals: MutableSet<String>): Set<String> = when (statement) {
        EmptyStatement -> emptySet()
        is LabeledStatement -> statementReferences(statement.statement, locals)
        is DeclarationStatement -> buildSet {
            statement.declarations.forEach { declaration -> when (declaration) {
                is VariableDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is ConstantDeclaration -> {
                    addAll(declaration.values.flatMap { expressionReferences(it, locals) }.toSet() - locals)
                    locals += declaration.names.filter { it != "_" }
                }
                is TypeDeclaration -> locals += declaration.name
                else -> Unit
            } }
        }
        is BlockStatement -> blockReferences(statement, locals)
        is VariableStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals) }.toSet() - locals)
            locals += statement.names.filter { it != "_" }
        }
        is ReturnStatement -> statement.values.flatMapTo(linkedSetOf()) { expressionReferences(it, locals) } - locals
        is ExpressionStatement -> expressionReferences(statement.expression, locals) - locals
        is SendStatement -> (expressionReferences(statement.channel, locals) + expressionReferences(statement.value, locals)) - locals
        is GoStatement -> expressionReferences(statement.call, locals) - locals
        is DeferStatement -> expressionReferences(statement.call, locals) - locals
        is BranchStatement -> emptySet()
        is AssignmentStatement -> buildSet {
            addAll(statement.values.flatMap { expressionReferences(it, locals) }.toSet() - locals)
            if (statement.operator == TokenKind.DEFINE) {
                locals += statement.targets.mapNotNull { (it as? NameExpression)?.name }.filter { it != "_" }
            } else addAll(statement.targets.flatMap { expressionReferences(it, locals) }.toSet() - locals)
        }
        is IncrementStatement -> expressionReferences(statement.target, locals) - locals
        is IfStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped) }
            references += expressionReferences(statement.condition, scoped) - scoped
            references += blockReferences(statement.thenBranch, scoped)
            statement.elseBranch?.let { references += statementReferences(it, scoped.toMutableSet()) }
            references
        }
        is ForStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped) }
            statement.condition?.let { references += expressionReferences(it, scoped) - scoped }
            statement.post?.let { references += statementReferences(it, scoped) }
            statement.rangeClause?.let { range ->
                references += expressionReferences(range.expression, scoped) - scoped
                if (range.operator != TokenKind.DEFINE)
                    references += range.targets.flatMap { expressionReferences(it, scoped) }.toSet() - scoped
            }
            val bodyLocals = scoped.toMutableSet()
            statement.rangeClause?.takeIf { it.operator == TokenKind.DEFINE }?.targets
                ?.mapNotNullTo(bodyLocals) { (it as? NameExpression)?.name }
            references += blockReferences(statement.body, bodyLocals)
            references
        }
        is SwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped) }
            statement.tag?.let { references += expressionReferences(it, scoped) - scoped }
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                clause.expressions?.forEach { references += expressionReferences(it, caseLocals) - caseLocals }
                val body = BlockStatement(clause.statements)
                references += blockReferences(body, caseLocals)
            }
            references
        }
        is TypeSwitchStatement -> {
            val scoped = locals.toMutableSet()
            val references = linkedSetOf<String>()
            statement.init?.let { references += statementReferences(it, scoped) }
            references += expressionReferences(statement.guard.expression, scoped) - scoped
            statement.clauses.forEach { clause ->
                val caseLocals = scoped.toMutableSet()
                statement.guard.name?.takeIf { it != "_" }?.let(caseLocals::add)
                references += blockReferences(BlockStatement(clause.statements), caseLocals)
            }
            references
        }
        is SelectStatement -> {
            val references = linkedSetOf<String>()
            statement.cases.forEach { clause ->
                val caseLocals = locals.toMutableSet()
                clause.communication?.let { references += statementReferences(it, caseLocals) }
                references += blockReferences(BlockStatement(clause.statements), caseLocals)
            }
            references
        }
    }

    private fun expressionReferences(expression: Expression, locals: Set<String> = emptySet()): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> expressionReferences(expression.operand, locals)
        is BinaryExpression -> expressionReferences(expression.left, locals) + expressionReferences(expression.right, locals)
        is CallExpression -> expressionReferences(expression.function, locals) + expression.arguments.flatMap { expressionReferences(it, locals) }
        is SelectorExpression -> expressionReferences(expression.receiver, locals)
        is IndexExpression -> expressionReferences(expression.receiver, locals) + expressionReferences(expression.index, locals)
        is SliceExpression -> expressionReferences(expression.receiver, locals) +
            listOfNotNull(expression.low, expression.high).flatMap { expressionReferences(it, locals) }
        is TypeAssertionExpression -> expressionReferences(expression.receiver, locals)
        is TypeSwitchGuardExpression -> expressionReferences(expression.receiver, locals)
        is ParenthesizedExpression -> expressionReferences(expression.expression, locals)
        is CompositeLiteral -> expression.elements.flatMap {
            listOfNotNull(it.key, it.value).flatMap { value -> expressionReferences(value, locals) }
        }.toSet()
        is ElidedCompositeLiteral -> expression.elements.flatMap {
            listOfNotNull(it.key, it.value).flatMap { value -> expressionReferences(value, locals) }
        }.toSet()
        is FunctionLiteralExpression -> functionLiteralReferences(expression.parameters, expression.resultNames, expression.body, locals)
    }
}
