package kgo

import java.math.BigInteger

class GoTypeError(message: String) : RuntimeException(message)

/** Static checks for the declaration and statement forms currently represented by the AST. */
class TypeChecker {
    private val typeDeclarations = linkedMapOf<String, GoTypeSyntax>()
    private val functions = linkedMapOf<String, FunctionDeclaration>()
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val methods = linkedMapOf<String, FunctionDeclaration>()
    private val packagePaths = linkedMapOf<String, String>()
    private val globals = Scope()
    private var resultTypes: List<GoTypeSyntax> = emptyList()
    private var functionLabels: Map<String, LabelInfo> = emptyMap()
    private var usedLabels: MutableSet<String> = mutableSetOf()
    private var labelBlockPath: List<Any> = emptyList()
    private var blockStatementIndices: Map<BlockStatement, Int> = emptyMap()

    fun check(file: GoFile) {
        file.declarations.filterIsInstance<TypeDeclaration>().forEach { declaration ->
            if (typeDeclarations.putIfAbsent(declaration.name, declaration.type) != null) error("type ${declaration.name} redeclared")
        }
        for (declaration in file.declarations) when (declaration) {
            is TypeDeclaration -> Unit
            is FunctionDeclaration -> {
                val receiver = declaration.receiver
                if (receiver == null) {
                    if (declaration.name == "init") initFunctions += declaration
                    else if (functions.putIfAbsent(declaration.name, declaration) != null) error("function ${declaration.name} redeclared")
                } else {
                    val base = (receiver.type as? PointerGoType)?.element ?: receiver.type
                    val baseName = base as? NamedGoType ?: error("method receiver must be a defined type")
                    if (baseName.name !in typeDeclarations) error("method receiver type ${baseName.name} must be defined in this package")
                    if (underlying(baseName) is InterfaceGoType || underlying(baseName) is PointerGoType)
                        error("invalid method receiver type ${baseName.name}")
                    val key = methodKey(receiver.type, declaration.name)
                    if (methods.putIfAbsent(key, declaration) != null) error("method ${declaration.name} redeclared for ${baseName.name}")
                }
            }
            is ImportDeclaration -> declaration.imports.forEach { spec ->
                val alias = when (spec.alias) {
                    ".", "_" -> null
                    null -> packageName(spec.path)
                    else -> spec.alias
                }
                if (alias != null) packagePaths[alias] = spec.path
            }
            else -> Unit
        }
        file.declarations.filterIsInstance<VariableDeclaration>().forEach { declaration ->
            declaration.names.filter { it != "_" }.forEach { name -> globals.define(name, declaration.type ?: intType) }
        }
        file.declarations.filterIsInstance<ConstantDeclaration>().forEach { declaration ->
            declaration.names.filter { it != "_" }.forEach { name -> globals.define(name, declaration.type ?: untypedInt) }
        }
        functions.forEach { (name, function) -> globals.define(name, functionType(function)) }
        methods.forEach { (key, function) -> globals.define(key, functionType(function)) }

        for (declaration in file.declarations) when (declaration) {
            is VariableDeclaration -> {
                val values = expressionTypes(declaration.values, declaration.names.size, globals)
                if (declaration.type != null) {
                    validateType(declaration.type)
                    values.forEach { requireAssignable(it, declaration.type, "initializer") }
                }
                declaration.names.forEachIndexed { i, name ->
                    if (name != "_") globals.define(name, declaration.type ?: defaultType(values.getOrNull(i) ?: intType))
                }
            }
            is ConstantDeclaration -> {
                val scope = globals.child()
                scope.define("iota", intType)
                val values = expressionTypes(declaration.values, declaration.names.size, scope)
                declaration.type?.let { t -> values.forEach { requireAssignable(it, t, "constant initializer") } }
                declaration.names.forEachIndexed { i, name ->
                    if (name != "_") globals.define(name, declaration.type ?: values.getOrNull(i) ?: intType)
                }
            }
            else -> Unit
        }
        typeDeclarations.keys.forEach { validateType(NamedGoType(it)) }
        file.declarations.filterIsInstance<FunctionDeclaration>().forEach(::checkFunction)
        initFunctions.forEach { if (it.parameters.isNotEmpty() || it.resultTypes.isNotEmpty()) error("init must have no parameters or results") }
        if (file.packageName == "main") checkMain()
    }

    private fun checkMain() {
        val main = functions["main"] ?: error("main function not found")
        if (main.parameters.isNotEmpty() || main.resultTypes.isNotEmpty()) error("main must have no parameters or results")
    }

    private fun checkFunction(function: FunctionDeclaration) {
        val scope = globals.child()
        function.receiver?.let { receiver ->
            validateType(receiver.type)
            receiver.name?.takeIf { it != "_" }?.let { name ->
                if (scope.containsLocal(name)) error("$name redeclared in function signature")
                scope.define(name, receiver.type)
            }
        }
        function.parameters.forEachIndexed { i, name ->
            val type = function.parameterTypes.getOrNull(i) ?: error("missing type for parameter ${name ?: i}")
            validateType(type)
            if (name != null && name != "_") {
                if (scope.containsLocal(name)) error("$name redeclared in function signature")
                scope.define(name, type)
            }
        }
        function.resultTypes.forEach(::validateType)
        val previousResults = resultTypes
        val previousLabels = functionLabels
        val previousUsedLabels = usedLabels
        val previousBlockPath = labelBlockPath
        val previousBlockIndices = blockStatementIndices
        resultTypes = function.resultTypes
        functionLabels = collectLabels(function.body)
        usedLabels = mutableSetOf()
        labelBlockPath = emptyList()
        blockStatementIndices = emptyMap()
        try {
            checkBlock(function.body, scope, reuseScope = true)
            val unused = functionLabels.keys - usedLabels
            if (unused.isNotEmpty()) error("label ${unused.first()} declared and not used")
        } finally {
            resultTypes = previousResults
            functionLabels = previousLabels
            usedLabels = previousUsedLabels
            labelBlockPath = previousBlockPath
            blockStatementIndices = previousBlockIndices
        }
    }

    private fun checkBlock(block: BlockStatement, parent: Scope, reuseScope: Boolean = false) {
        val scope = if (reuseScope) parent else parent.child()
        val previousPath = labelBlockPath
        labelBlockPath = previousPath + block
        try {
            block.statements.forEachIndexed { index, statement ->
                val previousIndices = blockStatementIndices
                blockStatementIndices = previousIndices + (block to index)
                try { checkStatement(statement, scope) } finally { blockStatementIndices = previousIndices }
            }
        }
        finally { labelBlockPath = previousPath }
    }

    private data class LabelInfo(
        val statement: Statement,
        val blockPath: List<Any>,
        val ownerBlock: BlockStatement?,
        val statementIndex: Int?
    )

    private fun collectLabels(body: BlockStatement): Map<String, LabelInfo> {
        val labels = linkedMapOf<String, LabelInfo>()
        fun visit(statement: Statement, path: List<Any>, ownerBlock: BlockStatement?, statementIndex: Int?) {
            when (statement) {
                is LabeledStatement -> {
                    if (labels.putIfAbsent(statement.label, LabelInfo(statement.statement, path, ownerBlock, statementIndex)) != null)
                        error("label ${statement.label} redeclared")
                    visit(statement.statement, path, ownerBlock, statementIndex)
                }
                is BlockStatement -> statement.statements.forEachIndexed { index, child -> visit(child, path + statement, statement, index) }
                is IfStatement -> {
                    statement.init?.let { visit(it, path, ownerBlock, statementIndex) }
                    visit(statement.thenBranch, path, ownerBlock, statementIndex)
                    statement.elseBranch?.let { visit(it, path, ownerBlock, statementIndex) }
                }
                is ForStatement -> {
                    statement.init?.let { visit(it, path, ownerBlock, statementIndex) }
                    statement.post?.let { visit(it, path, ownerBlock, statementIndex) }
                    visit(statement.body, path, ownerBlock, statementIndex)
                }
                is SwitchStatement -> {
                    statement.init?.let { visit(it, path, ownerBlock, statementIndex) }
                    statement.clauses.forEach { clause -> clause.statements.forEach { visit(it, path + clause, ownerBlock, statementIndex) } }
                }
                is TypeSwitchStatement -> {
                    statement.init?.let { visit(it, path, ownerBlock, statementIndex) }
                    statement.clauses.forEach { clause -> clause.statements.forEach { visit(it, path + clause, ownerBlock, statementIndex) } }
                }
                is SelectStatement -> statement.cases.forEach { clause ->
                    clause.communication?.let { visit(it, path + clause, ownerBlock, statementIndex) }
                    clause.statements.forEach { visit(it, path + clause, ownerBlock, statementIndex) }
                }
                else -> Unit
            }
        }
        body.statements.forEachIndexed { index, statement -> visit(statement, listOf(body), body, index) }
        return labels
    }

    private fun isPrefix(prefix: List<Any>, path: List<Any>): Boolean =
        prefix.size <= path.size && prefix.indices.all { prefix[it] === path[it] }

    private fun introducesVariable(statement: Statement): Boolean = when (statement) {
        is VariableStatement -> true
        is AssignmentStatement -> statement.operator == TokenKind.DEFINE
        is DeclarationStatement -> statement.declarations.any { it is VariableDeclaration }
        else -> false
    }

    private fun unwrapLabels(statement: Statement): Statement =
        if (statement is LabeledStatement) unwrapLabels(statement.statement) else statement

    private fun checkStatement(statement: Statement, scope: Scope) {
        when (statement) {
            EmptyStatement -> Unit
            is LabeledStatement -> checkStatement(statement.statement, scope)
            is DeclarationStatement -> statement.declarations.forEach { declaration ->
                when (declaration) {
                    is VariableDeclaration -> {
                        declaration.type?.let(::validateType)
                        val values = expressionTypes(declaration.values, declaration.names.size, scope)
                        if (declaration.type != null) values.forEach { requireAssignable(it, declaration.type, "initializer") }
                        declaration.names.forEachIndexed { i, name ->
                            if (name != "_") {
                                if (scope.containsLocal(name)) error("$name redeclared in this block")
                                scope.define(name, declaration.type ?: defaultType(values.getOrNull(i) ?: intType))
                            }
                        }
                    }
                    is ConstantDeclaration -> {
                        val constants = scope.child().also { it.define("iota", untypedInt) }
                        val values = expressionTypes(declaration.values, declaration.names.size, constants)
                        if (declaration.type != null) values.forEach { requireAssignable(it, declaration.type, "constant initializer") }
                        declaration.names.forEachIndexed { i, name -> if (name != "_") scope.define(name, declaration.type ?: values.getOrNull(i) ?: untypedInt) }
                    }
                    is TypeDeclaration -> typeDeclarations[declaration.name] = declaration.type
                    else -> error("unsupported local declaration")
                }
            }
            is BlockStatement -> checkBlock(statement, scope)
            is VariableStatement -> {
                statement.type?.let(::validateType)
                val values = expressionTypes(statement.values, statement.names.size, scope)
                if (statement.type != null) values.forEach { requireAssignable(it, statement.type, "initializer") }
                statement.names.forEachIndexed { i, name ->
                    if (name != "_") {
                        if (scope.containsLocal(name)) error("$name redeclared in this block")
                        scope.define(name, statement.type ?: defaultType(values.getOrNull(i) ?: intType))
                    }
                }
            }
            is ReturnStatement -> {
                val values = expressionTypes(statement.values, resultTypes.size, scope)
                if (values.size != resultTypes.size) error("return has ${values.size} values, want ${resultTypes.size}")
                values.zip(resultTypes).forEach { (from, to) -> requireAssignable(from, to, "return") }
            }
            is ExpressionStatement -> {
                val expression = statement.expression
                if (expression !is CallExpression) error("expression statement must be a function call")
                callResults(expression, scope)
            }
            is AssignmentStatement -> checkAssignment(statement, scope)
            is IncrementStatement -> {
                val type = expressionType(statement.target, scope)
                if (!isNumeric(type)) error("increment requires numeric operand")
            }
            is IfStatement -> {
                val branchScope = scope.child()
                statement.init?.let { checkStatement(it, branchScope) }
                requireBoolean(expressionType(statement.condition, branchScope), "if condition")
                checkBlock(statement.thenBranch, branchScope)
                statement.elseBranch?.let { checkStatement(it, branchScope) }
            }
            is ForStatement -> {
                val loopScope = scope.child()
                if (statement.rangeClause != null) checkRange(statement.rangeClause, statement.body, loopScope)
                else {
                    statement.init?.let { checkStatement(it, loopScope) }
                    statement.condition?.let { requireBoolean(expressionType(it, loopScope), "for condition") }
                    statement.post?.let { checkStatement(it, loopScope) }
                    checkBlock(statement.body, loopScope)
                }
            }
            is SendStatement -> checkSend(statement, scope)
            is GoStatement -> requireCall(statement.call, scope, "go")
            is DeferStatement -> requireCall(statement.call, scope, "defer")
            is BranchStatement -> when (statement.kind) {
                TokenKind.GOTO -> {
                    val label = statement.label ?: error("goto requires a label")
                    val target = functionLabels[label] ?: error("undefined label $label")
                    if (!isPrefix(target.blockPath, labelBlockPath)) error("goto $label jumps into a block")
                    val owner = target.ownerBlock
                    val sourceIndex = owner?.let { blockStatementIndices[it] }
                    val targetIndex = target.statementIndex
                    if (owner != null && sourceIndex != null && targetIndex != null && targetIndex > sourceIndex &&
                        owner.statements.subList(sourceIndex + 1, targetIndex).any(::introducesVariable)) {
                        error("goto $label jumps over a variable declaration")
                    }
                    usedLabels += label
                }
                TokenKind.BREAK, TokenKind.CONTINUE -> statement.label?.let { label ->
                    val target = functionLabels[label]?.statement ?: error("undefined label $label")
                    val destination = unwrapLabels(target)
                    usedLabels += label
                    if (statement.kind == TokenKind.BREAK && destination !is ForStatement && destination !is SwitchStatement &&
                        destination !is TypeSwitchStatement && destination !is SelectStatement)
                        error("invalid break label $label")
                    if (statement.kind == TokenKind.CONTINUE && destination !is ForStatement) error("invalid continue label $label")
                }
                TokenKind.FALLTHROUGH -> Unit
                else -> Unit
            }
            is SelectStatement -> checkSelect(statement, scope)
            is SwitchStatement -> checkSwitch(statement, scope)
            is TypeSwitchStatement -> checkTypeSwitch(statement, scope)
        }
    }

    private fun checkAssignment(statement: AssignmentStatement, scope: Scope) {
        if (statement.operator == TokenKind.DEFINE) {
            val names = statement.targets.map { (it as? NameExpression)?.name ?: error("short declaration target must be an identifier") }
            val valueTypes = expressionTypes(statement.values, names.size, scope)
            if (valueTypes.size != names.size) error("assignment count mismatch")
            requireUniqueNames(names, "short declaration")
            var added = 0
            names.forEachIndexed { i, name ->
                if (name == "_") return@forEachIndexed
                if (scope.containsLocal(name)) requireAssignable(valueTypes[i], scope.get(name), "assignment")
                else { scope.define(name, defaultType(valueTypes[i])); added++ }
            }
            if (added == 0) error("short declaration must introduce a new variable")
            return
        }
        val leftTypes = statement.targets.map { expressionType(it, scope) }
        val rightTypes = expressionTypes(statement.values, leftTypes.size, scope)
        if (leftTypes.size != rightTypes.size) error("assignment count mismatch")
        leftTypes.zip(rightTypes).forEach { (left, right) -> requireAssignable(right, left, "assignment") }
        if (statement.operator != TokenKind.ASSIGN && statement.operator !in setOf(TokenKind.DEFINE)) {
            if (leftTypes.size != 1 || rightTypes.size != 1) error("compound assignment requires one operand")
            checkBinaryType(leftTypes.single(), compoundOperator(statement.operator), rightTypes.single())
        }
    }

    private fun checkRange(range: RangeClause, body: BlockStatement, scope: Scope) {
        val source = underlying(expressionType(range.expression, scope))
        val keyAndValue = when (source) {
            is ArrayGoType -> intType to source.element
            is PointerGoType -> when (val pointed = underlying(source.element)) {
                is ArrayGoType -> intType to pointed.element
                else -> error("cannot range over this pointer type")
            }
            is SliceGoType -> intType to source.element
            is MapGoType -> source.key to source.value
            is ChannelGoType -> null to source.element
            is NamedGoType -> if (source.name == "string") intType to runeType else error("cannot range over ${source.name}")
            else -> error("cannot range over this type")
        }
        if (source is ChannelGoType && range.targets.size > 1) error("range over channel permits one iteration variable")
        val types = listOfNotNull(keyAndValue.first, keyAndValue.second).take(range.targets.size)
        if (types.size != range.targets.size) error("too many range variables")
        if (range.operator == TokenKind.DEFINE) {
            requireUniqueNames(range.targets.map { (it as? NameExpression)?.name ?: error("range declaration requires identifiers") }, "range declaration")
            range.targets.forEachIndexed { i, target ->
                val name = (target as? NameExpression)?.name ?: error("range declaration requires identifiers")
                if (name != "_") scope.define(name, defaultType(types[i]))
            }
        } else if (range.operator == TokenKind.ASSIGN) {
            range.targets.zip(types).forEach { (target, type) -> requireAssignable(type, expressionType(target, scope), "range assignment") }
        }
        checkBlock(body, scope)
    }

    private fun checkSend(statement: SendStatement, scope: Scope) {
        val channel = underlying(expressionType(statement.channel, scope)) as? ChannelGoType ?: error("send requires a channel")
        if (channel.direction == ChannelDirection.RECEIVE_ONLY) error("cannot send on receive-only channel")
        requireAssignable(expressionType(statement.value, scope), channel.element, "channel send")
    }

    private fun checkSelect(statement: SelectStatement, scope: Scope) {
        statement.cases.forEach { clause ->
            val caseScope = scope.child()
            when (val communication = clause.communication) {
                null -> Unit
                is SendStatement -> checkSend(communication, caseScope)
                is ExpressionStatement -> checkReceive(communication.expression, caseScope)
                is AssignmentStatement -> {
                    val receive = communication.values.singleOrNull() as? UnaryExpression ?: error("select case must receive from a channel")
                    val channel = underlying(expressionType(receive.operand, caseScope)) as? ChannelGoType ?: error("receive requires a channel")
                    if (communication.operator == TokenKind.DEFINE) {
                        val names = communication.targets.map { (it as? NameExpression)?.name ?: error("receive declaration requires identifiers") }
                        if (names.size !in 1..2) error("invalid receive assignment")
                        requireUniqueNames(names, "receive declaration")
                        names.forEachIndexed { i, name ->
                            if (name != "_") caseScope.define(name, if (i == 0) defaultType(channel.element) else boolType)
                        }
                    } else {
                        val targets = communication.targets.map { expressionType(it, caseScope) }
                        if (targets.size !in 1..2) error("invalid receive assignment")
                        requireAssignable(channel.element, targets.first(), "receive assignment")
                        if (targets.size == 2) requireAssignable(boolType, targets[1], "receive status")
                    }
                }
                else -> error("invalid select communication")
            }
            inLabelBlock(clause) { clause.statements.forEach { checkStatement(it, caseScope) } }
        }
    }

    private fun checkReceive(expression: Expression, scope: Scope) {
        val receive = expression as? UnaryExpression ?: error("select receive case must use <-")
        if (receive.operator != TokenKind.ARROW) error("select receive case must use <-")
        if (underlying(expressionType(receive.operand, scope)) !is ChannelGoType) error("receive requires a channel")
    }

    private fun checkSwitch(statement: SwitchStatement, scope: Scope) {
        val switchScope = scope.child()
        statement.init?.let { checkStatement(it, switchScope) }
        val tagType = statement.tag?.let { expressionType(it, switchScope) }
        statement.clauses.forEach { clause ->
            val caseScope = switchScope.child()
            clause.expressions?.forEach { case ->
                val caseType = expressionType(case, caseScope)
                if (tagType != null) {
                    if (!assignable(caseType, tagType) && !assignable(tagType, caseType)) error("case type does not match switch expression")
                } else requireBoolean(caseType, "expressionless switch case")
            }
            inLabelBlock(clause) { clause.statements.forEach { checkStatement(it, caseScope) } }
        }
    }

    private fun checkTypeSwitch(statement: TypeSwitchStatement, scope: Scope) {
        val switchScope = scope.child()
        statement.init?.let { checkStatement(it, switchScope) }
        val interfaceType = expressionType(statement.guard.expression, switchScope)
        if (underlying(interfaceType) !is InterfaceGoType) error("type switch requires an interface operand")
        var sawDefault = false
        var sawNil = false
        val seenTypes = mutableListOf<GoTypeSyntax>()
        statement.clauses.forEach { clause ->
            if (clause.types == null) {
                if (sawDefault) error("multiple default cases in type switch")
                sawDefault = true
            } else clause.types.forEach typeLoop@ { type ->
                if (type == NamedGoType("nil")) {
                    if (sawNil) error("duplicate nil type switch case")
                    sawNil = true
                    return@typeLoop
                }
                validateType(type)
                if (underlying(type) !is InterfaceGoType)
                    requireAssignable(type, interfaceType, "type switch case")
                if (seenTypes.any { sameType(it, type) }) error("duplicate type switch case $type")
                seenTypes += type
            }
            if (clause.statements.lastOrNull() is BranchStatement &&
                (clause.statements.last() as BranchStatement).kind == TokenKind.FALLTHROUGH)
                error("fallthrough is not permitted in a type switch")
            val caseScope = switchScope.child()
            val singleType = clause.types?.singleOrNull()?.takeUnless { it == NamedGoType("nil") }
            if (statement.guard.name != null && statement.guard.name != "_")
                caseScope.define(statement.guard.name, singleType ?: interfaceType)
            inLabelBlock(clause) { clause.statements.forEach { checkStatement(it, caseScope) } }
        }
    }

    private fun inLabelBlock(marker: Any, check: () -> Unit) {
        val previous = labelBlockPath
        labelBlockPath = previous + marker
        try { check() } finally { labelBlockPath = previous }
    }

    private fun expressionTypes(expressions: List<Expression>, arity: Int, scope: Scope): List<GoTypeSyntax> {
        if (expressions.size == 1) {
            val expression = expressions.single()
            if (expression is CallExpression) {
                val results = callResults(expression, scope)
                if (results.size > 1) return results
                if (results.size == 1) return results
            }
            if (expression is UnaryExpression && expression.operator == TokenKind.ARROW) {
                val channel = underlying(expressionType(expression.operand, scope)) as? ChannelGoType ?: error("receive requires a channel")
                return if (arity == 2) listOf(channel.element, boolType) else listOf(channel.element)
            }
            if (expression is TypeAssertionExpression) {
                val asserted = expressionType(expression, scope)
                return if (arity == 2) listOf(asserted, boolType) else listOf(asserted)
            }
            if (expression is IndexExpression && arity == 2) {
                val map = underlying(expressionType(expression.receiver, scope)) as? MapGoType
                if (map != null) return listOf(map.value, boolType)
            }
        }
        return expressions.map { expressionType(it, scope) }
    }

    private fun expressionType(expression: Expression, scope: Scope): GoTypeSyntax = when (expression) {
        is NameExpression -> when (expression.name) {
            "true", "false" -> untypedBool
            "nil" -> nilType
            "iota" -> untypedInt
            else -> scope.getOrNull(expression.name)
                ?: if (typeDeclarations.containsKey(expression.name)) NamedGoType(expression.name)
                else if (isBuiltinType(expression.name)) NamedGoType(expression.name)
                else if (functions.containsKey(expression.name)) functionType(functions.getValue(expression.name))
                else error("undefined: ${expression.name}")
        }
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT, TokenKind.CHAR -> untypedInt
            TokenKind.FLOAT -> untypedFloat
            TokenKind.IMAG -> untypedComplex
            TokenKind.STRING -> untypedString
            else -> error("invalid literal")
        }
        is ParenthesizedExpression -> expressionType(expression.expression, scope)
        is FunctionLiteralExpression -> {
            val literalScope = scope.child()
            expression.parameters.forEach { parameter ->
                validateType(parameter.type)
                val name = parameter.name
                if (name != null && name != "_") {
                    if (literalScope.containsLocal(name)) error("$name redeclared in function signature")
                    literalScope.define(name, parameter.type)
                }
            }
            expression.results.forEach(::validateType)
            val previousResults = resultTypes
            val previousLabels = functionLabels
            val previousUsedLabels = usedLabels
            val previousBlockPath = labelBlockPath
            val previousBlockIndices = blockStatementIndices
            resultTypes = expression.results
            functionLabels = collectLabels(expression.body)
            usedLabels = mutableSetOf()
            labelBlockPath = emptyList()
            blockStatementIndices = emptyMap()
            try {
                checkBlock(expression.body, literalScope, reuseScope = true)
                val unused = functionLabels.keys - usedLabels
                if (unused.isNotEmpty()) error("label ${unused.first()} declared and not used")
            } finally {
                resultTypes = previousResults
                functionLabels = previousLabels
                usedLabels = previousUsedLabels
                labelBlockPath = previousBlockPath
                blockStatementIndices = previousBlockIndices
            }
            FunctionGoType(expression.parameters, expression.results)
        }
        is UnaryExpression -> {
            val operand = expressionType(expression.operand, scope)
            when (expression.operator) {
                TokenKind.ADD, TokenKind.SUB -> { if (!isNumeric(operand)) error("unary operator requires numeric operand"); operand }
                TokenKind.NOT -> { requireBoolean(operand, "!"); boolType }
                TokenKind.XOR -> { if (!isInteger(operand)) error("^ requires integer operand"); operand }
                TokenKind.AND -> PointerGoType(operand)
                TokenKind.MUL -> (underlying(operand) as? PointerGoType)?.element ?: error("* requires pointer operand")
                TokenKind.ARROW -> {
                    val channel = underlying(operand) as? ChannelGoType ?: error("receive requires a channel")
                    if (channel.direction == ChannelDirection.SEND_ONLY) error("cannot receive from send-only channel")
                    channel.element
                }
                else -> error("invalid unary operator")
            }
        }
        is BinaryExpression -> checkBinaryType(expressionType(expression.left, scope), expression.operator, expressionType(expression.right, scope))
        is CallExpression -> {
            val results = callResults(expression, scope)
            if (results.size != 1) error("multiple-value call used in single-value context")
            results.single()
        }
        is SelectorExpression -> selectorType(expression, scope)
        is IndexExpression -> indexType(expression, scope)
        is SliceExpression -> {
            val receiver = underlying(expressionType(expression.receiver, scope))
            when (receiver) {
                is SliceGoType -> receiver
                is ArrayGoType -> SliceGoType(receiver.element)
                is PointerGoType -> when (val pointed = underlying(receiver.element)) {
                    is ArrayGoType -> SliceGoType(pointed.element)
                    else -> error("cannot slice through this pointer")
                }
                is NamedGoType -> if (receiver.name == "string") receiver else error("cannot slice ${receiver.name}")
                else -> error("cannot slice this value")
            }
        }
        is TypeAssertionExpression -> {
            if (underlying(expressionType(expression.receiver, scope)) !is InterfaceGoType)
                error("type assertion requires an interface operand")
            validateType(expression.type)
            expression.type
        }
        is TypeSwitchGuardExpression -> error("type switch guard is only valid in a switch statement")
        is TypeExpression -> expression.type
        is CompositeLiteral -> {
            checkComposite(expression, scope)
            expression.type
        }
    }

    private fun indexType(expression: IndexExpression, scope: Scope): GoTypeSyntax {
        val receiver = underlying(expressionType(expression.receiver, scope))
        val index = expressionType(expression.index, scope)
        return when (receiver) {
            is ArrayGoType -> { requireInteger(index, "array index"); receiver.element }
            is PointerGoType -> when (val pointed = underlying(receiver.element)) {
                is ArrayGoType -> { requireInteger(index, "array index"); pointed.element }
                else -> error("cannot index through this pointer")
            }
            is SliceGoType -> { requireInteger(index, "slice index"); receiver.element }
            is MapGoType -> { requireAssignable(index, receiver.key, "map index"); receiver.value }
            is NamedGoType -> if (receiver.name == "string") { requireInteger(index, "string index"); byteType } else error("cannot index ${receiver.name}")
            else -> error("cannot index this value")
        }
    }

    private fun selectorType(expression: SelectorExpression, scope: Scope): GoTypeSyntax {
        if (expression.receiver is NameExpression && expression.receiver.name in packagePaths) {
            return if (packageName(packagePaths.getValue(expression.receiver.name)) == "fmt") FunctionGoType(emptyList(), emptyList()) else error("unknown imported package")
        }
        val receiverType = expressionType(expression.receiver, scope)
        val receiver = underlying(receiverType)
        if (receiver is InterfaceGoType) {
            return interfaceMethods(receiver).getOrElse(expression.field) { error("undefined interface method ${expression.field}") }
        }
        val struct = when (receiver) {
            is StructGoType -> receiver
            is PointerGoType -> underlying(receiver.element) as? StructGoType
            else -> null
        } ?: error("selector requires struct or package")
        struct.fields.firstOrNull { expression.field in it.names }?.let { return it.type }
        val named = namedType(receiverType) ?: error("selector receiver has no method set")
        val method = methods["$named.${expression.field}"] ?: error("undefined field or method ${expression.field}")
        return functionType(method)
    }

    private fun checkComposite(literal: CompositeLiteral, scope: Scope) {
        val type = underlying(literal.type)
        when (type) {
            is SliceGoType, is ArrayGoType -> {
                val element = if (type is SliceGoType) type.element else (type as ArrayGoType).element
                literal.elements.forEachIndexed { index, item ->
                    item.key?.let { requireInteger(expressionType(it, scope), "composite index") }
                    requireAssignable(expressionType(item.value, scope), element, "composite element")
                }
            }
            is MapGoType -> literal.elements.forEach { item ->
                val key = item.key ?: error("map literal element requires key")
                requireAssignable(expressionType(key, scope), type.key, "map key")
                requireAssignable(expressionType(item.value, scope), type.value, "map value")
            }
            is StructGoType -> {
                val fields = type.fields.flatMap { it.names.map { name -> name to it.type } }.toMap()
                literal.elements.forEachIndexed { i, item ->
                    val fieldType = if (item.key != null) {
                        val key = (item.key as? NameExpression)?.name ?: error("struct field key must be an identifier")
                        fields[key] ?: error("unknown field $key")
                    } else fields.values.elementAtOrNull(i) ?: error("too many struct literal values")
                    requireAssignable(expressionType(item.value, scope), fieldType, "struct field")
                }
            }
            else -> error("invalid composite literal type")
        }
    }

    private fun callResults(call: CallExpression, scope: Scope): List<GoTypeSyntax> {
        val target = call.function
        if (target is SelectorExpression && target.receiver is NameExpression && target.receiver.name in packagePaths) {
            call.arguments.forEach { expressionType(it, scope) }
            return when {
                packageName(packagePaths.getValue(target.receiver.name)) != "fmt" -> error("unknown imported package")
                target.field in setOf("Print", "Println", "Printf", "Fprint", "Fprintln", "Fprintf") -> listOf(intType, NamedGoType("error"))
                target.field.startsWith("S") -> listOf(stringType)
                target.field == "Errorf" -> listOf(NamedGoType("error"))
                else -> error("undefined fmt function ${target.field}")
            }
        }
        if (target is NameExpression && scope.getOrNull(target.name) == null) {
            if (isBuiltinType(target.name) || typeDeclarations.containsKey(target.name)) {
                if (call.arguments.size != 1) error("conversion requires one argument")
                val from = expressionType(call.arguments.single(), scope)
                val to = NamedGoType(target.name)
                if (!convertible(from, to)) error("cannot convert $from to $to")
                return listOf(to)
            }
            val builtin = builtinCall(target.name, call.arguments, scope, call.expandLastArgument)
            if (builtin != null) return builtin
        }
        val functionType = underlying(expressionType(target, scope)) as? FunctionGoType ?: error("called value is not a function")
        val variadic = functionType.parameters.lastOrNull()?.variadic == true
        val fixedCount = if (variadic) functionType.parameters.size - 1 else functionType.parameters.size
        if (call.expandLastArgument && !variadic) error("cannot use ... with non-variadic function")
        if (call.expandLastArgument && call.arguments.size != functionType.parameters.size)
            error("variadic call with ... requires one slice argument")
        if ((!variadic && call.arguments.size != fixedCount) || (variadic && !call.expandLastArgument && call.arguments.size < fixedCount))
            error("wrong number of arguments: got ${call.arguments.size}")
        call.arguments.forEachIndexed { i, arg ->
            val parameter = functionType.parameters.getOrNull(i) ?: functionType.parameters.lastOrNull()
                ?: error("function has no parameters")
            val expected = when {
                call.expandLastArgument && i == call.arguments.lastIndex -> parameter.type
                parameter.variadic -> (parameter.type as? SliceGoType)?.element ?: parameter.type
                else -> parameter.type
            }
            requireAssignable(expressionType(arg, scope), expected, "argument")
        }
        return functionType.results
    }

    private fun builtinCall(name: String, args: List<Expression>, scope: Scope, expandLastArgument: Boolean = false): List<GoTypeSyntax>? {
        val types = args.map { expressionType(it, scope) }
        if (expandLastArgument && name in setOf("print", "println") && args.size != 1)
            error("... requires a single final argument")
        return when (name) {
            "print", "println" -> emptyList()
            "panic" -> { requireCount(name, args, 1); emptyList() }
            "recover" -> { requireCount(name, args, 0); listOf(NamedGoType("interface{}")) }
            "make" -> {
                if (types.isEmpty()) error("make requires a type argument")
                val type = when (val argument = args.first()) {
                    is TypeExpression -> argument.type
                    is NameExpression -> if (isBuiltinType(argument.name) || typeDeclarations.containsKey(argument.name)) NamedGoType(argument.name) else error("make requires a type argument")
                    else -> error("make requires a type argument")
                }
                if (underlying(type) !is ChannelGoType && underlying(type) !is SliceGoType && underlying(type) !is MapGoType) error("make requires slice, map, or channel type")
                listOf(type)
            }
            "new" -> { requireCount(name, args, 1); listOf(PointerGoType(types[0])) }
            "close" -> { requireCount(name, args, 1); if (underlying(types[0]) !is ChannelGoType) error("close requires channel"); emptyList() }
            "len", "cap" -> {
                requireCount(name, args, 1)
                val type = underlying(types[0])
                val string = type is NamedGoType && type.name == "string"
                if ((name == "cap" && string) || (!string && type !is SliceGoType && type !is ArrayGoType && type !is MapGoType && type !is ChannelGoType)) error("$name not defined for this type")
                listOf(intType)
            }
            "append" -> {
                if (types.size < 2) error("append requires a slice and values")
                if (expandLastArgument && types.size != 2) error("append with ... requires one slice argument")
                val slice = underlying(types[0]) as? SliceGoType ?: error("append requires slice")
                if (expandLastArgument) {
                    types.drop(1).dropLast(1).forEach { requireAssignable(it, slice.element, "append") }
                    requireAssignable(types.last(), types[0], "append slice")
                } else types.drop(1).forEach { requireAssignable(it, slice.element, "append") }
                listOf(types[0])
            }
            "copy" -> { requireCount(name, args, 2); listOf(intType) }
            "delete" -> { requireCount(name, args, 2); if (underlying(types[0]) !is MapGoType) error("delete requires a map"); emptyList() }
            "complex" -> {
                requireCount(name, args, 2)
                if (types.any { !isFloatArgument(it) }) error("complex arguments must be floating-point values")
                val first = types[0]
                val second = types[1]
                if (!isUntyped(first) && !isUntyped(second) && !sameType(first, second))
                    error("complex arguments must have the same type")
                val typed = listOf(first, second).firstOrNull { !isUntyped(it) }
                listOf(when {
                    typed == null -> untypedComplex
                    underlying(typed) == NamedGoType("float32") -> NamedGoType("complex64")
                    else -> NamedGoType("complex128")
                })
            }
            "real", "imag" -> {
                requireCount(name, args, 1)
                val type = types.single()
                if (type in setOf(untypedInt, untypedFloat, untypedComplex)) listOf(untypedFloat)
                else when (underlying(type)) {
                    NamedGoType("complex64") -> listOf(NamedGoType("float32"))
                    NamedGoType("complex128") -> listOf(NamedGoType("float64"))
                    else -> error("$name requires a complex argument")
                }
            }
            else -> null
        }
    }

    private fun checkBinaryType(left: GoTypeSyntax, operator: TokenKind, right: GoTypeSyntax): GoTypeSyntax {
        val l = underlying(left); val r = underlying(right)
        if (operator in setOf(TokenKind.LAND, TokenKind.LOR)) {
            requireBoolean(left, "logical operator"); requireBoolean(right, "logical operator"); return boolType
        }
        if (operator in setOf(TokenKind.EQL, TokenKind.NEQ)) {
            if (!assignable(left, right) && !assignable(right, left)) error("incompatible comparison: $left and $right")
            if (left == nilType) {
                if (!isNilable(right)) error("cannot compare nil with $right")
            } else if (right == nilType) {
                if (!isNilable(left)) error("cannot compare $left with nil")
            } else if (!isComparable(left) || !isComparable(right)) {
                error("cannot compare values of type $left and $right")
            }
            return boolType
        }
        if (operator in setOf(TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ)) {
            if (!((isOrderedNumeric(left) && isOrderedNumeric(right)) || (isString(left) && isString(right)))) error("invalid ordered comparison")
            requireSameOperands(left, right)
            return boolType
        }
        if (operator == TokenKind.ADD && isString(left) && isString(right)) { requireSameOperands(left, right); return commonType(left, right) }
        if (operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.MUL, TokenKind.QUO, TokenKind.REM) && !isNumeric(left)) error("arithmetic requires numeric operands")
        if (operator in setOf(TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT, TokenKind.SHL, TokenKind.SHR, TokenKind.REM) && !isInteger(left)) error("operator requires integer operands")
        if (!isNumeric(left) && operator !in setOf(TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT, TokenKind.SHL, TokenKind.SHR, TokenKind.REM)) error("invalid binary operands")
        requireSameOperands(left, right)
        return commonType(left, right)
    }

    private fun requireSameOperands(left: GoTypeSyntax, right: GoTypeSyntax) {
        if (!assignable(left, right) && !assignable(right, left)) error("mismatched operand types: $left and $right")
    }

    private fun commonType(left: GoTypeSyntax, right: GoTypeSyntax): GoTypeSyntax = when {
        isUntyped(left) && !isUntyped(right) -> right
        isUntyped(right) && !isUntyped(left) -> left
        left == untypedInt && right == untypedFloat || right == untypedInt && left == untypedFloat -> untypedFloat
        left == untypedComplex || right == untypedComplex -> untypedComplex
        else -> left
    }

    private fun requireAssignable(from: GoTypeSyntax, to: GoTypeSyntax, context: String) {
        if (!assignable(from, to)) error("cannot use $from as $to in $context")
    }

    private fun assignable(from: GoTypeSyntax, to: GoTypeSyntax): Boolean {
        if (from == to) return true
        if (from == nilType) return isNilable(to)
        val requiredMethods = (underlying(to) as? InterfaceGoType)?.let(::interfaceMethods)
        if (requiredMethods != null) {
            val availableMethods = methodSet(from)
            return requiredMethods.all { (name, signature) -> availableMethods[name]?.let { sameSignature(it, signature) } == true }
        }
        if (isUntyped(from)) {
            val f = underlying(from)
            val t = underlying(to)
            return when {
                f == untypedInt -> isNumeric(to) || isUntyped(to)
                f == untypedFloat -> t is NamedGoType && t.name.startsWith("float") || t is NamedGoType && t.name.startsWith("complex")
                f == untypedComplex -> t is NamedGoType && t.name.startsWith("complex")
                f == untypedString -> isString(to)
                f == untypedBool -> isBoolean(to)
                else -> false
            }
        }
        if (isNamed(from) && isNamed(to)) return false
        return sameType(underlying(from), underlying(to)) && (!isNamed(from) || !isNamed(to))
    }

    private fun convertible(from: GoTypeSyntax, to: GoTypeSyntax): Boolean = assignable(from, to) ||
        (isNumeric(from) && isNumeric(to)) || (isString(from) && (isString(to) || isInteger(to))) || (isInteger(from) && isString(to))

    private fun validateType(type: GoTypeSyntax, active: Set<String> = emptySet(), indirect: Boolean = false) {
        when (type) {
            is NamedGoType -> {
                if (!isBuiltinType(type.name) && type.name !in typeDeclarations) error("undefined type ${type.name}")
                if (type.name in active) {
                    if (indirect) return
                    error("invalid recursive type ${type.name}")
                }
                typeDeclarations[type.name]?.let { validateType(it, active + type.name) }
            }
            is QualifiedGoType -> if (type.packageName !in packagePaths) error("unknown package ${type.packageName}")
            is PointerGoType -> validateType(type.element, active, true)
            is SliceGoType -> validateType(type.element, active, true)
            is ArrayGoType -> { expressionType(type.length, globals); validateType(type.element, active) }
            is MapGoType -> { validateType(type.key, active); validateType(type.value, active, true); if (!isComparable(type.key)) error("invalid map key type") }
            is ChannelGoType -> validateType(type.element, active, true)
            is StructGoType -> type.fields.forEach { validateType(it.type, active) }
            is InterfaceGoType -> {
                val names = mutableSetOf<String>()
                type.embeddedTypes.forEach {
                    validateType(it, active)
                    if (underlying(it) !is InterfaceGoType) error("embedded interface element must be an interface")
                }
                type.methods.forEach { method ->
                    if (!names.add(method.name)) error("duplicate interface method ${method.name}")
                    method.parameters.forEach { validateType(it.type, active) }
                    method.results.forEach { validateType(it, active) }
                }
                interfaceMethods(type)
            }
            is FunctionGoType -> { type.parameters.forEach { validateType(it.type, active) }; type.results.forEach { validateType(it, active) } }
        }
    }

    private fun packageName(path: String): String = path.removeSurrounding("\"").substringAfterLast('/')
    private fun functionType(function: FunctionDeclaration) = FunctionGoType(function.parameterTypes.mapIndexed { i, t ->
        ParameterSyntax(function.parameters.getOrNull(i), t, function.variadic && i == function.parameterTypes.lastIndex)
    }, function.resultTypes)
    private fun namedType(type: GoTypeSyntax): String? = when (type) {
        is NamedGoType -> type.name
        is PointerGoType -> namedType(type.element)
        else -> null
    }
    private fun methodKey(type: GoTypeSyntax, name: String): String = "${namedType(type) ?: type}.$name"
    private fun interfaceMethods(type: GoTypeSyntax, seen: Set<String> = emptySet()): Map<String, FunctionGoType> {
        val actual = underlying(type)
        val iface = actual as? InterfaceGoType ?: return emptyMap()
        val result = linkedMapOf<String, FunctionGoType>()
        iface.embeddedTypes.forEach { embedded ->
            val key = embedded.toString()
            if (key in seen) error("invalid recursive interface embedding")
            interfaceMethods(embedded, seen + key).forEach { (name, signature) ->
                val previous = result.putIfAbsent(name, signature)
                if (previous != null && !sameSignature(previous, signature)) error("conflicting interface method $name")
            }
        }
        iface.methods.forEach { method ->
            val signature = FunctionGoType(method.parameters, method.results)
            val previous = result.putIfAbsent(method.name, signature)
            if (previous != null && !sameSignature(previous, signature)) error("conflicting interface method ${method.name}")
        }
        return result
    }

    private fun methodSet(type: GoTypeSyntax): Map<String, FunctionGoType> {
        val actual = underlying(type)
        if (actual is InterfaceGoType) return interfaceMethods(actual)
        val pointer = type is PointerGoType
        val baseName = namedType(type) ?: return emptyMap()
        val result = linkedMapOf<String, FunctionGoType>()
        methods.values.forEach { method ->
            val receiverType = method.receiver?.type ?: return@forEach
            if (namedType(receiverType) != baseName) return@forEach
            if (receiverType is PointerGoType && !pointer) return@forEach
            result[method.name] = functionType(method)
        }
        return result
    }

    private fun sameSignature(left: FunctionGoType, right: FunctionGoType): Boolean =
        left.parameters.size == right.parameters.size && left.results.size == right.results.size &&
            left.parameters.zip(right.parameters).all { (a, b) -> sameType(a.type, b.type) && a.variadic == b.variadic } &&
            left.results.zip(right.results).all { (a, b) -> sameType(a, b) }

    private fun sameType(left: GoTypeSyntax, right: GoTypeSyntax): Boolean {
        if (left == right) return true
        return when {
            left is QualifiedGoType && right is QualifiedGoType -> left.packageName == right.packageName && left.name == right.name
            left is PointerGoType && right is PointerGoType -> sameType(left.element, right.element)
            left is SliceGoType && right is SliceGoType -> sameType(left.element, right.element)
            left is ArrayGoType && right is ArrayGoType -> sameArrayLength(left.length, right.length) && sameType(left.element, right.element)
            left is MapGoType && right is MapGoType -> sameType(left.key, right.key) && sameType(left.value, right.value)
            left is ChannelGoType && right is ChannelGoType -> left.direction == right.direction && sameType(left.element, right.element)
            left is StructGoType && right is StructGoType -> {
                val leftFields = left.fields.flatMap { field -> (field.names.ifEmpty { listOf("") }).map { Triple(it, field.type, field.tag) } }
                val rightFields = right.fields.flatMap { field -> (field.names.ifEmpty { listOf("") }).map { Triple(it, field.type, field.tag) } }
                leftFields.size == rightFields.size && leftFields.zip(rightFields).all { (a, b) ->
                    a.first == b.first && a.third == b.third && sameType(a.second, b.second)
                }
            }
            left is InterfaceGoType && right is InterfaceGoType -> {
                val leftMethods = interfaceMethods(left)
                val rightMethods = interfaceMethods(right)
                leftMethods.keys == rightMethods.keys && leftMethods.all { (name, signature) ->
                    rightMethods[name]?.let { sameSignature(signature, it) } == true
                }
            }
            left is FunctionGoType && right is FunctionGoType -> sameSignature(left, right)
            else -> false
        }
    }

    private fun sameArrayLength(left: Expression, right: Expression): Boolean {
        val leftValue = constantInteger(left)
        val rightValue = constantInteger(right)
        return if (leftValue != null && rightValue != null) leftValue == rightValue
        else arrayLengthSyntax(left) == arrayLengthSyntax(right)
    }

    private fun constantInteger(expression: Expression): BigInteger? = when (expression) {
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> parseIntegerConstant(expression.token.lexeme)
            TokenKind.CHAR -> decodeCharacterConstant(expression.token.lexeme)
            else -> null
        }
        is ParenthesizedExpression -> constantInteger(expression.expression)
        is UnaryExpression -> constantInteger(expression.operand)?.let { value -> when (expression.operator) {
            TokenKind.ADD -> value
            TokenKind.SUB -> value.negate()
            TokenKind.XOR -> value.not()
            else -> null
        } }
        is BinaryExpression -> {
            val left = constantInteger(expression.left)
            val right = constantInteger(expression.right)
            if (left == null || right == null) null else runCatching { when (expression.operator) {
                TokenKind.ADD -> left + right
                TokenKind.SUB -> left - right
                TokenKind.MUL -> left * right
                TokenKind.QUO -> left / right
                TokenKind.REM -> left % right
                TokenKind.AND -> left.and(right)
                TokenKind.OR -> left.or(right)
                TokenKind.XOR -> left.xor(right)
                TokenKind.AND_NOT -> left.andNot(right)
                TokenKind.SHL -> left.shiftLeft(right.intValueExact())
                TokenKind.SHR -> left.shiftRight(right.intValueExact())
                else -> return@runCatching null
            } }.getOrNull()
        }
        else -> null
    }

    private fun parseIntegerConstant(text: String): BigInteger? = runCatching {
        val literal = text.replace("_", "")
        when {
            literal.startsWith("0x", true) -> BigInteger(literal.drop(2), 16)
            literal.length > 1 && literal.startsWith('0') -> BigInteger(literal.drop(1), 8)
            else -> BigInteger(literal, 10)
        }
    }.getOrNull()

    private fun decodeCharacterConstant(text: String): BigInteger? = runCatching {
        BigInteger(characterCodePoint(text).toString())
    }.getOrNull()

    private fun characterCodePoint(text: String): Int {
        val body = text.substring(1, text.length - 1)
        if (!body.startsWith("\\")) return body.codePointAt(0)
        val escape = body.drop(1)
        return when (escape.first()) {
            'a' -> 7
            'b' -> 8
            'f' -> 12
            'n' -> 10
            'r' -> 13
            't' -> 9
            'v' -> 11
            '\\' -> 92
            '\'' -> 39
            '"' -> 34
            'x' -> escape.drop(1).toInt(16)
            'u' -> escape.drop(1).toInt(16)
            'U' -> escape.drop(1).toLong(16).toInt()
            in '0'..'7' -> escape.take(3).toInt(8)
            else -> error("invalid character escape")
        }
    }

    private fun arrayLengthSyntax(expression: Expression): Any = when (expression) {
        is LiteralExpression -> expression.token.kind to expression.token.lexeme
        is NameExpression -> "name" to expression.name
        is UnaryExpression -> "unary" to (expression.operator to arrayLengthSyntax(expression.operand))
        is BinaryExpression -> "binary" to (expression.operator to (arrayLengthSyntax(expression.left) to arrayLengthSyntax(expression.right)))
        is ParenthesizedExpression -> arrayLengthSyntax(expression.expression)
        else -> expression
    }

    private fun underlying(type: GoTypeSyntax, seen: Set<String> = emptySet()): GoTypeSyntax = when (type) {
        is NamedGoType -> typeDeclarations[type.name]?.let { if (type.name in seen) type else underlying(it, seen + type.name) }
            ?: if (type.name == "error") errorInterfaceType else type
        else -> type
    }
    private fun isNamed(type: GoTypeSyntax) = type is NamedGoType && !type.name.startsWith("#")
    private fun isUntyped(type: GoTypeSyntax) = type is NamedGoType && type.name.startsWith("#untyped-")
    private fun isBuiltinType(name: String) = name in builtinTypes || name == "error"
    private fun isNumeric(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt, untypedFloat, untypedComplex -> true
        is NamedGoType -> t.name in integerNames || t.name in floatNames || t.name in complexNames
        else -> false
    }
    private fun isFloatArgument(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt, untypedFloat -> true
        is NamedGoType -> t.name in floatNames
        else -> false
    }
    private fun isOrderedNumeric(type: GoTypeSyntax): Boolean = isInteger(type) || when (val t = underlying(type)) {
        untypedFloat -> true
        is NamedGoType -> t.name in floatNames
        else -> false
    }
    private fun isInteger(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt -> true
        is NamedGoType -> t.name in integerNames
        else -> false
    }
    private fun isString(type: GoTypeSyntax) = underlying(type) == stringType || type == untypedString
    private fun isBoolean(type: GoTypeSyntax) = underlying(type) == boolType || type == untypedBool
    private fun isNilable(type: GoTypeSyntax) = when (underlying(type)) { is PointerGoType, is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType, is InterfaceGoType -> true; else -> false }
    private fun isComparable(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        is SliceGoType, is MapGoType, is FunctionGoType -> false
        is ArrayGoType -> isComparable(t.element)
        is StructGoType -> t.fields.all { isComparable(it.type) }
        else -> true
    }
    private fun defaultType(type: GoTypeSyntax) = when (type) {
        untypedInt -> intType
        untypedFloat -> NamedGoType("float64")
        untypedComplex -> NamedGoType("complex128")
        untypedString -> stringType
        untypedBool -> boolType
        else -> type
    }
    private fun requireBoolean(type: GoTypeSyntax, context: String) { if (!isBoolean(type)) error("$context must be boolean") }
    private fun requireInteger(type: GoTypeSyntax, context: String) { if (!isInteger(type)) error("$context must be integer") }
    private fun requireCall(expression: Expression, scope: Scope, context: String) {
        if (expression !is CallExpression) error("$context requires function call")
        callResults(expression, scope)
    }
    private fun requireCount(name: String, args: List<Expression>, count: Int) { if (args.size != count) error("$name expects $count arguments") }
    private fun compoundOperator(operator: TokenKind) = when (operator) {
        TokenKind.ADD_ASSIGN -> TokenKind.ADD; TokenKind.SUB_ASSIGN -> TokenKind.SUB; TokenKind.MUL_ASSIGN -> TokenKind.MUL
        TokenKind.QUO_ASSIGN -> TokenKind.QUO; TokenKind.REM_ASSIGN -> TokenKind.REM; TokenKind.AND_ASSIGN -> TokenKind.AND
        TokenKind.OR_ASSIGN -> TokenKind.OR; TokenKind.XOR_ASSIGN -> TokenKind.XOR; TokenKind.SHL_ASSIGN -> TokenKind.SHL
        TokenKind.SHR_ASSIGN -> TokenKind.SHR; TokenKind.AND_NOT_ASSIGN -> TokenKind.AND_NOT
        else -> error("invalid compound assignment")
    }
    private fun error(message: String): Nothing = throw GoTypeError(message)

    private fun requireUniqueNames(names: List<String>, context: String) {
        val declared = names.filter { it != "_" }
        if (declared.size != declared.toSet().size) error("repeated name in $context")
    }

    private class Scope(private val parent: Scope? = null) {
        private val values = linkedMapOf<String, GoTypeSyntax>()
        fun child() = Scope(this)
        fun define(name: String, type: GoTypeSyntax) { values[name] = type }
        fun containsLocal(name: String) = name in values
        fun get(name: String): GoTypeSyntax = getOrNull(name) ?: throw GoTypeError("undefined: $name")
        fun getOrNull(name: String): GoTypeSyntax? = values[name] ?: parent?.getOrNull(name)
    }

    companion object {
        private val untypedInt = NamedGoType("#untyped-int")
        private val untypedFloat = NamedGoType("#untyped-float")
        private val untypedComplex = NamedGoType("#untyped-complex")
        private val untypedString = NamedGoType("#untyped-string")
        private val untypedBool = NamedGoType("#untyped-bool")
        private val nilType = NamedGoType("#nil")
        private val intType = NamedGoType("int")
        private val byteType = NamedGoType("byte")
        private val runeType = NamedGoType("rune")
        private val boolType = NamedGoType("bool")
        private val stringType = NamedGoType("string")
        private val errorInterfaceType = InterfaceGoType(listOf(InterfaceMethodSyntax("Error", emptyList(), listOf(stringType))))
        private val integerNames = setOf("int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune")
        private val floatNames = setOf("float32", "float64")
        private val complexNames = setOf("complex64", "complex128")
        private val builtinTypes = integerNames + floatNames + complexNames + setOf("bool", "string")
    }
}
