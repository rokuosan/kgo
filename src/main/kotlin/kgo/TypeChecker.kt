package kgo

import java.math.BigInteger
import java.util.Collections
import java.util.IdentityHashMap
import java.util.concurrent.atomic.AtomicInteger

class GoTypeError(message: String) : RuntimeException(message)

/** Static checks for the declaration and statement forms currently represented by the AST. */
class TypeChecker {
    private val typeDeclarations = linkedMapOf<String, GoTypeSyntax>()
    private val functions = linkedMapOf<String, FunctionDeclaration>()
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val methods = linkedMapOf<String, FunctionDeclaration>()
    private val packagePaths = linkedMapOf<String, String>()
    private var usedPackageAliases = mutableSetOf<String>()
    private val usedPackageAliasesByFile = IdentityHashMap<GoFile, MutableSet<String>>()
    private val nextLocalTypeIdentity = AtomicInteger()
    private val terminatingPanicCalls = Collections.newSetFromMap(IdentityHashMap<CallExpression, Boolean>())
    private val globals = Scope()
    private var resultTypes: List<GoTypeSyntax> = emptyList()
    private var resultNames: List<String?> = emptyList()
    private var functionLabels: Map<String, LabelInfo> = emptyMap()
    private var usedLabels: MutableSet<String> = mutableSetOf()
    private var labelBlockPath: List<Any> = emptyList()
    private var blockStatementIndices: Map<BlockStatement, Int> = emptyMap()

    fun check(file: GoFile) = checkFiles(listOf(file))

    fun checkFiles(files: List<GoFile>) {
        usedPackageAliasesByFile.clear()
        if (files.isEmpty()) error("package has no source files")
        val packageName = files.first().packageName
        if (packageName == "_") error("package name cannot be _")
        if (files.any { it.packageName != packageName }) error("source files declare different package names")
        val declarations = files.flatMap { file -> file.declarations.map { file to it } }
        val packageIdentifiers = linkedSetOf<String>()
        declarations.forEach { (_, declaration) ->
            if (declaration !is FunctionDeclaration && "init" in when (declaration) {
                    is VariableDeclaration -> declaration.names
                    is ConstantDeclaration -> declaration.names
                    is TypeDeclaration -> listOf(declaration.name)
                    else -> emptyList()
                }) error("init may only be used for function declarations in the package block")
            val names = when (declaration) {
                is VariableDeclaration -> declaration.names
                is ConstantDeclaration -> declaration.names
                is TypeDeclaration -> listOf(declaration.name)
                is FunctionDeclaration -> if (declaration.receiver == null && declaration.name != "init")
                    listOf(declaration.name) else emptyList()
                else -> emptyList()
            }
            names.filter { it != "_" }.forEach { name ->
                if (!packageIdentifiers.add(name)) error("$name redeclared in package block")
            }
        }
        declarations.mapNotNull { (file, declaration) ->
            (declaration as? TypeDeclaration)?.let { file to it }
        }.forEach { (_, declaration) ->
            if (typeDeclarations.putIfAbsent(declaration.name, declaration.type) != null) error("type ${declaration.name} redeclared")
        }
        for ((_, declaration) in declarations) when (declaration) {
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
            else -> Unit
        }
        val globalVariables = declarations.mapNotNull { (_, declaration) -> declaration as? VariableDeclaration }
        globalVariables.forEach { declaration ->
            declaration.names.filter { it != "_" }.forEach { name -> globals.define(name, declaration.type ?: intType) }
        }
        declarations.mapNotNull { (_, declaration) -> declaration as? ConstantDeclaration }.forEach { declaration ->
            declaration.names.filter { it != "_" }.forEach { name ->
                globals.define(name, declaration.type ?: untypedInt, isConstant = true)
            }
        }
        functions.forEach { (name, function) -> globals.define(name, functionType(function), isFunction = true) }
        methods.forEach { (key, function) -> globals.define(key, functionType(function)) }
        files.forEach { withFileImports(it) {} }

        val globalConstants = declarations.flatMap { (file, declaration) ->
            (declaration as? ConstantDeclaration)?.let { constant ->
                if (constant.names.size != constant.values.size) error("constant initializer count mismatch")
                constant.names.indices.map { GlobalConstantBinding(file, constant, it) }
            }.orEmpty()
        }
        for (binding in globalConstantInitializationOrder(globalConstants)) {
            withFileImports(binding.file) {
                val declaration = binding.declaration
                val name = declaration.names[binding.index]
                val expression = declaration.values[binding.index]
                val scope = globals.child().also {
                    it.define("iota", untypedInt, BigInteger.valueOf(declaration.iotaIndex.toLong()), isConstant = true)
                }
                val type = expressionTypes(listOf(expression), 1, scope).singleOrNull()
                    ?: error("constant initializer count mismatch")
                if (!isConstantExpression(expression, scope)) error("constant initializer is not constant")
                declaration.type?.let { declaredType ->
                    validateType(declaredType)
                    requireAssignable(type, declaredType, "constant initializer", expression, scope)
                }
                if (name != "_") globals.define(
                    name, declaration.type ?: type,
                    constantInteger(expression, scope), constantStringLength(expression, scope), isConstant = true,
                    rationalConstant = constantRational(expression, scope),
                    stringIdentity = constantStringIdentity(expression, scope),
                    booleanConstant = constantBoolean(expression, scope)
                )
            }
        }
        val variableFiles = IdentityHashMap<VariableDeclaration, GoFile>()
        declarations.forEach { (file, declaration) ->
            (declaration as? VariableDeclaration)?.let { variableFiles[it] = file }
        }
        for (declaration in globalVariableInitializationOrder(globalVariables)) {
            val sourceFile = variableFiles.getValue(declaration)
            withFileImports(sourceFile) {
                val values = expressionTypes(declaration.values, declaration.names.size, globals)
                if (declaration.values.isNotEmpty() && values.size != declaration.names.size)
                    error("initializer count mismatch")
                if (declaration.type != null) {
                    validateType(declaration.type)
                    requireAssignableValues(values, declaration.values, declaration.type, "initializer", globals)
                } else requireDefaultIntegerValues(values, declaration.values, "initializer", globals)
                declaration.names.forEachIndexed { i, name ->
                    if (name != "_") globals.define(name, declaration.type ?: defaultType(values.getOrNull(i) ?: intType))
                }
            }
        }
        for ((sourceFile, declaration) in declarations) {
            if (declaration is TypeDeclaration) withFileImports(sourceFile) {
                validateType(NamedGoType(declaration.name))
            }
        }
        for ((sourceFile, declaration) in declarations) {
            if (declaration is FunctionDeclaration) withFileImports(sourceFile) { checkFunction(declaration) }
        }
        files.forEach { file ->
            val usedAliases = usedPackageAliasesByFile[file].orEmpty()
            file.declarations.filterIsInstance<ImportDeclaration>().flatMap { it.imports }.forEach { spec ->
                val alias = when (spec.alias) {
                    null -> runCatching { decodeGoStringLiteralBytes(spec.path).toString(Charsets.UTF_8).substringAfterLast('/') }.getOrNull()
                    else -> spec.alias
                }
                if (alias != null && alias != "_" && alias !in usedAliases)
                    error("imported package $alias is not used")
            }
        }
        initFunctions.forEach { if (it.parameters.isNotEmpty() || it.resultTypes.isNotEmpty()) error("init must have no parameters or results") }
        if (packageName == "main") checkMain()
    }

    private fun <T> withFileImports(file: GoFile, action: () -> T): T {
        val previous = packagePaths.toMap()
        val previousUsedAliases = usedPackageAliases
        usedPackageAliases = mutableSetOf()
        return try {
            packagePaths.clear()
            val importedNames = mutableSetOf<String>()
            val imports = file.declarations.filterIsInstance<ImportDeclaration>().flatMap { it.imports }
            val importedPaths = mutableSetOf<String>()
            imports.forEach { spec ->
                val path = try {
                    decodeGoStringLiteralBytes(spec.path).toString(Charsets.UTF_8)
                } catch (failure: RuntimeGoError) {
                    error("invalid import path: ${failure.message}")
                }
                if (path.isEmpty()) error("import path cannot be empty")
                if (!importedPaths.add(canonicalGoStringLiteral(spec.path)))
                    error("package $path imported more than once in this file")
                val alias = when (spec.alias) {
                    ".", "_" -> null
                    null -> path.substringAfterLast('/')
                    else -> spec.alias
                } ?: return@forEach
                if (!importedNames.add(alias)) error("package name $alias imported more than once in a file")
                packagePaths[alias] = spec.path
            }
            val collision = importedNames.firstOrNull { it in typeDeclarations || globals.containsLocal(it) }
            if (collision != null) error("package import name $collision conflicts with a package declaration")
            val result = action()
            usedPackageAliasesByFile.getOrPut(file) { mutableSetOf() }.addAll(usedPackageAliases)
            result
        } finally {
            packagePaths.clear()
            packagePaths.putAll(previous)
            usedPackageAliases = previousUsedAliases
        }
    }

    private fun importedPackagePath(alias: String): String? = packagePaths[alias]?.also {
        usedPackageAliases += alias
    }

    private fun checkMain() {
        val main = functions["main"] ?: error("main function not found")
        if (main.parameters.isNotEmpty() || main.resultTypes.isNotEmpty()) error("main must have no parameters or results")
    }

    private fun globalVariableInitializationOrder(variables: List<VariableDeclaration>): List<VariableDeclaration> {
        val ownerByName = variables.flatMapIndexed { index, declaration ->
            declaration.names.filter { it != "_" }.map { it to index }
        }.toMap()
        val dependencies = variables.map { declaration -> declaration.values
            .flatMap(::referencedNames)
            .mapNotNull(ownerByName::get)
            .distinct()
            .sorted()
            .toSet()
        }
        val state = IntArray(variables.size)
        val result = mutableListOf<VariableDeclaration>()
        fun visit(index: Int) {
            when (state[index]) {
                2 -> return
                1 -> error("initialization cycle involving ${variables[index].names.joinToString()}")
            }
            state[index] = 1
            dependencies[index].forEach(::visit)
            state[index] = 2
            result += variables[index]
        }
        variables.indices.forEach(::visit)
        return result
    }

    private data class GlobalConstantBinding(
        val file: GoFile,
        val declaration: ConstantDeclaration,
        val index: Int
    )

    private fun globalConstantInitializationOrder(constants: List<GlobalConstantBinding>): List<GlobalConstantBinding> {
        val ownerByName = buildMap {
            constants.forEachIndexed { index, binding ->
                binding.declaration.names[binding.index].takeIf { it != "_" }?.let { put(it, index) }
            }
        }
        val dependencies = constants.map { binding ->
            referencedNames(binding.declaration.values[binding.index]).mapNotNull(ownerByName::get).distinct().sorted().toSet()
        }
        val state = IntArray(constants.size)
        val result = mutableListOf<GlobalConstantBinding>()
        fun visit(index: Int) {
            when (state[index]) {
                2 -> return
                1 -> error("constant initialization cycle involving ${constants[index].declaration.names[constants[index].index]}")
            }
            state[index] = 1
            dependencies[index].forEach(::visit)
            state[index] = 2
            result += constants[index]
        }
        constants.indices.forEach(::visit)
        return result
    }

    private fun referencedNames(expression: Expression): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> referencedNames(expression.operand)
        is BinaryExpression -> referencedNames(expression.left) + referencedNames(expression.right)
        is CallExpression -> referencedNames(expression.function) + expression.arguments.flatMap(::referencedNames)
        is SelectorExpression -> referencedNames(expression.receiver)
        is IndexExpression -> referencedNames(expression.receiver) + referencedNames(expression.index)
        is SliceExpression -> referencedNames(expression.receiver) + listOfNotNull(expression.low, expression.high).flatMap(::referencedNames)
        is TypeAssertionExpression -> referencedNames(expression.receiver)
        is TypeSwitchGuardExpression -> referencedNames(expression.receiver)
        is ParenthesizedExpression -> referencedNames(expression.expression)
        is CompositeLiteral -> expression.elements.flatMap { listOfNotNull(it.key, it.value).flatMap(::referencedNames) }.toSet()
        is ElidedCompositeLiteral -> expression.elements.flatMap { listOfNotNull(it.key, it.value).flatMap(::referencedNames) }.toSet()
        is FunctionLiteralExpression -> emptySet()
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
        val names = function.resultNames.ifEmpty { List(function.resultTypes.size) { null } }
        if (names.size != function.resultTypes.size) error("result name count does not match result type count")
        names.forEachIndexed { index, name ->
            if (name != null && name != "_") {
                if (scope.containsLocal(name)) error("$name redeclared in function signature")
                scope.define(name, function.resultTypes[index])
            }
        }
        val body = function.body ?: return
        val previousResults = resultTypes
        val previousResultNames = resultNames
        val previousLabels = functionLabels
        val previousUsedLabels = usedLabels
        val previousBlockPath = labelBlockPath
        val previousBlockIndices = blockStatementIndices
        resultTypes = function.resultTypes
        resultNames = names
        functionLabels = collectLabels(body)
        usedLabels = mutableSetOf()
        labelBlockPath = emptyList()
        blockStatementIndices = emptyMap()
        try {
            validateBranchTargets(body)
            checkBlock(body, scope, reuseScope = true)
            if (function.resultTypes.isNotEmpty() && !endsWithTerminatingStatement(body))
                error("missing return at end of function ${function.name}")
            val unused = functionLabels.keys - usedLabels
            if (unused.isNotEmpty()) error("label ${unused.first()} declared and not used")
        } finally {
            resultTypes = previousResults
            resultNames = previousResultNames
            functionLabels = previousLabels
            usedLabels = previousUsedLabels
            labelBlockPath = previousBlockPath
            blockStatementIndices = previousBlockIndices
        }
    }

    private fun checkBlock(block: BlockStatement, parent: Scope, reuseScope: Boolean = false) {
        val scope = if (reuseScope) parent else parent.child()
        val previousTypes = typeDeclarations.toMap()
        val previousPath = labelBlockPath
        labelBlockPath = previousPath + block
        try {
            block.statements.forEachIndexed { index, statement ->
                val previousIndices = blockStatementIndices
                blockStatementIndices = previousIndices + (block to index)
                try { checkStatement(statement, scope) } finally { blockStatementIndices = previousIndices }
            }
        }
        finally {
            typeDeclarations.clear()
            typeDeclarations.putAll(previousTypes)
            labelBlockPath = previousPath
        }
    }

    private fun validateBranchTargets(body: BlockStatement) {
        fun visit(
            statement: Statement,
            loopDepth: Int,
            breakDepth: Int,
            loopLabels: Set<String>,
            breakLabels: Set<String>,
            allowFallthrough: Boolean = false
        ) {
            when (statement) {
                is BranchStatement -> when (statement.kind) {
                    TokenKind.BREAK -> if (statement.label == null) {
                        if (breakDepth == 0) error("break is not inside a loop, switch, or select")
                    } else if (statement.label !in breakLabels) error("invalid break label ${statement.label}")
                    TokenKind.CONTINUE -> if (statement.label == null) {
                        if (loopDepth == 0) error("continue is not inside a loop")
                    } else if (statement.label !in loopLabels) error("invalid continue label ${statement.label}")
                    TokenKind.FALLTHROUGH -> if (!allowFallthrough) error("fallthrough statement out of place")
                    else -> Unit
                }
                is LabeledStatement -> {
                    val target = statement.statement
                    val isLoop = target is ForStatement
                    val isBreakable = isLoop || target is SwitchStatement || target is TypeSwitchStatement || target is SelectStatement
                    visit(target, loopDepth, breakDepth,
                        if (isLoop) loopLabels + statement.label else loopLabels,
                        if (isBreakable) breakLabels + statement.label else breakLabels,
                        allowFallthrough)
                }
                is BlockStatement -> statement.statements.forEach {
                    visit(it, loopDepth, breakDepth, loopLabels, breakLabels)
                }
                is IfStatement -> {
                    statement.init?.let { visit(it, loopDepth, breakDepth, loopLabels, breakLabels) }
                    visit(statement.thenBranch, loopDepth, breakDepth, loopLabels, breakLabels)
                    statement.elseBranch?.let { visit(it, loopDepth, breakDepth, loopLabels, breakLabels) }
                }
                is ForStatement -> {
                    statement.init?.let { visit(it, loopDepth, breakDepth, loopLabels, breakLabels) }
                    statement.post?.let { visit(it, loopDepth, breakDepth, loopLabels, breakLabels) }
                    visit(statement.body, loopDepth + 1, breakDepth + 1, loopLabels, breakLabels)
                }
                is SwitchStatement -> {
                    statement.init?.let { visit(it, loopDepth, breakDepth, loopLabels, breakLabels) }
                    statement.clauses.forEachIndexed { index, clause ->
                        val last = clause.statements.lastOrNull { it != EmptyStatement }
                        clause.statements.forEach { child ->
                            val isFallthrough = index < statement.clauses.lastIndex && child === last &&
                                (unwrapLabels(child) as? BranchStatement)?.kind == TokenKind.FALLTHROUGH
                            visit(child, loopDepth, breakDepth + 1, loopLabels, breakLabels, isFallthrough)
                        }
                    }
                }
                is TypeSwitchStatement -> {
                    statement.init?.let { visit(it, loopDepth, breakDepth, loopLabels, breakLabels) }
                    statement.clauses.forEach { clause ->
                        clause.statements.forEach { visit(it, loopDepth, breakDepth + 1, loopLabels, breakLabels) }
                    }
                }
                is SelectStatement -> statement.cases.forEach { clause ->
                    clause.communication?.let { visit(it, loopDepth, breakDepth + 1, loopLabels, breakLabels) }
                    clause.statements.forEach { visit(it, loopDepth, breakDepth + 1, loopLabels, breakLabels) }
                }
                else -> Unit
            }
        }
        visit(body, 0, 0, emptySet(), emptySet())
    }

    private fun endsWithTerminatingStatement(block: BlockStatement, labels: Set<String> = emptySet()): Boolean =
        block.statements.lastOrNull { it != EmptyStatement }?.let { isTerminatingStatement(it, labels) } == true

    private fun isTerminatingStatement(statement: Statement, labels: Set<String> = emptySet()): Boolean = when (statement) {
        is ReturnStatement -> true
        is BranchStatement -> statement.kind == TokenKind.GOTO
        is ExpressionStatement -> (statement.expression.unparenthesized() as? CallExpression)?.let(terminatingPanicCalls::contains) == true
        is BlockStatement -> endsWithTerminatingStatement(statement, labels)
        is LabeledStatement -> isTerminatingStatement(statement.statement, labels + statement.label)
        is IfStatement -> statement.elseBranch != null &&
            endsWithTerminatingStatement(statement.thenBranch, labels) && isTerminatingStatement(statement.elseBranch, labels)
        is ForStatement -> statement.rangeClause == null && statement.condition == null &&
            !containsBreakTo(statement.body, labels)
        is SwitchStatement -> statement.clauses.any { it.expressions == null } &&
            !statement.clauses.any { containsBreakTo(it.statements, labels) } &&
            statement.clauses.all { clauseTerminates(it.statements, allowFallthrough = true, labels) }
        is TypeSwitchStatement -> statement.clauses.any { it.types == null } &&
            !statement.clauses.any { containsBreakTo(it.statements, labels) } &&
            statement.clauses.all { clauseTerminates(it.statements, allowFallthrough = false, labels) }
        is SelectStatement -> statement.cases.none { containsBreakTo(it.statements, labels) } &&
            statement.cases.all { clauseTerminates(it.statements, allowFallthrough = false, labels) }
        else -> false
    }

    private fun clauseTerminates(statements: List<Statement>, allowFallthrough: Boolean, labels: Set<String>): Boolean {
        val last = statements.lastOrNull { it != EmptyStatement } ?: return false
        return if (allowFallthrough && unwrapLabels(last) is BranchStatement &&
            (unwrapLabels(last) as BranchStatement).kind == TokenKind.FALLTHROUGH) true
        else isTerminatingStatement(last, labels)
    }

    private fun containsBreakTo(statement: Statement, labels: Set<String>, nestedBreakables: Int = 0): Boolean = when (statement) {
        is BranchStatement -> statement.kind == TokenKind.BREAK &&
            if (statement.label == null) nestedBreakables == 0 else statement.label in labels
        is LabeledStatement -> containsBreakTo(statement.statement, labels, nestedBreakables)
        is BlockStatement -> statement.statements.any { containsBreakTo(it, labels, nestedBreakables) }
        is IfStatement -> listOfNotNull(statement.init, statement.thenBranch, statement.elseBranch)
            .any { containsBreakTo(it, labels, nestedBreakables) }
        is ForStatement -> containsBreakTo(statement.body, labels, nestedBreakables + 1)
        is SwitchStatement -> statement.clauses.any { containsBreakTo(it.statements, labels, nestedBreakables + 1) }
        is TypeSwitchStatement -> statement.clauses.any { containsBreakTo(it.statements, labels, nestedBreakables + 1) }
        is SelectStatement -> statement.cases.any { containsBreakTo(it.statements, labels, nestedBreakables + 1) }
        else -> false
    }

    private fun containsBreakTo(statements: List<Statement>, labels: Set<String>, nestedBreakables: Int = 0): Boolean =
        statements.any { containsBreakTo(it, labels, nestedBreakables) }

    private fun <T> withLocalTypeScope(action: () -> T): T {
        val previous = typeDeclarations.toMap()
        return try {
            action()
        } finally {
            typeDeclarations.clear()
            typeDeclarations.putAll(previous)
        }
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

    private fun containsFallthrough(statement: Statement): Boolean = when (statement) {
        is BranchStatement -> statement.kind == TokenKind.FALLTHROUGH
        is LabeledStatement -> containsFallthrough(statement.statement)
        is BlockStatement -> statement.statements.any(::containsFallthrough)
        is IfStatement -> listOfNotNull(statement.init, statement.thenBranch, statement.elseBranch).any(::containsFallthrough)
        is ForStatement -> listOfNotNull(statement.init, statement.post, statement.body).any(::containsFallthrough)
        // Nested clause-bearing statements validate their own fallthrough statements.
        is SwitchStatement, is TypeSwitchStatement, is SelectStatement -> false
        else -> false
    }

    private fun checkStatement(statement: Statement, scope: Scope) {
        when (statement) {
            EmptyStatement -> Unit
            is LabeledStatement -> checkStatement(statement.statement, scope)
            is DeclarationStatement -> statement.declarations.forEach { declaration ->
                when (declaration) {
                    is VariableDeclaration -> {
                        val declaredType = declaration.type?.let { resolveLocalType(it, scope) }
                        declaredType?.let(::validateType)
                        val values = expressionTypes(declaration.values, declaration.names.size, scope)
                        if (declaration.values.isNotEmpty() && values.size != declaration.names.size)
                            error("initializer count mismatch")
                        if (declaredType != null) requireAssignableValues(values, declaration.values, declaredType, "initializer", scope)
                        else requireDefaultIntegerValues(values, declaration.values, "initializer", scope)
                        declaration.names.forEachIndexed { i, name ->
                            if (name != "_") {
                                if (scope.containsLocal(name)) error("$name redeclared in this block")
                                scope.define(name, declaredType ?: defaultType(values.getOrNull(i) ?: intType))
                            }
                        }
                    }
                    is ConstantDeclaration -> {
                        requireUniqueNames(declaration.names, "constant declaration")
                        val declaredType = declaration.type?.let { resolveLocalType(it, scope) }
                        val constants = scope.child().also {
                            it.define("iota", untypedInt, BigInteger.valueOf(declaration.iotaIndex.toLong()), isConstant = true)
                        }
                        val values = expressionTypes(declaration.values, declaration.names.size, constants)
                        if (values.size != declaration.names.size) error("constant initializer count mismatch")
                        declaration.values.forEach { if (!isConstantExpression(it, constants)) error("constant initializer is not constant") }
                        if (declaredType != null) requireAssignableValues(values, declaration.values, declaredType, "constant initializer", constants)
                        val integerConstants = if (values.size == declaration.values.size)
                            declaration.values.map { constantInteger(it, constants) } else emptyList()
                        val stringLengths = if (values.size == declaration.values.size)
                            declaration.values.map { constantStringLength(it, constants) } else emptyList()
                        val rationalConstants = if (values.size == declaration.values.size)
                            declaration.values.map { constantRational(it, constants) } else emptyList()
                        val stringIdentities = if (values.size == declaration.values.size)
                            declaration.values.map { constantStringIdentity(it, constants) } else emptyList()
                        val booleanValues = if (values.size == declaration.values.size)
                            declaration.values.map { constantBoolean(it, constants) } else emptyList()
                        declaration.names.forEachIndexed { i, name -> if (name != "_") {
                            if (scope.containsLocal(name)) error("$name redeclared in this block")
                            scope.define(
                                name, declaredType ?: values.getOrNull(i) ?: untypedInt,
                                integerConstants.getOrNull(i), stringLengths.getOrNull(i), isConstant = true,
                                rationalConstant = rationalConstants.getOrNull(i), stringIdentity = stringIdentities.getOrNull(i),
                                booleanConstant = booleanValues.getOrNull(i)
                            )
                        } }
                    }
                    is TypeDeclaration -> {
                        if (scope.containsLocal(declaration.name)) error("${declaration.name} redeclared in this block")
                        val identity = "<local:${nextLocalTypeIdentity.incrementAndGet()}:${declaration.name}>"
                        scope.defineType(declaration.name, identity)
                        typeDeclarations[identity] = resolveLocalType(declaration.type, scope)
                        validateType(NamedGoType(identity))
                    }
                    else -> error("unsupported local declaration")
                }
            }
            is BlockStatement -> checkBlock(statement, scope)
            is VariableStatement -> {
                val declaredType = statement.type?.let { resolveLocalType(it, scope) }
                declaredType?.let(::validateType)
                val values = expressionTypes(statement.values, statement.names.size, scope)
                if (statement.values.isNotEmpty() && values.size != statement.names.size)
                    error("initializer count mismatch")
                if (declaredType != null) requireAssignableValues(values, statement.values, declaredType, "initializer", scope)
                else requireDefaultIntegerValues(values, statement.values, "initializer", scope)
                statement.names.forEachIndexed { i, name ->
                    if (name != "_") {
                        if (scope.containsLocal(name)) error("$name redeclared in this block")
                        scope.define(name, declaredType ?: defaultType(values.getOrNull(i) ?: intType))
                    }
                }
            }
            is ReturnStatement -> {
                if (statement.values.isNotEmpty() || resultTypes.isEmpty() || resultNames.any { it == null }) {
                    val values = returnExpressionTypes(statement.values, scope)
                    if (values.size != resultTypes.size) error("return has ${values.size} values, want ${resultTypes.size}")
                    values.zip(resultTypes).forEachIndexed { i, (from, to) ->
                        requireAssignable(from, to, "return", statement.values.getOrNull(i), scope)
                    }
                }
            }
            is ExpressionStatement -> {
                when (val expression = statement.expression.unparenthesized()) {
                    is CallExpression -> {
                        if (isTypeConversion(expression.function, scope)) error("conversion cannot be used as a statement")
                        callResults(expression, scope)
                    }
                    is UnaryExpression -> {
                        if (expression.operator != TokenKind.ARROW) error("expression statement must be a function call or receive")
                        checkReceive(expression, scope)
                    }
                    else -> error("expression statement must be a function call or receive")
                }
            }
            is AssignmentStatement -> checkAssignment(statement, scope)
            is IncrementStatement -> {
                requireAssignmentTarget(statement.target, scope, allowBlank = false)
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
                    statement.condition?.let {
                        requireBoolean(expressionType(it, loopScope), "for condition")
                    }
                    statement.post?.let { post ->
                        if (post is AssignmentStatement && post.operator == TokenKind.DEFINE)
                            error("for post statement cannot be a short variable declaration")
                        checkStatement(post, loopScope)
                    }
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
                if (scope.containsLocal(name)) {
                    if (scope.isConstant(name)) error("cannot assign to constant $name")
                    requireAssignable(valueTypes[i], scope.get(name), "assignment", statement.values.getOrNull(i), scope)
                }
                else {
                    val targetType = defaultType(valueTypes[i])
                    statement.values.getOrNull(i)?.let { requireIntegerConstantRepresentable(it, targetType, scope) }
                    scope.define(name, targetType)
                    added++
                }
            }
            if (added == 0) error("short declaration must introduce a new variable")
            return
        }
        statement.targets.forEach { requireAssignmentTarget(it, scope, allowBlank = statement.operator == TokenKind.ASSIGN) }
        val leftTypes = statement.targets.map { target ->
            if (isBlankIdentifier(target)) null else expressionType(target, scope)
        }
        val rightTypes = expressionTypes(statement.values, leftTypes.size, scope)
        if (leftTypes.size != rightTypes.size) error("assignment count mismatch")
        if (statement.operator == TokenKind.ASSIGN) {
            leftTypes.zip(rightTypes).forEachIndexed { i, (left, right) ->
                val value = statement.values.getOrNull(i)
                if (left != null) requireAssignable(right, left, "assignment", value, scope)
                else if (value != null && statement.values.size == rightTypes.size)
                    requireDefaultIntegerValues(listOf(right), listOf(value), "assignment", scope)
            }
        } else {
            if (leftTypes.size != 1 || rightTypes.size != 1) error("compound assignment requires one operand")
            checkBinaryType(leftTypes.single() ?: error("invalid compound assignment target"), compoundOperator(statement.operator), rightTypes.single(), statement.targets.single(), statement.values.single(), scope)
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
            is ChannelGoType -> {
                if (source.direction == ChannelDirection.SEND_ONLY) error("cannot range over send-only channel")
                null to source.element
            }
            is NamedGoType -> if (source.name == "string") intType to runeType else error("cannot range over ${source.name}")
            else -> error("cannot range over this type")
        }
        if (source is ChannelGoType && range.targets.size > 1) error("range over channel permits one iteration variable")
        val types = listOfNotNull(keyAndValue.first, keyAndValue.second).take(range.targets.size)
        if (types.size != range.targets.size) error("too many range variables")
        if (range.operator == TokenKind.DEFINE) {
            val names = range.targets.map { (it as? NameExpression)?.name ?: error("range declaration requires identifiers") }
            requireUniqueNames(names, "range declaration")
            if (names.none { it != "_" }) error("range declaration must introduce a variable")
            range.targets.forEachIndexed { i, target ->
                val name = (target as? NameExpression)?.name ?: error("range declaration requires identifiers")
                if (name != "_") scope.define(name, defaultType(types[i]))
            }
        } else if (range.operator == TokenKind.ASSIGN) {
            range.targets.zip(types).forEach { (target, type) ->
                requireAssignmentTarget(target, scope)
                if (!isBlankIdentifier(target))
                    requireAssignable(type, expressionType(target, scope), "range assignment")
            }
        }
        checkBlock(body, scope)
    }

    private fun checkSend(statement: SendStatement, scope: Scope) {
        val channel = underlying(expressionType(statement.channel, scope)) as? ChannelGoType ?: error("send requires a channel")
        if (channel.direction == ChannelDirection.RECEIVE_ONLY) error("cannot send on receive-only channel")
        requireAssignable(expressionType(statement.value, scope), channel.element, "channel send", statement.value, scope)
    }

    private fun checkSelect(statement: SelectStatement, scope: Scope) {
        var sawDefault = false
        statement.cases.forEach { clause ->
            if (clause.statements.any(::containsFallthrough)) error("fallthrough is not permitted in a select")
            val caseScope = scope.child()
            when (val communication = clause.communication) {
                null -> {
                    if (sawDefault) error("multiple default cases in select")
                    sawDefault = true
                }
                is SendStatement -> checkSend(communication, caseScope)
                is ExpressionStatement -> checkReceive(communication.expression, caseScope)
                is AssignmentStatement -> {
                    if (communication.operator !in setOf(TokenKind.ASSIGN, TokenKind.DEFINE))
                        error("select receive assignment must use = or :=")
                    val receive = communication.values.singleOrNull()?.unparenthesized() as? UnaryExpression
                        ?: error("select case must receive from a channel")
                    if (receive.operator != TokenKind.ARROW) error("select case must receive from a channel")
                    val channel = underlying(expressionType(receive.operand, caseScope)) as? ChannelGoType ?: error("receive requires a channel")
                    if (channel.direction == ChannelDirection.SEND_ONLY) error("cannot receive from send-only channel")
                    if (communication.operator == TokenKind.DEFINE) {
                        val names = communication.targets.map { (it as? NameExpression)?.name ?: error("receive declaration requires identifiers") }
                        if (names.size !in 1..2) error("invalid receive assignment")
                        requireUniqueNames(names, "receive declaration")
                        if (names.none { it != "_" }) error("receive declaration must introduce a variable")
                        names.forEachIndexed { i, name ->
                            if (name != "_") caseScope.define(name, if (i == 0) defaultType(channel.element) else boolType)
                        }
                    } else {
                        communication.targets.forEach { requireAssignmentTarget(it, caseScope) }
                        val targets = communication.targets.map { target ->
                            if (isBlankIdentifier(target)) null else expressionType(target, caseScope)
                        }
                        if (targets.size !in 1..2) error("invalid receive assignment")
                        targets.first()?.let { requireAssignable(channel.element, it, "receive assignment") }
                        if (targets.size == 2) targets[1]?.let { requireAssignable(boolType, it, "receive status") }
                    }
                }
                else -> error("invalid select communication")
            }
            inLabelBlock(clause) { withLocalTypeScope { clause.statements.forEach { checkStatement(it, caseScope) } } }
        }
    }

    private fun checkReceive(expression: Expression, scope: Scope) {
        val receive = expression.unparenthesized() as? UnaryExpression ?: error("select receive case must use <-")
        if (receive.operator != TokenKind.ARROW) error("select receive case must use <-")
        val channel = underlying(expressionType(receive.operand, scope)) as? ChannelGoType ?: error("receive requires a channel")
        if (channel.direction == ChannelDirection.SEND_ONLY) error("cannot receive from send-only channel")
    }

    private fun checkSwitch(statement: SwitchStatement, scope: Scope) {
        val switchScope = scope.child()
        statement.init?.let { checkStatement(it, switchScope) }
        val tagType = statement.tag?.let { expressionType(it, switchScope) }
        if (tagType != null && !isComparable(tagType)) error("switch expression must be comparable")
        var sawDefault = false
        val seenCases = mutableSetOf<String>()
        statement.clauses.forEachIndexed { clauseIndex, clause ->
            val lastStatementIndex = clause.statements.indexOfLast { it != EmptyStatement }
            clause.statements.forEachIndexed { statementIndex, child ->
                val branch = unwrapLabels(child) as? BranchStatement
                if (branch?.kind == TokenKind.FALLTHROUGH) {
                    if (clauseIndex == statement.clauses.lastIndex || statementIndex != lastStatementIndex)
                        error("fallthrough statement out of place")
                } else if (containsFallthrough(child)) error("fallthrough statement out of place")
            }
            val caseScope = switchScope.child()
            if (clause.expressions == null) {
                if (sawDefault) error("multiple default cases in switch")
                sawDefault = true
            }
            clause.expressions?.forEach { case ->
                val caseType = expressionType(case, caseScope)
                if (tagType != null) {
                    if (!assignable(caseType, tagType) && !assignable(tagType, caseType))
                        error("case type does not match switch expression")
                    requireIntegerConstantRepresentable(case, tagType, caseScope)
                } else requireBoolean(caseType, "expressionless switch case")
                val identity = constantCaseIdentity(case, caseType, tagType, caseScope)
                if (identity != null && !seenCases.add(identity)) error("duplicate case $case in switch")
            }
            inLabelBlock(clause) { withLocalTypeScope { clause.statements.forEach { checkStatement(it, caseScope) } } }
        }
    }

    private fun constantCaseIdentity(
        expression: Expression,
        caseType: GoTypeSyntax,
        switchType: GoTypeSyntax?,
        scope: Scope
    ): String? {
        val identityType = if (isUntyped(caseType)) switchType ?: defaultType(caseType) else caseType
        val typeKey = identityType.toString()
        constantRational(expression, scope)?.let { value ->
            return "$typeKey:number:${value.numerator}/${value.denominator}"
        }
        constantStringIdentity(expression, scope)?.let { value -> return "$typeKey:string:$value" }
        return constantBoolean(expression, scope)?.let { "$typeKey:boolean:$it" }
    }

    private fun constantBoolean(expression: Expression, scope: Scope = globals): Boolean? = when (expression) {
        is NameExpression -> if (scope.getOrNull(expression.name) != null) scope.constantBoolean(expression.name) else when (expression.name) {
            "true" -> true
            "false" -> false
            else -> null
        }
        is ParenthesizedExpression -> constantBoolean(expression.expression, scope)
        is UnaryExpression -> if (expression.operator == TokenKind.NOT) constantBoolean(expression.operand, scope)?.not() else null
        is BinaryExpression -> {
            val leftBoolean = constantBoolean(expression.left, scope)
            val rightBoolean = constantBoolean(expression.right, scope)
            when (expression.operator) {
                TokenKind.LAND -> if (leftBoolean != null && rightBoolean != null) leftBoolean && rightBoolean else null
                TokenKind.LOR -> if (leftBoolean != null && rightBoolean != null) leftBoolean || rightBoolean else null
                TokenKind.EQL, TokenKind.NEQ -> {
                    val equal = when {
                        leftBoolean != null && rightBoolean != null -> leftBoolean == rightBoolean
                        constantRational(expression.left, scope) != null && constantRational(expression.right, scope) != null ->
                            constantRational(expression.left, scope) == constantRational(expression.right, scope)
                        constantStringIdentity(expression.left, scope) != null && constantStringIdentity(expression.right, scope) != null ->
                            constantStringIdentity(expression.left, scope) == constantStringIdentity(expression.right, scope)
                        else -> null
                    }
                    equal?.let { if (expression.operator == TokenKind.EQL) it else !it }
                }
                TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ -> {
                    val leftNumber = constantRational(expression.left, scope)
                    val rightNumber = constantRational(expression.right, scope)
                    val comparison = if (leftNumber != null && rightNumber != null) leftNumber.compareTo(rightNumber)
                    else {
                        val leftString = constantStringIdentity(expression.left, scope)
                        val rightString = constantStringIdentity(expression.right, scope)
                        if (leftString != null && rightString != null) compareConstantStrings(leftString, rightString) else null
                    }
                    comparison?.let { value -> when (expression.operator) {
                        TokenKind.LSS -> value < 0
                        TokenKind.LEQ -> value <= 0
                        TokenKind.GTR -> value > 0
                        TokenKind.GEQ -> value >= 0
                    } }
                }
                else -> null
            }
        }
        is CallExpression -> {
            val target = when (val function = expression.function) {
                is TypeExpression -> function.type
                is NameExpression -> if (scope.getOrNull(function.name) == null &&
                    (isBuiltinType(function.name) || function.name in typeDeclarations)) NamedGoType(function.name) else null
                else -> null
            }
            if (target != null && underlying(target) == boolType && expression.arguments.size == 1 && !expression.expandLastArgument)
                constantBoolean(expression.arguments.single(), scope) else null
        }
        else -> null
    }

    private fun constantStringIdentity(expression: Expression, scope: Scope = globals): String? = when (expression) {
        is NameExpression -> scope.constantStringIdentity(expression.name)
        is LiteralExpression -> if (expression.token.kind == TokenKind.STRING)
            canonicalGoStringLiteral(expression.token.lexeme) else null
        is ParenthesizedExpression -> constantStringIdentity(expression.expression, scope)
        is BinaryExpression -> if (expression.operator == TokenKind.ADD) {
            val left = constantStringIdentity(expression.left, scope)
            val right = constantStringIdentity(expression.right, scope)
            if (left != null && right != null) left + right else null
        } else null
        is CallExpression -> {
            val target = when (val function = expression.function) {
                is TypeExpression -> function.type
                is NameExpression -> if (scope.getOrNull(function.name) == null &&
                    (isBuiltinType(function.name) || function.name in typeDeclarations)) NamedGoType(function.name) else null
                else -> null
            }
            if (target == null || underlying(target) != stringType || expression.arguments.size != 1 || expression.expandLastArgument) null
            else constantStringIdentity(expression.arguments.single(), scope) ?: constantInteger(expression.arguments.single(), scope)?.let { value ->
                val codePoint = runCatching { value.intValueExact() }.getOrNull()
                val rune = if (codePoint == null || codePoint !in 0..Character.MAX_CODE_POINT || codePoint in 0xd800..0xdfff)
                    0xfffd else codePoint
                String(Character.toChars(rune)).toByteArray(Charsets.UTF_8).joinToString("") { byte ->
                    (byte.toInt() and 0xff).toString(16).padStart(2, '0')
                }
            }
        }
        else -> null
    }

    private fun compareConstantStrings(left: String, right: String): Int {
        val commonBytes = minOf(left.length, right.length) / 2
        for (index in 0 until commonBytes) {
            val leftByte = left.substring(index * 2, index * 2 + 2).toInt(16)
            val rightByte = right.substring(index * 2, index * 2 + 2).toInt(16)
            if (leftByte != rightByte) return leftByte.compareTo(rightByte)
        }
        return (left.length / 2).compareTo(right.length / 2)
    }

    private fun checkTypeSwitch(statement: TypeSwitchStatement, scope: Scope) {
        val switchScope = scope.child()
        statement.init?.let { checkStatement(it, switchScope) }
        if (statement.guard.name == "_") error("type switch guard must declare a variable")
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
                val caseType = resolveLocalType(type, switchScope)
                validateType(caseType)
                if (underlying(caseType) !is InterfaceGoType)
                    requireAssignable(caseType, interfaceType, "type switch case")
                if (seenTypes.any { sameType(it, caseType) }) error("duplicate type switch case $caseType")
                seenTypes += caseType
            }
            if (clause.statements.any(::containsFallthrough)) error("fallthrough is not permitted in a type switch")
            val caseScope = switchScope.child()
            val singleType = clause.types?.singleOrNull()?.takeUnless { it == NamedGoType("nil") }
                ?.let { resolveLocalType(it, switchScope) }
            if (statement.guard.name != null && statement.guard.name != "_")
                caseScope.define(statement.guard.name, singleType ?: interfaceType)
            inLabelBlock(clause) { withLocalTypeScope { clause.statements.forEach { checkStatement(it, caseScope) } } }
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

    private fun returnExpressionTypes(expressions: List<Expression>, scope: Scope): List<GoTypeSyntax> {
        val call = expressions.singleOrNull() as? CallExpression
        val callResults = call?.let { callResults(it, scope) }
        if (callResults != null && callResults.size > 1) return callResults
        return expressions.map { expressionType(it, scope) }
    }

    private fun callArgumentTypes(arguments: List<Expression>, expandLastArgument: Boolean, scope: Scope): List<GoTypeSyntax> {
        if (!expandLastArgument && arguments.size == 1) {
            val multiValueCall = arguments.single() as? CallExpression
            val results = multiValueCall?.let { callResults(it, scope) }
            if (results != null && results.size > 1) return results
        }
        return arguments.map { expressionType(it, scope) }
    }

    private fun expressionType(expression: Expression, scope: Scope): GoTypeSyntax = when (expression) {
        is NameExpression -> scope.getOrNull(expression.name) ?: when (expression.name) {
            "true", "false" -> untypedBool
            "nil" -> nilType
            "iota" -> error("undefined: iota")
            else -> scope.typeBinding(expression.name)?.let(::NamedGoType)
                ?: if (typeDeclarations.containsKey(expression.name)) NamedGoType(expression.name)
                else if (isBuiltinType(expression.name)) NamedGoType(expression.name)
                else if (functions.containsKey(expression.name)) functionType(functions.getValue(expression.name))
                else error("undefined: ${expression.name}")
        }
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> untypedInt
            TokenKind.CHAR -> untypedRune
            TokenKind.FLOAT -> untypedFloat
            TokenKind.IMAG -> untypedComplex
            TokenKind.STRING -> untypedString
            else -> error("invalid literal")
        }
        is ParenthesizedExpression -> expressionType(expression.expression, scope)
        is FunctionLiteralExpression -> {
            val parameters = expression.parameters.map { it.copy(type = resolveLocalType(it.type, scope)) }
            val results = expression.results.map { resolveLocalType(it, scope) }
            val literalScope = scope.child()
            parameters.forEach { parameter ->
                validateType(parameter.type)
                val name = parameter.name
                if (name != null && name != "_") {
                    if (literalScope.containsLocal(name)) error("$name redeclared in function signature")
                    literalScope.define(name, parameter.type)
                }
            }
            results.forEach(::validateType)
            val resultNamesForLiteral = expression.resultNames.ifEmpty { List(results.size) { null } }
            if (resultNamesForLiteral.size != results.size) error("result name count does not match result type count")
            resultNamesForLiteral.forEachIndexed { index, name ->
                if (name != null && name != "_") {
                    if (literalScope.containsLocal(name)) error("$name redeclared in function signature")
                    literalScope.define(name, results[index])
                }
            }
            val previousResults = resultTypes
            val previousResultNames = resultNames
            val previousLabels = functionLabels
            val previousUsedLabels = usedLabels
            val previousBlockPath = labelBlockPath
            val previousBlockIndices = blockStatementIndices
            resultTypes = results
            resultNames = resultNamesForLiteral
            functionLabels = collectLabels(expression.body)
            usedLabels = mutableSetOf()
            labelBlockPath = emptyList()
            blockStatementIndices = emptyMap()
            try {
                validateBranchTargets(expression.body)
                checkBlock(expression.body, literalScope, reuseScope = true)
                if (results.isNotEmpty() && !endsWithTerminatingStatement(expression.body))
                    error("missing return at end of function literal")
                val unused = functionLabels.keys - usedLabels
                if (unused.isNotEmpty()) error("label ${unused.first()} declared and not used")
            } finally {
                resultTypes = previousResults
                resultNames = previousResultNames
                functionLabels = previousLabels
                usedLabels = previousUsedLabels
                labelBlockPath = previousBlockPath
                blockStatementIndices = previousBlockIndices
            }
            FunctionGoType(parameters, results)
        }
        is UnaryExpression -> {
            val operand = expressionType(expression.operand, scope)
            when (expression.operator) {
                TokenKind.ADD, TokenKind.SUB -> { if (!isNumeric(operand)) error("unary operator requires numeric operand"); operand }
                TokenKind.NOT -> { requireBoolean(operand, "!"); boolType }
                TokenKind.XOR -> { if (!isInteger(operand)) error("^ requires integer operand"); operand }
                TokenKind.AND -> {
                    if (expression.operand !is CompositeLiteral && !isAddressable(expression.operand, scope))
                        error("& requires addressable operand")
                    PointerGoType(operand)
                }
                TokenKind.MUL -> (underlying(operand) as? PointerGoType)?.element ?: error("* requires pointer operand")
                TokenKind.ARROW -> {
                    val channel = underlying(operand) as? ChannelGoType ?: error("receive requires a channel")
                    if (channel.direction == ChannelDirection.SEND_ONLY) error("cannot receive from send-only channel")
                    channel.element
                }
                else -> error("invalid unary operator")
            }
        }
        is BinaryExpression -> checkBinaryType(
            expressionType(expression.left, scope), expression.operator, expressionType(expression.right, scope), expression.left, expression.right, scope
        )
        is CallExpression -> {
            val results = callResults(expression, scope)
            if (results.size != 1) error("multiple-value call used in single-value context")
            results.single()
        }
        is SelectorExpression -> selectorType(expression, scope)
        is IndexExpression -> indexType(expression, scope)
        is SliceExpression -> {
            listOfNotNull(expression.low, expression.high).forEach { bound ->
                val boundType = expressionType(bound, scope)
                requireInteger(boundType, "slice index")
                if (isUntyped(boundType)) requireIntegerConstantRepresentable(bound, intType, scope)
            }
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
            resolveLocalType(expression.type, scope).also(::validateType)
        }
        is TypeSwitchGuardExpression -> error("type switch guard is only valid in a switch statement")
        is TypeExpression -> resolveLocalType(expression.type, scope).also(::validateType)
        is CompositeLiteral -> {
            checkComposite(expression, scope)
        }
        is ElidedCompositeLiteral -> error("elided composite literal requires an element type")
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
            is MapGoType -> { requireAssignable(index, receiver.key, "map index", expression.index, scope); receiver.value }
            is NamedGoType -> if (receiver.name == "string") { requireInteger(index, "string index"); byteType } else error("cannot index ${receiver.name}")
            else -> error("cannot index this value")
        }
    }

    private fun selectorType(
        expression: SelectorExpression,
        scope: Scope,
        allowBoundMethod: Boolean = false
    ): GoTypeSyntax {
        if (expression.field == "_") error("cannot refer to blank struct field")
        if (expression.receiver is NameExpression && expression.receiver.name in packagePaths &&
            scope.getOrNull(expression.receiver.name) == null) {
            return if (packageName(importedPackagePath(expression.receiver.name)!!) == "fmt") FunctionGoType(emptyList(), emptyList()) else error("unknown imported package")
        }
        methodExpressionReceiver(expression.receiver, scope)?.let { receiverType ->
            val method = methodSet(receiverType)[expression.field] ?: error("undefined method ${expression.field} on $receiverType")
            return FunctionGoType(listOf(ParameterSyntax(null, receiverType)) + method.parameters, method.results)
        }
        val receiverType = expressionType(expression.receiver, scope)
        data class Candidate(
            val type: GoTypeSyntax,
            val needsAddressableReceiver: Boolean = false,
            val isMethod: Boolean = false
        )
        data class SearchNode(val type: GoTypeSyntax, val pointer: Boolean, val ancestors: Set<String>)
        var level = listOf(SearchNode(receiverType, receiverType is PointerGoType, emptySet()))
        while (level.isNotEmpty()) {
            val candidates = mutableListOf<Candidate>()
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                when (val actual = selectorBaseType(node.type)) {
                    is InterfaceGoType -> interfaceMethods(actual)[expression.field]?.let {
                        candidates += Candidate(it, isMethod = true)
                    }
                    is StructGoType -> {
                        actual.fields.forEach { field ->
                            val fieldNames = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                            if (expression.field in fieldNames) candidates += Candidate(field.type)
                        }
                        val named = namedType(node.type)
                        if (named != null) methods["$named.${expression.field}"]?.let { method ->
                            val pointerReceiver = method.receiver?.type is PointerGoType
                            candidates += Candidate(
                                functionType(method), pointerReceiver && !node.pointer &&
                                    !isAddressable(expression.receiver, scope), isMethod = true
                            )
                        }
                        actual.fields.filter { it.names.isEmpty() }.forEach { field ->
                            val embedded = field.type
                            val key = embedded.toString()
                            if (key !in node.ancestors) next += SearchNode(
                                embedded, node.pointer || embedded is PointerGoType, node.ancestors + key
                            )
                        }
                    }
                    else -> namedType(node.type)?.let { named ->
                        methods["$named.${expression.field}"]?.let { method ->
                            val pointerReceiver = method.receiver?.type is PointerGoType
                            candidates += Candidate(
                                functionType(method), pointerReceiver && !node.pointer &&
                                    !isAddressable(expression.receiver, scope), isMethod = true
                            )
                        }
                    }
                }
            }
            if (candidates.isNotEmpty()) {
                if (candidates.size != 1) error("ambiguous selector ${expression.field}")
                val candidate = candidates.single()
                if (candidate.needsAddressableReceiver)
                    error("cannot call pointer method ${expression.field} on non-addressable value")
                if (candidate.isMethod && !allowBoundMethod)
                    error("method values are not supported by Go 1.0")
                return candidate.type
            }
            level = next
        }
        error("undefined field or method ${expression.field}")
    }

    private fun methodExpressionReceiver(expression: Expression, scope: Scope): GoTypeSyntax? = when (expression) {
        is NameExpression -> if (scope.getOrNull(expression.name) != null) null else {
            scope.typeBinding(expression.name)?.let { resolveLocalType(NamedGoType(it), scope) }
                ?: if (expression.name in typeDeclarations || isBuiltinType(expression.name)) NamedGoType(expression.name)
                else null
        }
        is ParenthesizedExpression -> methodExpressionReceiver(expression.expression, scope)
        is UnaryExpression -> if (expression.operator == TokenKind.MUL) {
            methodExpressionReceiver(expression.operand, scope)?.let(::PointerGoType)
        } else null
        else -> null
    }

    private fun isAddressable(expression: Expression, scope: Scope): Boolean = when (expression) {
        is NameExpression -> scope.isVariable(expression.name)
        is ParenthesizedExpression -> isAddressable(expression.expression, scope)
        is UnaryExpression -> expression.operator == TokenKind.MUL &&
            underlying(expressionType(expression.operand, scope)) is PointerGoType
        is IndexExpression -> when (val receiver = underlying(expressionType(expression.receiver, scope))) {
            is SliceGoType -> true
            is ArrayGoType -> isAddressable(expression.receiver, scope)
            is PointerGoType -> underlying(receiver.element) is ArrayGoType
            else -> false
        }
        is SelectorExpression -> selectorFieldAddressable(expression, scope)
        else -> false
    }

    private fun requireAssignmentTarget(expression: Expression, scope: Scope, allowBlank: Boolean = true) {
        val target = when (expression) {
            is ParenthesizedExpression -> return requireAssignmentTarget(expression.expression, scope, allowBlank)
            is NameExpression -> if (allowBlank && expression.name == "_") return else expression
            else -> expression
        }
        val isMapIndex = target is IndexExpression && underlying(expressionType(target.receiver, scope)) is MapGoType
        if (!isMapIndex && !isAddressable(target, scope)) error("assignment target is not addressable")
    }

    private fun isBlankIdentifier(expression: Expression): Boolean = when (expression) {
        is NameExpression -> expression.name == "_"
        is ParenthesizedExpression -> isBlankIdentifier(expression.expression)
        else -> false
    }

    private fun selectorFieldAddressable(expression: SelectorExpression, scope: Scope): Boolean {
        val receiverType = expressionType(expression.receiver, scope)
        val pointer = underlying(receiverType) is PointerGoType
        data class SearchNode(val type: GoTypeSyntax, val addressable: Boolean, val ancestors: Set<String>)
        var level = listOf(SearchNode(receiverType, pointer || isAddressable(expression.receiver, scope), emptySet()))
        while (level.isNotEmpty()) {
            val fields = mutableListOf<Boolean>()
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                val actual = selectorBaseType(node.type) as? StructGoType ?: return@forEach
                actual.fields.forEach { field ->
                    val fieldNames = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                    if (expression.field in fieldNames) fields += node.addressable
                }
                actual.fields.filter { it.names.isEmpty() }.forEach { field ->
                    val key = field.type.toString()
                    if (key !in node.ancestors) next += SearchNode(
                        field.type,
                        node.addressable || field.type is PointerGoType,
                        node.ancestors + key
                    )
                }
            }
            if (fields.isNotEmpty()) return fields.size == 1 && fields.single()
            level = next
        }
        return false
    }

    private fun checkComposite(literal: CompositeLiteral, scope: Scope): GoTypeSyntax {
        val literalType = resolveLocalType(literal.type, scope)
        checkCompositeElements(literalType, literal.elements, scope)
        val type = underlying(literalType)
        if (type is ArrayGoType && type.length == null) {
            var nextIndex = BigInteger.ZERO
            var maxIndex = BigInteger.valueOf(-1L)
            literal.elements.forEach { item ->
                val index = item.key?.let { constantInteger(it, scope) } ?: nextIndex
                if (index > maxIndex) maxIndex = index
                nextIndex = index + BigInteger.ONE
            }
            val length = maxIndex + BigInteger.ONE
            val lengthExpression = LiteralExpression(Token(TokenKind.INT, length.toString(), Position(0, 1, 1)))
            requireIntegerConstantRepresentable(lengthExpression, intType, scope)
            return ArrayGoType(lengthExpression, type.element)
        }
        return literalType
    }

    private fun resolveLocalType(type: GoTypeSyntax, scope: Scope): GoTypeSyntax = when (type) {
        is NamedGoType -> scope.typeBinding(type.name)?.let(::NamedGoType) ?: type
        is QualifiedGoType -> type
        is PointerGoType -> PointerGoType(resolveLocalType(type.element, scope))
        is SliceGoType -> SliceGoType(resolveLocalType(type.element, scope))
        is ArrayGoType -> ArrayGoType(type.length, resolveLocalType(type.element, scope))
        is MapGoType -> MapGoType(resolveLocalType(type.key, scope), resolveLocalType(type.value, scope))
        is ChannelGoType -> ChannelGoType(resolveLocalType(type.element, scope), type.direction)
        is StructGoType -> StructGoType(type.fields.map { field ->
            field.copy(type = resolveLocalType(field.type, scope))
        })
        is InterfaceGoType -> InterfaceGoType(
            type.methods.map { method ->
                method.copy(
                    parameters = method.parameters.map { it.copy(type = resolveLocalType(it.type, scope)) },
                    results = method.results.map { resolveLocalType(it, scope) }
                )
            },
            type.embeddedTypes.map { resolveLocalType(it, scope) }
        )
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = resolveLocalType(it.type, scope)) },
            type.results.map { resolveLocalType(it, scope) }
        )
    }

    private fun checkCompositeElements(literalType: GoTypeSyntax, elements: List<CompositeElement>, scope: Scope) {
        val type = underlying(literalType)
        when (type) {
            is SliceGoType, is ArrayGoType -> {
                val element = if (type is SliceGoType) type.element else (type as ArrayGoType).element
                val arrayLength = (type as? ArrayGoType)?.length?.let { length ->
                    requireInteger(expressionType(length, scope), "array length")
                    val constant = constantInteger(length, scope) ?: error("array length must be constant")
                    if (constant.signum() < 0) error("array length must be non-negative")
                    requireIntegerConstantRepresentable(length, intType, scope)
                    constant
                }
                var nextIndex = BigInteger.ZERO
                val usedIndices = mutableSetOf<BigInteger>()
                elements.forEach { item ->
                    val index = item.key?.let { key ->
                        requireInteger(expressionType(key, scope), "composite index")
                        val constant = constantInteger(key, scope) ?: error("composite index must be constant")
                        if (constant.signum() < 0) error("composite index must be non-negative")
                        requireIntegerConstantRepresentable(key, intType, scope)
                        constant
                    } ?: nextIndex
                    if (!usedIndices.add(index)) error("duplicate composite index $index")
                    if (arrayLength != null && index >= arrayLength) error("composite index $index is out of bounds")
                    nextIndex = index + BigInteger.ONE
                    checkCompositeValue(item.value, element, "composite element", scope)
                }
            }
            is MapGoType -> elements.forEach { item ->
                val key = item.key ?: error("map literal element requires key")
                checkCompositeValue(key, type.key, "map key", scope)
                checkCompositeValue(item.value, type.value, "map value", scope)
            }
            is StructGoType -> {
                val fieldList = type.fields.flatMap { field ->
                    field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }.map { it to field.type }
                }.filter { it.first.isNotEmpty() }
                val fields = fieldList.toMap()
                val keyed = elements.map { it.key != null }.toSet()
                if (keyed.size > 1) error("mixture of keyed and unkeyed struct literal elements")
                if (keyed.singleOrNull() == true) {
                    val usedFields = mutableSetOf<String>()
                    elements.forEach { item ->
                        val key = (item.key as? NameExpression)?.name ?: error("struct field key must be an identifier")
                        if (key == "_") error("cannot use blank field in keyed struct literal")
                        if (!usedFields.add(key)) error("duplicate field $key in struct literal")
                        val fieldType = fields[key] ?: error("unknown field $key")
                        checkCompositeValue(item.value, fieldType, "struct field", scope, allowElided = false)
                    }
                } else {
                    if (elements.size != fieldList.size) error("struct literal has ${elements.size} values for ${fieldList.size} fields")
                    elements.forEachIndexed { i, item ->
                        checkCompositeValue(item.value, fieldList[i].second, "struct field", scope, allowElided = false)
                    }
                }
            }
            else -> error("invalid composite literal type")
        }
    }

    private fun embeddedFieldName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> type.name
        is PointerGoType -> embeddedFieldName(type.element)
        else -> ""
    }

    private fun validateStructFields(type: StructGoType) {
        val names = mutableSetOf<String>()
        type.fields.forEach { field ->
            val fieldNames = if (field.names.isEmpty()) {
                val embedded = when (val fieldType = field.type) {
                    is NamedGoType, is QualifiedGoType -> fieldType
                    is PointerGoType -> when (val element = fieldType.element) {
                        is NamedGoType, is QualifiedGoType -> element
                        else -> error("embedded field must be a type name or pointer to a type name")
                    }
                    else -> error("embedded field must be a type name or pointer to a type name")
                }
                if (field.type is PointerGoType && underlying(embedded) is InterfaceGoType)
                    error("embedded pointer field cannot have interface type")
                listOf(embeddedFieldName(embedded))
            } else field.names
            fieldNames.filter { it != "_" }.forEach { name ->
                if (!names.add(name)) error("duplicate field name $name in struct type")
            }
        }
    }

    private fun checkCompositeValue(
        value: Expression,
        expectedType: GoTypeSyntax,
        context: String,
        scope: Scope,
        allowElided: Boolean = true
    ) {
        if (value is ElidedCompositeLiteral) {
            if (!allowElided) error("elided composite literal is not allowed here")
            val actual = underlying(expectedType)
            val literalType = if (actual is PointerGoType) actual.element else expectedType
            if (underlying(literalType) !is StructGoType && underlying(literalType) !is ArrayGoType &&
                underlying(literalType) !is SliceGoType && underlying(literalType) !is MapGoType)
                error("elided literal type must be composite")
            checkCompositeElements(literalType, value.elements, scope)
        }
        else requireAssignable(expressionType(value, scope), expectedType, context, value, scope)
    }

    private fun callResults(call: CallExpression, scope: Scope): List<GoTypeSyntax> {
        val target = call.function
        if (target is TypeExpression) {
            if (call.arguments.size != 1) error("conversion requires one argument")
            val from = expressionType(call.arguments.single(), scope)
            if (!convertible(from, target.type)) error("cannot convert $from to ${target.type}")
            requireIntegerConstantRepresentable(call.arguments.single(), target.type, scope)
            return listOf(target.type)
        }
        if (target is SelectorExpression && target.receiver is NameExpression &&
            target.receiver.name in packagePaths && scope.getOrNull(target.receiver.name) == null) {
            val importedPath = importedPackagePath(target.receiver.name)!!
            callArgumentTypes(call.arguments, call.expandLastArgument, scope)
            return when {
                packageName(importedPath) != "fmt" -> error("unknown imported package")
                target.field in setOf("Print", "Println", "Printf", "Fprint", "Fprintln", "Fprintf") -> listOf(intType, NamedGoType("error"))
                target.field.startsWith("S") -> listOf(stringType)
                target.field == "Errorf" -> listOf(NamedGoType("error"))
                else -> error("undefined fmt function ${target.field}")
            }
        }
        val typeNameTarget = target.unparenthesized() as? NameExpression
        if (typeNameTarget != null && scope.getOrNull(typeNameTarget.name) == null) {
            val localType = scope.typeBinding(typeNameTarget.name)?.let(::NamedGoType)
            if (localType != null || isBuiltinType(typeNameTarget.name) || typeDeclarations.containsKey(typeNameTarget.name)) {
                if (call.arguments.size != 1) error("conversion requires one argument")
                val from = expressionType(call.arguments.single(), scope)
                val to = localType ?: NamedGoType(typeNameTarget.name)
                if (!convertible(from, to)) error("cannot convert $from to $to")
                requireIntegerConstantRepresentable(call.arguments.single(), to, scope)
                return listOf(to)
            }
            val builtin = builtinCall(typeNameTarget.name, call.arguments, scope, call.expandLastArgument)
            if (builtin != null) {
                if (typeNameTarget.name == "panic") terminatingPanicCalls += call
                return builtin
            }
        }
        val targetType = if (target is SelectorExpression) selectorType(target, scope, allowBoundMethod = true)
            else expressionType(target, scope)
        val functionType = underlying(targetType) as? FunctionGoType ?: error("called value is not a function")
        val variadic = functionType.parameters.lastOrNull()?.variadic == true
        val fixedCount = if (variadic) functionType.parameters.size - 1 else functionType.parameters.size
        if (call.expandLastArgument && !variadic) error("cannot use ... with non-variadic function")
        if (call.expandLastArgument && call.arguments.size != functionType.parameters.size)
            error("variadic call with ... requires one slice argument")
        val argumentTypes = callArgumentTypes(call.arguments, call.expandLastArgument, scope)
        if ((!variadic && argumentTypes.size != fixedCount) || (variadic && !call.expandLastArgument && argumentTypes.size < fixedCount))
            error("wrong number of arguments: got ${argumentTypes.size}")
        argumentTypes.forEachIndexed { i, argumentType ->
            val parameter = functionType.parameters.getOrNull(i) ?: functionType.parameters.lastOrNull()
                ?: error("function has no parameters")
            val expected = when {
                call.expandLastArgument && i == argumentTypes.lastIndex -> parameter.type
                parameter.variadic -> (parameter.type as? SliceGoType)?.element ?: parameter.type
                else -> parameter.type
            }
            requireAssignable(argumentType, expected, "argument", call.arguments.getOrNull(i), scope)
        }
        return functionType.results
    }

    private fun builtinCall(name: String, args: List<Expression>, scope: Scope, expandLastArgument: Boolean = false): List<GoTypeSyntax>? {
        val types = callArgumentTypes(args, expandLastArgument, scope)
        if (expandLastArgument && name in setOf("print", "println") && args.size != 1)
            error("... requires a single final argument")
        return when (name) {
            "print", "println" -> emptyList()
            "panic" -> { requireCount(name, args, 1, types.size); emptyList() }
            "recover" -> { requireCount(name, args, 0, types.size); listOf(NamedGoType("interface{}")) }
            "make" -> {
                if (expandLastArgument) error("make does not accept ...")
                if (types.isEmpty()) error("make requires a type argument")
                val type = when (val argument = args.first()) {
                    is TypeExpression -> argument.type
                    is NameExpression -> scope.typeBinding(argument.name)?.let(::NamedGoType)
                        ?: if (isBuiltinType(argument.name) || typeDeclarations.containsKey(argument.name)) NamedGoType(argument.name)
                        else error("make requires a type argument")
                    else -> error("make requires a type argument")
                }
                when (underlying(type)) {
                    is SliceGoType -> {
                        if (args.size !in 2..3) error("make slice requires length and optional capacity")
                        args.drop(1).forEachIndexed { index, expression ->
                            val sizeType = types[index + 1]
                            if (!isInteger(sizeType)) error("make size must be integer")
                            if (isUntyped(sizeType)) requireIntegerConstantRepresentable(expression, intType, scope)
                        }
                    }
                    is MapGoType -> {
                        if (args.size !in 1..2) error("make map accepts at most one size hint")
                        args.getOrNull(1)?.let { expression ->
                            val sizeType = types[1]
                            if (!isInteger(sizeType)) error("make size hint must be integer")
                            if (isUntyped(sizeType)) requireIntegerConstantRepresentable(expression, intType, scope)
                        }
                    }
                    is ChannelGoType -> {
                        if (args.size !in 1..2) error("make channel accepts at most one buffer size")
                        args.getOrNull(1)?.let { expression ->
                            val sizeType = types[1]
                            if (!isInteger(sizeType)) error("make buffer size must be integer")
                            if (isUntyped(sizeType)) requireIntegerConstantRepresentable(expression, intType, scope)
                        }
                    }
                    else -> error("make requires slice, map, or channel type")
                }
                listOf(type)
            }
            "new" -> { requireCount(name, args, 1, types.size); listOf(PointerGoType(types[0])) }
            "close" -> {
                requireCount(name, args, 1, types.size)
                val channel = underlying(types[0]) as? ChannelGoType ?: error("close requires channel")
                if (channel.direction == ChannelDirection.RECEIVE_ONLY) error("cannot close receive-only channel")
                emptyList()
            }
            "len", "cap" -> {
                requireCount(name, args, 1, types.size)
                val type = underlying(types[0])
                val string = type is NamedGoType && type.name == "string"
                val pointerToArray = type is PointerGoType && underlying(type.element) is ArrayGoType
                if ((name == "cap" && string) || (!string && !pointerToArray && type !is SliceGoType &&
                        type !is ArrayGoType && type !is MapGoType && type !is ChannelGoType))
                    error("$name not defined for this type")
                listOf(intType)
            }
            "append" -> {
                if (types.size < 2) error("append requires a slice and values")
                if (expandLastArgument && types.size != 2) error("append with ... requires one slice argument")
                val slice = underlying(types[0]) as? SliceGoType ?: error("append requires slice")
                if (expandLastArgument) {
                    types.drop(1).dropLast(1).forEachIndexed { i, type -> requireAssignable(type, slice.element, "append", args.getOrNull(i + 1), scope) }
                    if (!(isString(types.last()) && isPredeclaredByteType(slice.element)))
                        requireAssignable(types.last(), SliceGoType(slice.element), "append slice")
                } else types.drop(1).forEachIndexed { i, type -> requireAssignable(type, slice.element, "append", args.getOrNull(i + 1), scope) }
                listOf(types[0])
            }
            "copy" -> {
                requireCount(name, args, 2, types.size)
                val destination = underlying(types[0])
                val source = underlying(types[1])
                when {
                    destination is SliceGoType && source is SliceGoType ->
                        if (!sameType(destination.element, source.element)) error("copy slice element types do not match")
                    destination is SliceGoType && isString(types[1]) ->
                        if (!isPredeclaredByteType(destination.element)) error("copy from string requires a byte slice")
                    destination == nilType && (source is SliceGoType || isString(types[1])) -> Unit
                    source == nilType && destination is SliceGoType -> Unit
                    else -> error("copy requires slices, or a byte slice and string")
                }
                listOf(intType)
            }
            "delete" -> {
                requireCount(name, args, 2, types.size)
                val map = underlying(types[0]) as? MapGoType ?: error("delete requires a map")
                requireAssignable(types[1], map.key, "delete key", args.getOrNull(1), scope)
                emptyList()
            }
            "complex" -> {
                requireCount(name, args, 2, types.size)
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
                requireCount(name, args, 1, types.size)
                val type = types.single()
                if (type == untypedComplex) listOf(untypedFloat)
                else when (underlying(type)) {
                    NamedGoType("complex64") -> listOf(NamedGoType("float32"))
                    NamedGoType("complex128") -> listOf(NamedGoType("float64"))
                    else -> error("$name requires a complex argument")
                }
            }
            else -> null
        }
    }

    private fun checkBinaryType(
        left: GoTypeSyntax,
        operator: TokenKind,
        right: GoTypeSyntax,
        leftExpression: Expression? = null,
        rightExpression: Expression? = null,
        scope: Scope = globals
    ): GoTypeSyntax {
        if (operator != TokenKind.SHL && operator != TokenKind.SHR) {
            if (isUntyped(left) && !isUntyped(right)) leftExpression?.let { requireIntegerConstantRepresentable(it, right, scope) }
            if (isUntyped(right) && !isUntyped(left)) rightExpression?.let { requireIntegerConstantRepresentable(it, left, scope) }
        }
        if (operator == TokenKind.SHL || operator == TokenKind.SHR) {
            if (isUntyped(left)) {
                if (leftExpression?.let { constantInteger(it, scope) } == null)
                    error("left operand of shift must be an integer")
            } else if (!isInteger(left)) error("left operand of shift must be an integer")

            if (isUntyped(right)) {
                val shiftExpression = rightExpression
                    ?: error("shift count must be a non-negative integer constant or unsigned integer")
                val count = constantInteger(shiftExpression, scope)
                    ?: error("shift count must be a non-negative integer constant or unsigned integer")
                if (count.signum() < 0) error("negative shift count")
                requireIntegerConstantRepresentable(shiftExpression, NamedGoType("uint64"), scope)
            } else if (!isUnsignedInteger(right)) {
                error("shift count must have unsigned integer type")
            }
            return if (isUntyped(left)) untypedInt else left
        }
        val l = underlying(left); val r = underlying(right)
        if (operator in setOf(TokenKind.LAND, TokenKind.LOR)) {
            requireBoolean(left, "logical operator"); requireBoolean(right, "logical operator"); return boolType
        }
        if (operator in setOf(TokenKind.EQL, TokenKind.NEQ)) {
            if (!constantOperandsAssignable(left, right, leftExpression, rightExpression, scope))
                error("incompatible comparison: $left and $right")
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
            requireSameOperands(left, right, leftExpression, rightExpression, scope)
            return boolType
        }
        if (operator == TokenKind.ADD && isString(left) && isString(right)) {
            requireSameOperands(left, right, leftExpression, rightExpression, scope)
            return commonType(left, right)
        }
        if (operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.MUL, TokenKind.QUO, TokenKind.REM) && !isNumeric(left)) error("arithmetic requires numeric operands")
        if (operator in setOf(TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT, TokenKind.REM) && !isInteger(left)) error("operator requires integer operands")
        if (!isNumeric(left) && operator !in setOf(TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT, TokenKind.REM)) error("invalid binary operands")
        requireSameOperands(left, right, leftExpression, rightExpression, scope)
        return commonType(left, right)
    }

    private fun constantOperandsAssignable(
        left: GoTypeSyntax,
        right: GoTypeSyntax,
        leftExpression: Expression?,
        rightExpression: Expression?,
        scope: Scope
    ): Boolean = assignable(left, right) || constantIntegerAssignable(left, right, leftExpression, scope) ||
        assignable(right, left) || constantIntegerAssignable(right, left, rightExpression, scope)

    private fun constantIntegerAssignable(from: GoTypeSyntax, to: GoTypeSyntax, expression: Expression?, scope: Scope) =
        expression != null && isUntyped(from) && isInteger(to) && constantInteger(expression, scope) != null

    private fun requireSameOperands(
        left: GoTypeSyntax,
        right: GoTypeSyntax,
        leftExpression: Expression? = null,
        rightExpression: Expression? = null,
        scope: Scope = globals
    ) {
        if (!constantOperandsAssignable(left, right, leftExpression, rightExpression, scope))
            error("mismatched operand types: $left and $right")
    }

    private fun commonType(left: GoTypeSyntax, right: GoTypeSyntax): GoTypeSyntax = when {
        isUntyped(left) && !isUntyped(right) -> right
        isUntyped(right) && !isUntyped(left) -> left
        left == untypedComplex || right == untypedComplex -> untypedComplex
        left == untypedFloat || right == untypedFloat -> untypedFloat
        left == untypedRune || right == untypedRune -> untypedRune
        else -> left
    }

    private fun requireAssignableValues(
        values: List<GoTypeSyntax>, expressions: List<Expression>, to: GoTypeSyntax, context: String, scope: Scope = globals
    ) {
        if (values.size == expressions.size) {
            values.zip(expressions).forEach { (from, expression) -> requireAssignable(from, to, context, expression, scope) }
        } else values.forEach { requireAssignable(it, to, context) }
    }

    private fun requireDefaultIntegerValues(values: List<GoTypeSyntax>, expressions: List<Expression>, context: String, scope: Scope = globals) {
        if (values.size != expressions.size) return
        values.zip(expressions).forEach { (from, expression) ->
            if (isUntyped(from)) requireIntegerConstantRepresentable(expression, defaultType(from), scope)
        }
    }

    private fun requireAssignable(
        from: GoTypeSyntax, to: GoTypeSyntax, context: String, expression: Expression? = null, scope: Scope = globals
    ) {
        val integralFloatConstant = constantIntegerAssignable(from, to, expression, scope)
        if (!assignable(from, to) && !integralFloatConstant) error("cannot use $from as $to in $context")
        expression?.let { requireIntegerConstantRepresentable(it, to, scope) }
    }

    private fun requireIntegerConstantRepresentable(expression: Expression, target: GoTypeSyntax, scope: Scope = globals) {
        val targetName = (underlying(target) as? NamedGoType)?.name ?: return
        if (targetName in floatNames) {
            val value = constantRational(expression, scope) ?: return
            val converted = value.toDouble()
            if (!converted.isFinite() || targetName == "float32" && !converted.toFloat().isFinite())
                error("constant overflows $target")
            return
        }
        if (!isInteger(target)) return
        val value = constantInteger(expression, scope) ?: run {
            if (isConstantExpression(expression, scope)) error("constant is not representable as $target")
            return
        }
        val name = (underlying(target) as? NamedGoType)?.name ?: return
        val bits = when (name) {
            "int8", "uint8", "byte" -> 8
            "int16", "uint16" -> 16
            "int32", "uint32", "rune" -> 32
            else -> 64
        }
        val unsigned = name in setOf("uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte")
        val minimum = if (unsigned) BigInteger.ZERO else BigInteger.ONE.shiftLeft(bits - 1).negate()
        val maximum = if (unsigned) BigInteger.ONE.shiftLeft(bits).subtract(BigInteger.ONE)
            else BigInteger.ONE.shiftLeft(bits - 1).subtract(BigInteger.ONE)
        if (value < minimum || value > maximum) error("constant $value overflows $target")
    }

    private fun assignable(from: GoTypeSyntax, to: GoTypeSyntax): Boolean {
        if (from == to) return true
        if (from == nilType) return isNilable(to)
        val requiredMethods = (underlying(to) as? InterfaceGoType)?.let(::interfaceMethods)
        if (requiredMethods != null) {
            val availableMethods = methodSet(from)
            return requiredMethods.all { (name, signature) -> availableMethods[name]?.let { sameSignature(it, signature) } == true }
        }
        val sourceChannel = underlying(from) as? ChannelGoType
        val targetChannel = underlying(to) as? ChannelGoType
        if (sourceChannel?.direction == ChannelDirection.SEND_RECEIVE && targetChannel != null &&
            sameType(sourceChannel.element, targetChannel.element) && (!isNamed(from) || !isNamed(to))) return true
        if (isUntyped(from)) {
            val f = underlying(from)
            val t = underlying(to)
            return when {
                f == untypedInt || f == untypedRune -> isNumeric(to) || isUntyped(to)
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

    private fun convertible(from: GoTypeSyntax, to: GoTypeSyntax): Boolean {
        if (assignable(from, to)) return true
        val source = underlying(from)
        val destination = underlying(to)
        if (sameType(source, destination)) return true
        if (from is PointerGoType && to is PointerGoType &&
            sameType(underlying(from.element), underlying(to.element))) return true
        return (isNumeric(from) && isNumeric(to)) ||
            (isString(from) && (isString(to) || isByteOrRuneSlice(to))) ||
            (isInteger(from) && isString(to)) ||
            (isByteOrRuneSlice(from) && isString(to))
    }

    private fun isByteOrRuneSlice(type: GoTypeSyntax): Boolean {
        val slice = underlying(type) as? SliceGoType ?: return false
        val element = underlying(slice.element)
        return element == NamedGoType("uint8") || element == NamedGoType("int32")
    }

    private fun isPredeclaredByteType(type: GoTypeSyntax): Boolean =
        type == NamedGoType("byte") && "byte" !in typeDeclarations ||
            type == NamedGoType("uint8") && "uint8" !in typeDeclarations

    private fun validateType(type: GoTypeSyntax, active: Set<String> = emptySet(), indirect: Boolean = false) {
        when (type) {
            is NamedGoType -> {
                if (!isBuiltinType(type.name) && type.name !in typeDeclarations) error("undefined type ${type.name}")
                if (type.name in active) {
                    if (indirect) return
                    error("invalid recursive type ${type.name}")
                }
                typeDeclarations[type.name]?.let { declaredType ->
                    validateType(declaredType, active + type.name)
                    val struct = underlying(NamedGoType(type.name)) as? StructGoType
                    struct?.fields?.flatMap { field ->
                        field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                    }?.filter { it != "_" }?.forEach { fieldName ->
                        if (methods.containsKey("${type.name}.$fieldName"))
                            error("field and method name conflict: $fieldName")
                    }
                }
            }
            is QualifiedGoType -> if (type.packageName !in packagePaths) error("unknown package ${type.packageName}")
                else importedPackagePath(type.packageName)
            is PointerGoType -> validateType(type.element, active, true)
            is SliceGoType -> validateType(type.element, active, true)
            is ArrayGoType -> {
                val length = type.length ?: error("inferred array length is only valid in a composite literal")
                requireInteger(expressionType(length, globals), "array length")
                val constant = constantInteger(length, globals) ?: error("array length must be constant")
                if (constant.signum() < 0) error("array length must be non-negative")
                requireIntegerConstantRepresentable(length, intType, globals)
                validateType(type.element, active)
            }
            is MapGoType -> { validateType(type.key, active); validateType(type.value, active, true); if (!isComparable(type.key)) error("invalid map key type") }
            is ChannelGoType -> validateType(type.element, active, true)
            is StructGoType -> {
                validateStructFields(type)
                type.fields.forEach { validateType(it.type, active) }
            }
            is InterfaceGoType -> {
                val names = mutableSetOf<String>()
                type.embeddedTypes.forEach {
                    validateType(it, active)
                    if (underlying(it) !is InterfaceGoType) error("embedded interface element must be an interface")
                }
                type.methods.forEach { method ->
                    if (!names.add(method.name)) error("duplicate interface method ${method.name}")
                    method.parameters.forEach { validateType(it.type, active, true) }
                    method.results.forEach { validateType(it, active, true) }
                }
                interfaceMethods(type)
            }
            is FunctionGoType -> {
                type.parameters.forEach { validateType(it.type, active, true) }
                type.results.forEach { validateType(it, active, true) }
            }
        }
    }

    private fun packageName(path: String): String = decodeGoStringLiteralBytes(path).toString(Charsets.UTF_8).substringAfterLast('/')
    private fun functionType(function: FunctionDeclaration) = FunctionGoType(function.parameterTypes.mapIndexed { i, t ->
        ParameterSyntax(function.parameters.getOrNull(i), t, function.variadic && i == function.parameterTypes.lastIndex)
    }, function.resultTypes)
    private fun namedType(type: GoTypeSyntax): String? = when (type) {
        is NamedGoType -> type.name
        is PointerGoType -> namedType(type.element)
        else -> null
    }
    private fun selectorBaseType(type: GoTypeSyntax): GoTypeSyntax = underlying((type as? PointerGoType)?.element ?: type)
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
                if (previous != null) error("duplicate interface method $name")
            }
        }
        iface.methods.forEach { method ->
            val signature = FunctionGoType(method.parameters, method.results)
            val previous = result.putIfAbsent(method.name, signature)
            if (previous != null) error("duplicate interface method ${method.name}")
        }
        return result
    }

    private fun methodSet(type: GoTypeSyntax): Map<String, FunctionGoType> {
        // A pointer to an interface does not inherit the interface's method set.
        if (type is PointerGoType && underlying(type.element) is InterfaceGoType) return emptyMap()
        val actual = underlying(type)
        if (actual is InterfaceGoType) return interfaceMethods(actual)
        val pointer = type is PointerGoType
        val result = linkedMapOf<String, FunctionGoType>()
        data class SearchNode(val type: GoTypeSyntax, val pointer: Boolean, val ancestors: Set<String>)
        var level = listOf(SearchNode(type, pointer, emptySet()))
        val blocked = mutableSetOf<String>()
        while (level.isNotEmpty()) {
            val candidates = linkedMapOf<String, MutableList<FunctionGoType>>()
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                when (val nodeType = selectorBaseType(node.type)) {
                    is InterfaceGoType -> interfaceMethods(nodeType).forEach { (name, signature) ->
                        candidates.getOrPut(name) { mutableListOf() } += signature
                    }
                    is StructGoType -> {
                        val baseName = namedType(node.type)
                        if (baseName != null) methods.values.forEach { method ->
                            val receiverType = method.receiver?.type ?: return@forEach
                            if (namedType(receiverType) != baseName || receiverType is PointerGoType && !node.pointer) return@forEach
                            candidates.getOrPut(method.name) { mutableListOf() } += functionType(method)
                        }
                        nodeType.fields.filter { it.names.isEmpty() }.forEach { field ->
                            val embedded = field.type
                            val key = embedded.toString()
                            if (key !in node.ancestors) next += SearchNode(
                                embedded,
                                node.pointer || embedded is PointerGoType,
                                node.ancestors + key
                            )
                        }
                    }
                    else -> {
                        val baseName = namedType(node.type)
                        if (baseName != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            if (namedType(receiverType) != baseName || receiverType is PointerGoType && !node.pointer) return@methodLoop
                            candidates.getOrPut(method.name) { mutableListOf() } += functionType(method)
                        }
                    }
                }
            }
            candidates.forEach { (name, methodsAtDepth) ->
                if (methodsAtDepth.size == 1 && name !in blocked) result[name] = methodsAtDepth.single()
                blocked += name
            }
            level = next
        }
        return result
    }

    private fun sameSignature(left: FunctionGoType, right: FunctionGoType): Boolean =
        left.parameters.size == right.parameters.size && left.results.size == right.results.size &&
            left.parameters.zip(right.parameters).all { (a, b) -> sameType(a.type, b.type) && a.variadic == b.variadic } &&
            left.results.zip(right.results).all { (a, b) -> sameType(a, b) }

    private fun sameType(left: GoTypeSyntax, right: GoTypeSyntax): Boolean {
        if (left == right) return true
        if ("byte" !in typeDeclarations && "uint8" !in typeDeclarations &&
            (left == byteType && right == NamedGoType("uint8") || right == byteType && left == NamedGoType("uint8"))) return true
        if ("rune" !in typeDeclarations && "int32" !in typeDeclarations &&
            (left == runeType && right == NamedGoType("int32") || right == runeType && left == NamedGoType("int32"))) return true
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
                    a.first == b.first && a.third.orEmpty() == b.third.orEmpty() && sameType(a.second, b.second)
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

    private fun sameArrayLength(left: Expression?, right: Expression?): Boolean {
        if (left == null || right == null) return left == null && right == null
        val leftValue = constantInteger(left)
        val rightValue = constantInteger(right)
        return if (leftValue != null && rightValue != null) leftValue == rightValue
        else arrayLengthSyntax(left) == arrayLengthSyntax(right)
    }

    private fun isConstantExpression(expression: Expression, scope: Scope): Boolean = when (expression) {
        is LiteralExpression -> expression.token.kind in setOf(
            TokenKind.INT, TokenKind.FLOAT, TokenKind.IMAG, TokenKind.CHAR, TokenKind.STRING
        )
        is NameExpression -> if (scope.getOrNull(expression.name) != null) scope.isConstant(expression.name)
            else expression.name in setOf("true", "false")
        is ParenthesizedExpression -> isConstantExpression(expression.expression, scope)
        is UnaryExpression -> expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.NOT, TokenKind.XOR) &&
            isConstantExpression(expression.operand, scope)
        is BinaryExpression -> isConstantExpression(expression.left, scope) && isConstantExpression(expression.right, scope)
        is CallExpression -> {
            val target = when (val function = expression.function) {
                is TypeExpression -> function.type
                is NameExpression -> if (scope.getOrNull(function.name) == null &&
                    (isBuiltinType(function.name) || function.name in typeDeclarations)) NamedGoType(function.name) else null
                else -> null
            }
            when {
                target != null -> expression.arguments.size == 1 && isConstantExpression(expression.arguments.single(), scope)
                expression.function == NameExpression("len") || expression.function == NameExpression("cap") ->
                    constantInteger(expression, scope) != null
                expression.function in setOf(NameExpression("complex"), NameExpression("real"), NameExpression("imag")) ->
                    expression.arguments.isNotEmpty() && expression.arguments.all { isConstantExpression(it, scope) }
                else -> false
            }
        }
        else -> false
    }

    private fun constantRational(expression: Expression, scope: Scope = globals): GoRational? = when (expression) {
        is NameExpression -> scope.constantRational(expression.name)
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> parseIntegerConstant(expression.token.lexeme)?.let(GoRational::of)
            TokenKind.CHAR -> decodeCharacterConstant(expression.token.lexeme)?.let(GoRational::of)
            TokenKind.FLOAT -> runCatching { GoRational.decimal(expression.token.lexeme) }.getOrNull()
            else -> null
        }
        is ParenthesizedExpression -> constantRational(expression.expression, scope)
        is UnaryExpression -> constantRational(expression.operand, scope)?.let { value -> when (expression.operator) {
            TokenKind.ADD -> value
            TokenKind.SUB -> value.negate()
            else -> null
        } }
        is BinaryExpression -> {
            val left = constantRational(expression.left, scope)
            val right = constantRational(expression.right, scope)
            if (left == null || right == null) null else when (expression.operator) {
                    TokenKind.ADD -> left + right
                    TokenKind.SUB -> left - right
                    TokenKind.MUL -> left * right
                    TokenKind.QUO -> {
                        if (right.numerator.signum() == 0) error("division by zero in constant expression")
                        val leftIsInteger = runCatching { isInteger(expressionType(expression.left, scope)) }.getOrDefault(false)
                        val rightIsInteger = runCatching { isInteger(expressionType(expression.right, scope)) }.getOrDefault(false)
                        if (leftIsInteger && rightIsInteger) {
                            val divisor = right.numerator
                            GoRational.of(left.numerator / divisor)
                        } else left / right
                    }
                    else -> null
                }
        }
        is CallExpression -> {
            val target = when (val function = expression.function) {
                is TypeExpression -> function.type
                is NameExpression -> if (scope.getOrNull(function.name) == null &&
                    (isBuiltinType(function.name) || function.name in typeDeclarations)) NamedGoType(function.name) else null
                else -> null
            }
            if (target == null || !isNumeric(target) || expression.arguments.size != 1 || expression.expandLastArgument) null
            else constantRational(expression.arguments.single(), scope)
        }
        else -> null
    }

    private fun constantInteger(expression: Expression, scope: Scope = globals): BigInteger? {
        constantRational(expression, scope)?.takeIf { it.isInteger() }?.let { return it.numerator }
        return when (expression) {
        is NameExpression -> scope.constantInteger(expression.name)
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> parseIntegerConstant(expression.token.lexeme)
            TokenKind.CHAR -> decodeCharacterConstant(expression.token.lexeme)
            else -> null
        }
        is ParenthesizedExpression -> constantInteger(expression.expression, scope)
        is UnaryExpression -> constantInteger(expression.operand, scope)?.let { value -> when (expression.operator) {
            TokenKind.ADD -> value
            TokenKind.SUB -> value.negate()
            TokenKind.XOR -> value.not()
            else -> null
        } }
        is CallExpression -> {
            val builtinLength = (expression.function == NameExpression("len") || expression.function == NameExpression("cap")) &&
                scope.getOrNull((expression.function as NameExpression).name) == null
            val lengthConstant = if (builtinLength &&
                expression.arguments.size == 1 && !expression.expandLastArgument) {
                val operand = expression.arguments.single()
                (if (expression.function == NameExpression("len")) constantStringLength(operand, scope) else null)
                    ?: if (!containsCallOrReceive(operand, scope)) {
                    val type = runCatching { underlying(expressionType(operand, scope)) }.getOrNull()
                    val array = when (type) {
                        is ArrayGoType -> type
                        is PointerGoType -> underlying(type.element) as? ArrayGoType
                        else -> null
                    }
                    array?.length?.let { constantInteger(it, scope) }
                } else null
            } else null
            if (lengthConstant != null) lengthConstant else {
                val target = when (val function = expression.function) {
                    is TypeExpression -> function.type
                    is NameExpression -> if (scope.getOrNull(function.name) == null &&
                        (isBuiltinType(function.name) || function.name in typeDeclarations))
                        NamedGoType(function.name) else null
                    else -> null
                }
                if (target != null && isInteger(target) && expression.arguments.size == 1)
                    constantInteger(expression.arguments.single(), scope) else null
            }
        }
        is BinaryExpression -> {
            val left = constantInteger(expression.left, scope)
            val right = constantInteger(expression.right, scope)
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
    }

    private fun constantStringLength(expression: Expression, scope: Scope): BigInteger? = when (expression) {
        is LiteralExpression -> if (expression.token.kind == TokenKind.STRING)
            stringLiteralByteLength(expression.token.lexeme)?.let(BigInteger::valueOf) else null
        is NameExpression -> scope.constantStringLength(expression.name)
        is ParenthesizedExpression -> constantStringLength(expression.expression, scope)
        is BinaryExpression -> if (expression.operator == TokenKind.ADD) {
            val left = constantStringLength(expression.left, scope)
            val right = constantStringLength(expression.right, scope)
            if (left != null && right != null) left + right else null
        } else null
        is CallExpression -> {
            val target = when (val function = expression.function) {
                is TypeExpression -> function.type
                is NameExpression -> if (scope.getOrNull(function.name) == null &&
                    (isBuiltinType(function.name) || function.name in typeDeclarations)) NamedGoType(function.name) else null
                else -> null
            }
            if (target == null || underlying(target) != stringType || expression.arguments.size != 1 || expression.expandLastArgument) null
            else constantStringLength(expression.arguments.single(), scope) ?: constantInteger(expression.arguments.single(), scope)?.let { value ->
                val codePoint = runCatching { value.intValueExact() }.getOrNull()
                val rune = if (codePoint == null || codePoint !in 0..Character.MAX_CODE_POINT || codePoint in 0xd800..0xdfff)
                    0xfffd else codePoint
                BigInteger.valueOf(when {
                    rune <= 0x7f -> 1L
                    rune <= 0x7ff -> 2L
                    rune <= 0xffff -> 3L
                    else -> 4L
                })
            }
        }
        else -> null
    }

    private fun stringLiteralByteLength(text: String): Long? = runCatching {
        if (text.first() == '`') return@runCatching text.substring(1, text.length - 1).replace("\r", "").toByteArray(Charsets.UTF_8).size.toLong()
        val body = text.substring(1, text.length - 1)
        var length = 0L
        var i = 0
        while (i < body.length) {
            val character = body[i++]
            if (character != '\\') {
                val codePoint = if (Character.isHighSurrogate(character) && i < body.length && Character.isLowSurrogate(body[i]))
                    Character.toCodePoint(character, body[i++]) else character.code
                length += when {
                    codePoint <= 0x7f -> 1
                    codePoint <= 0x7ff -> 2
                    codePoint <= 0xffff -> 3
                    else -> 4
                }
                continue
            }
            when (val escaped = body[i++]) {
                'x' -> { i += 2; length++ }
                in '0'..'7' -> { i += 2; length++ }
                'u', 'U' -> {
                    val digits = if (escaped == 'u') 4 else 8
                    val codePoint = body.substring(i, i + digits).toLong(16).toInt()
                    length += when {
                        codePoint <= 0x7f -> 1
                        codePoint <= 0x7ff -> 2
                        codePoint <= 0xffff -> 3
                        else -> 4
                    }
                    i += digits
                }
                else -> length++
            }
        }
        length
    }.getOrNull()

    private fun containsCallOrReceive(expression: Expression, scope: Scope): Boolean = when (expression) {
        is CallExpression -> {
            val conversion = when (val target = expression.function) {
                is TypeExpression -> true
                is NameExpression -> scope.getOrNull(target.name) == null &&
                    (scope.typeBinding(target.name) != null || isBuiltinType(target.name) || target.name in typeDeclarations)
                else -> false
            }
            !conversion || expression.arguments.any { containsCallOrReceive(it, scope) }
        }
        is UnaryExpression -> expression.operator == TokenKind.ARROW || containsCallOrReceive(expression.operand, scope)
        is BinaryExpression -> containsCallOrReceive(expression.left, scope) || containsCallOrReceive(expression.right, scope)
        is ParenthesizedExpression -> containsCallOrReceive(expression.expression, scope)
        is SelectorExpression -> containsCallOrReceive(expression.receiver, scope)
        is IndexExpression -> containsCallOrReceive(expression.receiver, scope) || containsCallOrReceive(expression.index, scope)
        is SliceExpression -> containsCallOrReceive(expression.receiver, scope) ||
            listOfNotNull(expression.low, expression.high).any { containsCallOrReceive(it, scope) }
        is TypeAssertionExpression -> containsCallOrReceive(expression.receiver, scope)
        is CompositeLiteral -> expression.elements.any { (it.key?.let { key -> containsCallOrReceive(key, scope) } ?: false) ||
            containsCallOrReceive(it.value, scope) }
        is ElidedCompositeLiteral -> expression.elements.any { (it.key?.let { key -> containsCallOrReceive(key, scope) } ?: false) ||
            containsCallOrReceive(it.value, scope) }
        is FunctionLiteralExpression -> true
        else -> false
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
            ?: when (type.name) {
                "byte" -> NamedGoType("uint8")
                "rune" -> NamedGoType("int32")
                "error" -> errorInterfaceType
                else -> type
            }
        else -> type
    }
    private fun isNamed(type: GoTypeSyntax) = type is NamedGoType && !type.name.startsWith("#")
    private fun isUntyped(type: GoTypeSyntax) = type is NamedGoType && type.name.startsWith("#untyped-")
    private fun isBuiltinType(name: String) = name in builtinTypes || name == "error"
    private fun isNumeric(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt, untypedRune, untypedFloat, untypedComplex -> true
        is NamedGoType -> t.name in integerNames || t.name in floatNames || t.name in complexNames
        else -> false
    }
    private fun isFloatArgument(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt, untypedRune, untypedFloat -> true
        is NamedGoType -> t.name in floatNames
        else -> false
    }
    private fun isOrderedNumeric(type: GoTypeSyntax): Boolean = isInteger(type) || when (val t = underlying(type)) {
        untypedFloat -> true
        is NamedGoType -> t.name in floatNames
        else -> false
    }
    private fun isInteger(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt, untypedRune -> true
        is NamedGoType -> t.name in integerNames
        else -> false
    }
    private fun isUnsignedInteger(type: GoTypeSyntax): Boolean =
        (underlying(type) as? NamedGoType)?.name in setOf("uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte")
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
        untypedRune -> runeType
        untypedFloat -> NamedGoType("float64")
        untypedComplex -> NamedGoType("complex128")
        untypedString -> stringType
        untypedBool -> boolType
        else -> type
    }
    private fun requireBoolean(type: GoTypeSyntax, context: String) { if (!isBoolean(type)) error("$context must be boolean") }
    private fun requireInteger(type: GoTypeSyntax, context: String) { if (!isInteger(type)) error("$context must be integer") }
    private fun requireCall(expression: Expression, scope: Scope, context: String) {
        val call = expression.unparenthesized() as? CallExpression ?: error("$context requires function call")
        if (isTypeConversion(call.function, scope)) error("$context requires function or method call")
        callResults(call, scope)
    }

    private fun isTypeConversion(expression: Expression, scope: Scope): Boolean = when (val target = expression.unparenthesized()) {
        is TypeExpression -> true
        is NameExpression -> scope.getOrNull(target.name) == null &&
            (scope.typeBinding(target.name) != null || isBuiltinType(target.name) || target.name in typeDeclarations)
        else -> false
    }
    private fun requireCount(name: String, args: List<Expression>, count: Int, actualCount: Int = args.size) {
        if (actualCount != count) error("$name expects $count arguments")
    }
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
        private val typeNames = linkedMapOf<String, String>()
        private val integerConstants = linkedMapOf<String, BigInteger>()
        private val constantNames = linkedSetOf<String>()
        fun child() = Scope(this)
        private val stringLengths = linkedMapOf<String, BigInteger>()
        private val rationalConstants = linkedMapOf<String, GoRational>()
        private val stringIdentities = linkedMapOf<String, String>()
        private val booleanConstants = linkedMapOf<String, Boolean>()
        private val functionNames = linkedSetOf<String>()
        fun define(
            name: String,
            type: GoTypeSyntax,
            integerConstant: BigInteger? = null,
            stringLength: BigInteger? = null,
            isConstant: Boolean = false,
            rationalConstant: GoRational? = null,
            stringIdentity: String? = null,
            booleanConstant: Boolean? = null,
            isFunction: Boolean = false
        ) {
            values[name] = type
            if (isFunction) functionNames += name else functionNames -= name
            if (integerConstant == null) integerConstants.remove(name) else integerConstants[name] = integerConstant
            if (stringLength == null) stringLengths.remove(name) else stringLengths[name] = stringLength
            if (rationalConstant == null) rationalConstants.remove(name) else rationalConstants[name] = rationalConstant
            if (stringIdentity == null) stringIdentities.remove(name) else stringIdentities[name] = stringIdentity
            if (booleanConstant == null) booleanConstants.remove(name) else booleanConstants[name] = booleanConstant
            if (isConstant) constantNames += name else constantNames -= name
        }
        fun defineType(name: String, identity: String) { typeNames[name] = identity }
        fun typeBinding(name: String): String? = typeNames[name] ?: parent?.typeBinding(name)
        fun containsLocal(name: String) = name in values || name in typeNames
        fun get(name: String): GoTypeSyntax = getOrNull(name) ?: throw GoTypeError("undefined: $name")
        fun getOrNull(name: String): GoTypeSyntax? = values[name] ?: parent?.getOrNull(name)
        fun isVariable(name: String): Boolean = if (name in values)
            name !in constantNames && name !in functionNames else parent?.isVariable(name) == true
        fun constantInteger(name: String): BigInteger? = if (name in values) integerConstants[name] else parent?.constantInteger(name)
        fun constantRational(name: String): GoRational? = if (name in values) rationalConstants[name]
            ?: integerConstants[name]?.let { GoRational.of(it) } else parent?.constantRational(name)
        fun constantStringLength(name: String): BigInteger? = if (name in values) stringLengths[name] else parent?.constantStringLength(name)
        fun constantStringIdentity(name: String): String? = if (name in values) stringIdentities[name] else parent?.constantStringIdentity(name)
        fun constantBoolean(name: String): Boolean? = if (name in values) booleanConstants[name] else parent?.constantBoolean(name)
        fun isConstant(name: String): Boolean = if (name in values) name in constantNames else parent?.isConstant(name) == true
    }

    companion object {
        private val untypedInt = NamedGoType("#untyped-int")
        private val untypedRune = NamedGoType("#untyped-rune")
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
