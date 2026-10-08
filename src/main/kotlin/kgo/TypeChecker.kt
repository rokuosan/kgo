package kgo

import java.math.BigInteger
import java.util.Collections
import java.util.IdentityHashMap
import java.util.concurrent.atomic.AtomicInteger

class GoTypeError(message: String) : RuntimeException(message)

internal data class ConstantComplexValue(val real: GoRational, val imaginary: GoRational)
internal data class ExportedConstant(
    val type: GoTypeSyntax,
    val integer: BigInteger?,
    val rational: GoRational?,
    val stringLength: BigInteger?,
    val stringIdentity: String?,
    val boolean: Boolean?,
    val complex: ConstantComplexValue?
)
private data class TypeMethod(
    val signature: FunctionGoType,
    val pointerReceiver: Boolean,
    val declaration: FunctionDeclaration? = null
)

/** Static checks for the declaration and statement forms currently represented by the AST. */
class TypeChecker(
    private val importedPackages: Map<String, TypeChecker> = emptyMap(),
    private val sourceImportPath: String? = null
) {
    private val typeDeclarations = linkedMapOf<String, GoTypeSyntax>()
    private val checkedRuntimeTypeDeclarations = linkedMapOf<String, GoTypeSyntax>()
    private val checkedFunctionTypes = IdentityHashMap<FunctionDeclaration, FunctionGoType>()
    private val functions = linkedMapOf<String, FunctionDeclaration>()
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val methods = linkedMapOf<String, FunctionDeclaration>()
    private val packagePaths = linkedMapOf<String, String>()
    private var dotImportPaths = mutableSetOf<String>()
    private var usedPackageAliases = mutableSetOf<String>()
    private var usedDotImportPaths = mutableSetOf<String>()
    private val usedPackageAliasesByFile = IdentityHashMap<GoFile, MutableSet<String>>()
    private val usedDotImportsByFile = IdentityHashMap<GoFile, MutableSet<String>>()
    private val nextLocalTypeIdentity = AtomicInteger()
    private val terminatingPanicCalls = Collections.newSetFromMap(IdentityHashMap<CallExpression, Boolean>())
    private val globals = Scope()
    private val calledMethodsByFunction = IdentityHashMap<FunctionDeclaration, MutableSet<FunctionDeclaration>>()
    private val calledMethodsByExpression = IdentityHashMap<Expression, MutableSet<FunctionDeclaration>>()
    private var dependencyFunction: FunctionDeclaration? = null
    private var dependencyExpression: Expression? = null
    private var checkedVariableInitializationOrder: List<PackageVariableInitialization> = emptyList()
    private var resultTypes: List<GoTypeSyntax> = emptyList()
    private var resultNames: List<String?> = emptyList()
    private var functionLabels: Map<String, LabelInfo> = emptyMap()
    private var usedLabels: MutableSet<String> = mutableSetOf()
    private var labelBlockPath: List<Any> = emptyList()
    private var blockStatementIndices: Map<Any, Int> = emptyMap()
    internal var packageName: String? = null
        private set
    private var packageLevelNames: Set<String> = emptySet()
    private var packageIdentity: String? = sourceImportPath

    fun check(file: GoFile) = checkFiles(listOf(file))

    fun checkFiles(files: List<GoFile>) {
        usedPackageAliasesByFile.clear()
        usedDotImportsByFile.clear()
        if (files.isEmpty()) error("package has no source files")
        val packageName = files.first().packageName
        this.packageName = packageName
        this.packageIdentity = sourceImportPath ?: packageName
        if (packageName == "_") error("package name cannot be _")
        if (files.any { it.packageName != packageName }) error("source files declare different package names")
        val declarations = files.flatMap { file -> file.declarations.map { file to it } }
        packageLevelNames = declarations.flatMap { (_, declaration) -> when (declaration) {
            is VariableDeclaration -> declaration.names
            is ConstantDeclaration -> declaration.names
            is TypeDeclaration -> listOf(declaration.name)
            is FunctionDeclaration -> if (declaration.receiver == null && declaration.name != "init")
                listOf(declaration.name) else emptyList()
            else -> emptyList()
        } }.filter { it != "_" }.toSet()
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
            if (declaration.name == "_") return@forEach
            if (typeDeclarations.putIfAbsent(declaration.name, declaration.type) != null) error("type ${declaration.name} redeclared")
        }
        for ((_, declaration) in declarations) when (declaration) {
            is TypeDeclaration -> Unit
            is FunctionDeclaration -> {
                val receiver = declaration.receiver
                if (receiver != null && declaration.name == "_") error("method name cannot be blank")
                if (receiver == null) {
                    if (declaration.name == "init") initFunctions += declaration
                    else if (declaration.name != "_" && functions.putIfAbsent(declaration.name, declaration) != null)
                        error("function ${declaration.name} redeclared")
                } else {
                    val base = (receiver.type as? PointerGoType)?.element ?: receiver.type
                    val baseName = base as? NamedGoType ?: error("method receiver must be a defined type")
                    if (baseName.name !in typeDeclarations) error("method receiver type ${baseName.name} must be defined in this package")
                    if (underlying(baseName) is InterfaceGoType || underlying(baseName) is PointerGoType)
                        error("invalid method receiver type ${baseName.name}")
                    if (declaration.name != "_") {
                        val key = methodKey(receiver.type, declaration.name)
                        if (methods.putIfAbsent(key, declaration) != null)
                            error("method ${declaration.name} redeclared for ${baseName.name}")
                    }
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
                val scope = globals.child().also { initializerScope ->
                    if ("iota" !in packageLevelNames && "iota" !in packagePaths) {
                        initializerScope.define(
                            "iota", untypedInt, BigInteger.valueOf(declaration.iotaIndex.toLong()), isConstant = true
                        )
                    }
                }
                val type = expressionTypes(listOf(expression), 1, scope).singleOrNull()
                    ?: error("constant initializer count mismatch")
                if (!isConstantExpression(expression, scope)) error("constant initializer is not constant")
                val declaredType = declaration.type?.let { resolveLocalType(it, globals) }
                declaredType?.let {
                    validateType(it)
                    requireAssignable(type, it, "constant initializer", expression, scope)
                }
                if (name != "_") globals.define(
                    name, declaredType ?: type,
                    constantInteger(expression, scope), constantStringLength(expression, scope), isConstant = true,
                    rationalConstant = constantRational(expression, scope),
                    stringIdentity = constantStringIdentity(expression, scope),
                    booleanConstant = constantBoolean(expression, scope),
                    complexConstant = constantComplex(expression, scope)
                )
            }
        }
        for ((sourceFile, declaration) in declarations) {
            if (declaration is VariableDeclaration && declaration.type != null) withFileImports(sourceFile) {
                val resolvedType = resolveLocalType(declaration.type, globals)
                declaration.names.filter { it != "_" }.forEach { name -> globals.define(name, resolvedType) }
            }
        }
        checkedFunctionTypes.clear()
        for ((sourceFile, declaration) in declarations) {
            if (declaration is FunctionDeclaration) withFileImports(sourceFile) {
                checkedFunctionTypes[declaration] = resolveFunctionType(declaration, globals)
            }
        }
        functions.forEach { (name, function) -> globals.define(name, functionType(function), isFunction = true) }
        methods.forEach { (key, function) -> globals.define(key, functionType(function)) }
        val variableFiles = IdentityHashMap<VariableDeclaration, GoFile>()
        declarations.forEach { (file, declaration) ->
            (declaration as? VariableDeclaration)?.let { variableFiles[it] = file }
        }
        if (globalVariables.any { it.values.isNotEmpty() && it.values.size != it.names.size && it.values.size != 1 })
            error("initializer count mismatch")
        val initialVariableOrder = globalVariableInitializationOrder(globalVariables)
        for (initialization in initialVariableOrder) {
            val declaration = initialization.declaration
            val names = initialization.indices.map(declaration.names::get)
            val expressions = initialization.initializerExpressions()
            val sourceFile = variableFiles.getValue(declaration)
            withFileImports(sourceFile) {
                val previousDependencyExpression = dependencyExpression
                val values = try {
                    expressions.flatMap { expression ->
                        dependencyExpression = expression
                        expressionTypes(listOf(expression), if (expressions.size == 1) names.size else 1, globals)
                    }
                } finally { dependencyExpression = previousDependencyExpression }
                if (expressions.isNotEmpty() && values.size != names.size)
                    error("initializer count mismatch")
                val declaredType = declaration.type?.let { resolveLocalType(it, globals) }
                if (declaredType != null) {
                    validateType(declaredType)
                    requireAssignableValues(values, expressions, declaredType, "initializer", globals)
                } else if (expressions.isNotEmpty()) requireDefaultValues(values, expressions, "initializer", globals)
                names.forEachIndexed { i, name ->
                    if (name != "_") globals.define(name, declaredType ?: defaultType(values.getOrNull(i) ?: intType))
                }
            }
        }
        for ((sourceFile, declaration) in declarations) {
            if (declaration is TypeDeclaration) withFileImports(sourceFile) {
                if (declaration.name == "_") validateType(declaration.type)
                else {
                    validateType(NamedGoType(declaration.name))
                    checkedRuntimeTypeDeclarations[declaration.name] =
                        resolveLocalType(typeDeclarations.getValue(declaration.name), globals)
                }
            }
        }
        for ((sourceFile, declaration) in declarations) {
            if (declaration is FunctionDeclaration) withFileImports(sourceFile) { checkFunction(declaration) }
        }
        checkedVariableInitializationOrder = globalVariableInitializationOrder(globalVariables)
        files.forEach { file ->
            val usedAliases = usedPackageAliasesByFile[file].orEmpty()
            val usedDotImports = usedDotImportsByFile[file].orEmpty()
            file.importBindings().forEach { binding ->
                val spec = binding.specification
                if (spec.alias == ".") {
                    if (binding.path !in usedDotImports) error("dot-imported package ${binding.path} is not used")
                    return@forEach
                }
                val alias = binding.alias
                if (alias != "_" && alias !in usedAliases)
                    error("imported package $alias is not used")
            }
        }
        initFunctions.forEach { if (it.parameters.isNotEmpty() || it.resultTypes.isNotEmpty()) error("init must have no parameters or results") }
        if (packageName == "main") checkMain()
    }

    private fun <T> withFileImports(file: GoFile, action: () -> T): T {
        val previous = packagePaths.toMap()
        val previousDotImports = dotImportPaths
        val previousUsedAliases = usedPackageAliases
        val previousUsedDotImports = usedDotImportPaths
        usedPackageAliases = mutableSetOf()
        usedDotImportPaths = mutableSetOf()
        return try {
            packagePaths.clear()
            dotImportPaths = mutableSetOf()
            val importedNames = mutableSetOf<String>()
            val packageNames = importedPackages.mapValues { (_, checker) ->
                checker.packageName ?: error("imported package was not checked")
            }
            val imports = try {
                file.importBindings(packageNames)
            } catch (failure: RuntimeGoError) {
                error("invalid import path: ${failure.message}")
            }
            val importedPaths = mutableSetOf<String>()
            imports.forEach { binding ->
                val spec = binding.specification
                val path = binding.path
                if (path.isEmpty()) error("import path cannot be empty")
                // Import identity is the decoded path, not its source spelling. For example,
                // "fmt" and "f\\x6dt" name the same package and cannot both be imported.
                if (!importedPaths.add(path))
                    error("package $path imported more than once in this file")
                val alias = when (spec.alias) {
                    "." -> {
                        dotImportPaths += path
                        val dotImportedNames = when (standardPackageName(path)) {
                            "fmt" -> GoFmtPackage.exportedNames
                            "math" -> GoMathPackage.exportedNames
                            "unsafe" -> GoUnsafePackage.exportedNames
                            "runtime" -> GoRuntimePackage.exportedTypes
                            else -> emptySet()
                        } + importedPackages[path]?.exportedNames().orEmpty()
                        val collision = dotImportedNames.firstOrNull { !importedNames.add(it) }
                        if (collision != null) error("dot-imported identifier $collision redeclared")
                        null
                    }
                    "_" -> null
                    null -> binding.alias
                    else -> spec.alias
                } ?: return@forEach
                if (!importedNames.add(alias)) error("package name $alias imported more than once in a file")
                packagePaths[alias] = path
            }
            val collision = importedNames.firstOrNull { it in typeDeclarations || globals.containsLocal(it) }
            if (collision != null) error("package import name $collision conflicts with a package declaration")
            val result = action()
            usedPackageAliasesByFile.getOrPut(file) { mutableSetOf() }.addAll(usedPackageAliases)
            usedDotImportsByFile.getOrPut(file) { mutableSetOf() }.addAll(usedDotImportPaths)
            result
        } finally {
            packagePaths.clear()
            packagePaths.putAll(previous)
            dotImportPaths = previousDotImports
            usedPackageAliases = previousUsedAliases
            usedDotImportPaths = previousUsedDotImports
        }
    }

    private fun importedPackagePath(alias: String): String? = packagePaths[alias]?.also {
        usedPackageAliases += alias
    }

    internal fun exportedNames(): Set<String> =
        packageLevelNames.filterTo(linkedSetOf(), ::isExportedIdentifier)

    internal fun runtimeTypeDefinitions(): Map<String, GoTypeSyntax> =
        checkedRuntimeTypeDeclarations.toMap()

    internal fun runtimeFunctionTypes(): Map<FunctionDeclaration, FunctionGoType> =
        IdentityHashMap<FunctionDeclaration, FunctionGoType>().also { it.putAll(checkedFunctionTypes) }

    internal fun runtimeVariableInitializationOrder(): List<PackageVariableInitialization> =
        checkedVariableInitializationOrder.toList()

    internal fun exportedFunctionType(name: String, importPath: String? = null): FunctionGoType? =
        if (isExportedIdentifier(name)) functions[name]?.let(::functionType)
            ?.let { externalizeType(it, importPath) as FunctionGoType } else null

    internal fun exportedVariableType(name: String, importPath: String? = null): GoTypeSyntax? =
        if (isExportedIdentifier(name) && globals.isVariable(name)) globals.getOrNull(name)?.let { externalizeType(it, importPath) } else null

    internal fun hasExportedType(name: String): Boolean = isExportedIdentifier(name) && name in typeDeclarations

    internal fun exportedConstant(name: String, importPath: String? = null): ExportedConstant? {
        if (!isExportedIdentifier(name) || !globals.isConstant(name)) return null
        return ExportedConstant(
            externalizeType(globals.get(name), importPath), globals.constantInteger(name), globals.constantRational(name),
            globals.constantStringLength(name), globals.constantStringIdentity(name),
            globals.constantBoolean(name), globals.constantComplex(name)
        )
    }

    private fun isExportedIdentifier(name: String): Boolean = GoUnicode6.isExportedIdentifier(name)

    private fun externalizeType(type: GoTypeSyntax, importPath: String?): GoTypeSyntax {
        fun visit(current: GoTypeSyntax): GoTypeSyntax = when (current) {
            is NamedGoType -> if (importPath != null && current.name in typeDeclarations)
                QualifiedGoType(importPath, current.name) else canonicalPredeclaredAlias(current)
            is PointerGoType -> PointerGoType(visit(current.element))
            is SliceGoType -> SliceGoType(visit(current.element))
            is ArrayGoType -> ArrayGoType(current.length?.let(::externalizeArrayLength), visit(current.element))
            is MapGoType -> MapGoType(visit(current.key), visit(current.value))
            is ChannelGoType -> ChannelGoType(visit(current.element), current.direction)
            is StructGoType -> StructGoType(current.fields.map { field ->
                field.copy(
                    type = visit(field.type),
                    declaringPackagePath = field.declaringPackagePath ?: importPath,
                    packagePath = field.packagePath ?: importPath.takeIf { path ->
                        field.names.any(GoUnicode6::isUnexportedIdentifier) ||
                            field.names.isEmpty() && GoUnicode6.isUnexportedIdentifier(embeddedFieldName(field.type))
                    }
                )
            })
            is InterfaceGoType -> InterfaceGoType(current.methods.map { method -> method.copy(
                parameters = method.parameters.map { it.copy(type = visit(it.type)) },
                results = method.results.map(::visit),
                packagePath = method.packagePath ?: importPath.takeIf { GoUnicode6.isUnexportedIdentifier(method.name) }
            ) }, current.embeddedTypes.map(::visit))
            is FunctionGoType -> FunctionGoType(current.parameters.map { it.copy(type = visit(it.type)) }, current.results.map(::visit))
            is QualifiedGoType -> current
        }
        return visit(type)
    }

    private fun externalizeArrayLength(expression: Expression): Expression =
        constantInteger(expression)?.let { value ->
            LiteralExpression(Token(TokenKind.INT, value.toString(), Position(0, 1, 1)))
        } ?: expression

    private fun dotImportedIdentifierType(name: String): Pair<String, GoTypeSyntax>? {
        dotImportPaths.forEach { path ->
            val type = when (standardPackageName(path)) {
                "fmt" -> GoFmtPackage.functionType(name)
                "math" -> GoMathPackage.memberType(name)
                "unsafe" -> GoUnsafePackage.memberType(name)
                else -> null
            } ?: importedPackages[path]?.let { imported ->
                imported.exportedFunctionType(name, path) ?: imported.exportedConstant(name, path)?.type
                    ?: imported.exportedVariableType(name, path)
            }
            if (type != null) return path to type
        }
        return null
    }

    private fun importedConstant(path: String, name: String): ExportedConstant? =
        importedPackages[path]?.exportedConstant(name, path)

    private fun dotImportedConstant(name: String): Pair<String, ExportedConstant>? =
        dotImportPaths.firstNotNullOfOrNull { path -> importedConstant(path, name)?.let { path to it } }

    private fun dotImportedType(name: String): QualifiedGoType? = dotImportPaths.firstNotNullOfOrNull { path ->
        if (standardPackageName(path) == "unsafe" && name in GoUnsafePackage.exportedTypes) {
            usedDotImportPaths += path
            QualifiedGoType(path, name)
        } else if (standardPackageName(path) == "runtime" && name in GoRuntimePackage.exportedTypes) {
            usedDotImportPaths += path
            QualifiedGoType(path, name)
        } else importedPackages[path]?.takeIf { it.hasExportedType(name) }?.let {
            usedDotImportPaths += path
            QualifiedGoType(path, name)
        }
    }

    private fun importedPackageType(expression: SelectorExpression, scope: Scope): QualifiedGoType? {
        val alias = (expression.receiver as? NameExpression)?.name ?: return null
        if (scope.getOrNull(alias) != null || scope.typeBinding(alias) != null) return null
        val path = importedPackagePath(alias) ?: return null
        if (standardPackageName(path) == "unsafe" && expression.field in GoUnsafePackage.exportedTypes)
            return QualifiedGoType(path, expression.field)
        if (standardPackageName(path) == "runtime" && expression.field in GoRuntimePackage.exportedTypes)
            return QualifiedGoType(path, expression.field)
        return importedPackages[path]?.takeIf { it.hasExportedType(expression.field) }
            ?.let { QualifiedGoType(path, expression.field) }
    }

    private fun checkMain() {
        val main = functions["main"] ?: error("main function not found")
        if (main.parameters.isNotEmpty() || main.resultTypes.isNotEmpty()) error("main must have no parameters or results")
    }

    private fun globalVariableInitializationOrder(
        variables: List<VariableDeclaration>
    ): List<PackageVariableInitialization> {
        val initializations = packageVariableInitializations(variables)
        val ownerByName = buildMap {
            initializations.forEachIndexed { index, initialization ->
                initialization.indices.map(initialization.declaration.names::get).filter { it != "_" }
                    .forEach { put(it, index) }
            }
        }
        val dependencies = initializations.map { initialization ->
            val expressions = initialization.initializerExpressions()
            val references = expressions.flatMapTo(linkedSetOf(), ::referencedNames)
            val methodDependencies = expressions.flatMap { calledMethodsByExpression[it].orEmpty() }
            addFunctionDependencies(references, methodDependencies)
            references.mapNotNull(ownerByName::get).distinct().toSet()
        }
        val initialized = BooleanArray(initializations.size)
        val result = mutableListOf<PackageVariableInitialization>()
        while (result.size < initializations.size) {
            val next = initializations.indices.firstOrNull { index ->
                !initialized[index] && dependencies[index].all { initialized[it] }
            } ?: error("initialization cycle involving ${initializations.filterIndexed { index, _ -> !initialized[index] }
                .flatMap { initialization -> initialization.indices.map(initialization.declaration.names::get) }
                .distinct().joinToString()}")
            initialized[next] = true
            result += initializations[next]
        }
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
        is FunctionLiteralExpression -> GoPackageDependencies.functionLiteralReferences(
            expression.parameters, expression.resultNames, expression.body
        )
    }

    private fun addFunctionDependencies(
        references: MutableSet<String>,
        methodDependencies: Iterable<FunctionDeclaration> = emptyList()
    ) {
        val pending = ArrayDeque<FunctionDeclaration>()
        references.mapNotNull(functions::get).forEach(pending::addLast)
        methodDependencies.forEach(pending::addLast)
        val visited = Collections.newSetFromMap(IdentityHashMap<FunctionDeclaration, Boolean>())
        while (pending.isNotEmpty()) {
            val function = pending.removeFirst()
            if (!visited.add(function)) continue
            val functionReferences = GoPackageDependencies.functionReferences(function)
            references += functionReferences
            functionReferences.mapNotNull(functions::get).forEach(pending::addLast)
            calledMethodsByFunction[function].orEmpty().forEach(pending::addLast)
        }
    }

    private fun checkFunction(function: FunctionDeclaration) {
        val signature = functionType(function)
        val scope = globals.child(trackLocalUsage = true)
        function.receiver?.let { receiver ->
            val receiverType = resolveLocalType(receiver.type, globals)
            validateType(receiverType)
            receiver.name?.takeIf { it != "_" }?.let { name ->
                if (scope.containsLocal(name)) error("$name redeclared in function signature")
                scope.define(name, receiverType)
            }
        }
        function.parameters.forEachIndexed { i, name ->
            val type = signature.parameters.getOrNull(i)?.type ?: error("missing type for parameter ${name ?: i}")
            validateType(type)
            if (name != null && name != "_") {
                if (scope.containsLocal(name)) error("$name redeclared in function signature")
                scope.define(name, type)
            }
        }
        signature.results.forEach(::validateType)
        val names = function.resultNames.ifEmpty { List(signature.results.size) { null } }
        if (names.size != signature.results.size) error("result name count does not match result type count")
        names.forEachIndexed { index, name ->
            if (name != null && name != "_") {
                if (scope.containsLocal(name)) error("$name redeclared in function signature")
                scope.define(name, signature.results[index])
            }
        }
        val body = function.body ?: return
        val previousResults = resultTypes
        val previousResultNames = resultNames
        val previousLabels = functionLabels
        val previousUsedLabels = usedLabels
        val previousBlockPath = labelBlockPath
        val previousBlockIndices = blockStatementIndices
        val previousDependencyFunction = dependencyFunction
        dependencyFunction = function
        resultTypes = signature.results
        resultNames = names
        functionLabels = collectLabels(body)
        usedLabels = mutableSetOf()
        labelBlockPath = emptyList()
        blockStatementIndices = emptyMap()
        try {
            validateBranchTargets(body)
            checkBlock(body, scope, reuseScope = true)
            scope.unusedLocalVariable()?.let { error("$it declared and not used") }
            if (signature.results.isNotEmpty() && !endsWithGo10Exit(body))
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
            dependencyFunction = previousDependencyFunction
        }
    }

    private fun checkBlock(block: BlockStatement, parent: Scope, reuseScope: Boolean = false) {
        val scope = if (reuseScope) parent else parent.child()
        val previousTypes = typeDeclarations.toMap()
        val previousPath = labelBlockPath
        labelBlockPath = previousPath + block
        try {
            block.statements.forEachIndexed { index, statement ->
                withStatementIndex(block, index) { checkStatement(statement, scope) }
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

    private fun endsWithGo10Exit(block: BlockStatement): Boolean =
        endsWithGo10Exit(block.statements, label = "")

    private fun endsWithGo10Exit(statements: List<Statement>, label: String): Boolean =
        statements.lastOrNull { it != EmptyStatement }?.let { endsWithGo10Exit(it, label) } == true

    private fun endsWithGo10Exit(statement: Statement, label: String = ""): Boolean = when (statement) {
        is LabeledStatement -> endsWithGo10Exit(statement.statement, statement.label)
        is ReturnStatement -> true
        is BranchStatement -> statement.kind == TokenKind.GOTO || statement.kind == TokenKind.FALLTHROUGH
        is BlockStatement -> endsWithGo10Exit(statement.statements, label = "")
        is ExpressionStatement -> (statement.expression.unparenthesized() as? CallExpression)
            ?.let(terminatingPanicCalls::contains) == true
        is IfStatement -> statement.elseBranch != null &&
            endsWithGo10Exit(statement.thenBranch) && endsWithGo10Exit(statement.elseBranch)
        is ForStatement -> statement.rangeClause == null && statement.condition == null &&
            !hasBreak(statement.body, label, implicit = true)
        is SwitchStatement -> isTerminatingSwitch(statement.clauses.map { (it.expressions == null) to it.statements }, label)
        is TypeSwitchStatement -> isTerminatingSwitch(statement.clauses.map { (it.types == null) to it.statements }, label)
        is SelectStatement -> statement.cases.all { clause ->
            endsWithGo10Exit(clause.statements, label = "") &&
                !hasBreak(clause.statements, label, implicit = true)
        }
        else -> false
    }

    private fun isTerminatingSwitch(clauses: List<Pair<Boolean, List<Statement>>>, label: String): Boolean {
        var hasDefault = false
        for ((isDefault, statements) in clauses) {
            if (isDefault) hasDefault = true
            if (!endsWithGo10Exit(statements, label = "") || hasBreak(statements, label, implicit = true))
                return false
        }
        return hasDefault
    }

    private fun hasBreak(statement: Statement, label: String, implicit: Boolean): Boolean = when (statement) {
        is BranchStatement -> statement.kind == TokenKind.BREAK &&
            (statement.label?.let { it == label } ?: implicit)
        is LabeledStatement -> hasBreak(statement.statement, label, implicit)
        is BlockStatement -> hasBreak(statement.statements, label, implicit)
        is IfStatement -> hasBreak(statement.thenBranch, label, implicit) ||
            (statement.elseBranch?.let { hasBreak(it, label, implicit) } ?: false)
        is ForStatement -> label.isNotEmpty() && hasBreak(statement.body, label, implicit = false)
        is SwitchStatement -> label.isNotEmpty() && statement.clauses.any {
            hasBreak(it.statements, label, implicit = false)
        }
        is TypeSwitchStatement -> label.isNotEmpty() && statement.clauses.any {
            hasBreak(it.statements, label, implicit = false)
        }
        is SelectStatement -> label.isNotEmpty() && statement.cases.any {
            hasBreak(it.statements, label, implicit = false)
        }
        else -> false
    }

    private fun hasBreak(statements: List<Statement>, label: String, implicit: Boolean): Boolean =
        statements.any { hasBreak(it, label, implicit) }

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
        val ownerBlock: Any?,
        val statementIndex: Int?
    )

    private fun collectLabels(body: BlockStatement): Map<String, LabelInfo> {
        val labels = linkedMapOf<String, LabelInfo>()
        fun visit(statement: Statement, path: List<Any>, ownerBlock: Any?, statementIndex: Int?) {
            when (statement) {
                is LabeledStatement -> {
                    if (statement.label == "_") error("label cannot be blank")
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
                    statement.clauses.forEach { clause ->
                        clause.statements.forEachIndexed { index, child -> visit(child, path + clause, clause, index) }
                    }
                }
                is TypeSwitchStatement -> {
                    statement.init?.let { visit(it, path, ownerBlock, statementIndex) }
                    statement.clauses.forEach { clause ->
                        clause.statements.forEachIndexed { index, child -> visit(child, path + clause, clause, index) }
                    }
                }
                is SelectStatement -> statement.cases.forEach { clause ->
                    clause.communication?.let { visit(it, path + clause, clause, -1) }
                    clause.statements.forEachIndexed { index, child -> visit(child, path + clause, clause, index) }
                }
                else -> Unit
            }
        }
        body.statements.forEachIndexed { index, statement -> visit(statement, listOf(body), body, index) }
        return labels
    }

    private fun isPrefix(prefix: List<Any>, path: List<Any>): Boolean =
        prefix.size <= path.size && prefix.indices.all { prefix[it] === path[it] }

    private fun <T> withStatementIndex(owner: Any, index: Int, action: () -> T): T {
        val previous = blockStatementIndices
        val current = IdentityHashMap<Any, Int>().apply {
            putAll(previous)
            put(owner, index)
        }
        blockStatementIndices = current
        return try { action() } finally { blockStatementIndices = previous }
    }

    private fun introducesVariable(statement: Statement): Boolean = when (statement) {
        is LabeledStatement -> introducesVariable(statement.statement)
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
                        else requireDefaultValues(values, declaration.values, "initializer", scope)
                        declaration.names.forEachIndexed { i, name ->
                            if (name != "_") {
                                if (scope.containsLocal(name)) error("$name redeclared in this block")
                                scope.define(name, declaredType ?: defaultType(values.getOrNull(i) ?: intType), trackUsage = true)
                            }
                        }
                    }
                    is ConstantDeclaration -> {
                        requireUniqueNames(declaration.names, "constant declaration")
                        val declaredType = declaration.type?.let { resolveLocalType(it, scope) }
                        val constants = scope.child().also { initializerScope ->
                            if (!initializerScope.hasBinding("iota") && "iota" !in packageLevelNames &&
                                "iota" !in packagePaths) {
                                initializerScope.define(
                                    "iota", untypedInt, BigInteger.valueOf(declaration.iotaIndex.toLong()), isConstant = true
                                )
                            }
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
                        val complexValues = if (values.size == declaration.values.size)
                            declaration.values.map { constantComplex(it, constants) } else emptyList()
                        declaration.names.forEachIndexed { i, name -> if (name != "_") {
                            if (scope.containsLocal(name)) error("$name redeclared in this block")
                            scope.define(
                                name, declaredType ?: values.getOrNull(i) ?: untypedInt,
                                integerConstants.getOrNull(i), stringLengths.getOrNull(i), isConstant = true,
                                rationalConstant = rationalConstants.getOrNull(i), stringIdentity = stringIdentities.getOrNull(i),
                                booleanConstant = booleanValues.getOrNull(i), complexConstant = complexValues.getOrNull(i)
                            )
                        } }
                    }
                    is TypeDeclaration -> {
                        if (declaration.name != "_" && scope.containsLocal(declaration.name))
                            error("${declaration.name} redeclared in this block")
                        val identity = "<local:${nextLocalTypeIdentity.incrementAndGet()}:${declaration.name}>"
                        if (declaration.name != "_") scope.defineType(declaration.name, identity)
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
                else requireDefaultValues(values, statement.values, "initializer", scope)
                statement.names.forEachIndexed { i, name ->
                    if (name != "_") {
                        if (scope.containsLocal(name)) error("$name redeclared in this block")
                        scope.define(name, declaredType ?: defaultType(values.getOrNull(i) ?: intType), trackUsage = true)
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
                    val ownerStatements = when (owner) {
                        is BlockStatement -> owner.statements
                        is SelectCase -> owner.statements
                        is SwitchClause -> owner.statements
                        is TypeSwitchClause -> owner.statements
                        else -> emptyList()
                    }
                    if (owner != null && sourceIndex != null && targetIndex != null && targetIndex > sourceIndex &&
                        ownerStatements.subList(sourceIndex + 1, targetIndex).any(::introducesVariable)) {
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
                if (name == "_") {
                    if (valueTypes[i] == nilType) error("use of untyped nil in short variable declaration")
                    return@forEachIndexed
                }
                if (scope.containsLocalType(name)) error("$name redeclared in this block")
                if (scope.containsLocal(name)) {
                    if (scope.isConstant(name)) error("cannot assign to constant $name")
                    requireAssignable(valueTypes[i], scope.get(name), "assignment", statement.values.getOrNull(i), scope)
                }
                else {
                    if (valueTypes[i] == nilType) error("use of untyped nil in short variable declaration")
                    val targetType = defaultType(valueTypes[i])
                    statement.values.getOrNull(i)?.let { requireIntegerConstantRepresentable(it, targetType, scope) }
                    scope.define(name, targetType, trackUsage = true)
                    added++
                }
            }
            if (added == 0) error("short declaration must introduce a new variable")
            return
        }
        statement.targets.forEach { requireAssignmentTarget(it, scope, allowBlank = statement.operator == TokenKind.ASSIGN) }
        val leftTypes = statement.targets.map { target ->
            if (isBlankIdentifier(target)) null
            else if (statement.operator == TokenKind.ASSIGN) assignmentTargetType(target, scope)
            else expressionType(target, scope)
        }
        val rightTypes = expressionTypes(statement.values, leftTypes.size, scope)
        if (leftTypes.size != rightTypes.size) error("assignment count mismatch")
        if (statement.operator == TokenKind.ASSIGN) {
            leftTypes.zip(rightTypes).forEachIndexed { i, (left, right) ->
                val value = statement.values.getOrNull(i)
                if (left != null) requireAssignable(right, left, "assignment", value, scope)
                else if (value != null && statement.values.size == rightTypes.size)
                    requireDefaultValues(listOf(right), listOf(value), "assignment", scope)
            }
        } else {
            if (leftTypes.size != 1 || rightTypes.size != 1) error("compound assignment requires one operand")
            checkBinaryType(leftTypes.single() ?: error("invalid compound assignment target"), compoundOperator(statement.operator), rightTypes.single(), statement.targets.single(), statement.values.single(), scope)
        }
    }

    private fun checkRange(range: RangeClause, body: BlockStatement, scope: Scope) {
        val targets = if (range.targets.size == 2 && isBlankIdentifier(range.targets[1]))
            range.targets.take(1) else range.targets
        if (range.targets.isNotEmpty() && range.operator == null)
            error("range variables require = or :=")
        val source = underlying(expressionType(range.expression, scope))
        val keyAndValue = when (source) {
            is ArrayGoType -> predeclaredIntType to source.element
            is PointerGoType -> when (val pointed = underlying(source.element)) {
                is ArrayGoType -> predeclaredIntType to pointed.element
                else -> error("cannot range over this pointer type")
            }
            is SliceGoType -> predeclaredIntType to source.element
            is MapGoType -> source.key to source.value
            is ChannelGoType -> {
                if (source.direction == ChannelDirection.SEND_ONLY) error("cannot range over send-only channel")
                null to source.element
            }
            else -> if (isString(source)) predeclaredIntType to predeclaredInt32Type
                else error("cannot range over this type")
        }
        if (source is ChannelGoType && targets.size > 1) error("range over channel permits one iteration variable")
        val types = listOfNotNull(keyAndValue.first, keyAndValue.second).take(targets.size)
        if (types.size != targets.size) error("too many range variables")
        if (range.operator == TokenKind.DEFINE) {
            val names = targets.map { (it as? NameExpression)?.name ?: error("range declaration requires identifiers") }
            requireUniqueNames(names, "range declaration")
            if (names.none { it != "_" }) error("range declaration must introduce a variable")
            targets.forEachIndexed { i, target ->
                val name = (target as? NameExpression)?.name ?: error("range declaration requires identifiers")
                if (name != "_") scope.define(name, defaultType(types[i]), trackUsage = true)
            }
        } else if (range.operator == TokenKind.ASSIGN) {
            targets.zip(types).forEach { (target, type) ->
                requireAssignmentTarget(target, scope)
                if (!isBlankIdentifier(target))
                    requireAssignable(type, assignmentTargetType(target, scope), "range assignment")
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
                            if (name != "_") caseScope.define(name, if (i == 0) defaultType(channel.element) else predeclaredBoolType,
                                trackUsage = true)
                        }
                    } else {
                        communication.targets.forEach { requireAssignmentTarget(it, caseScope) }
                        val targets = communication.targets.map { target ->
                            if (isBlankIdentifier(target)) null else assignmentTargetType(target, caseScope)
                        }
                        if (targets.size !in 1..2) error("invalid receive assignment")
                        targets.first()?.let { requireAssignable(channel.element, it, "receive assignment") }
                        if (targets.size == 2) targets[1]?.let { requireAssignable(predeclaredBoolType, it, "receive status") }
                    }
                }
                else -> error("invalid select communication")
            }
            inLabelBlock(clause) {
                withLocalTypeScope {
                    clause.statements.forEachIndexed { index, child ->
                        withStatementIndex(clause, index) { checkStatement(child, caseScope) }
                    }
                }
            }
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
            ?.let { if (isUntyped(it)) defaultType(it) else it }
        if (tagType == nilType) error("switch expression cannot be nil")
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
                if (caseType != nilType && !isComparable(caseType)) error("switch case expression must be comparable")
                if (tagType != null) {
                    if (!comparisonCompatible(caseType, tagType, case, statement.tag, caseScope) &&
                        !constantIntegerAssignable(caseType, tagType, case, caseScope))
                        error("case type does not match switch expression")
                    requireIntegerConstantRepresentable(case, tagType, caseScope)
                } else requireBoolean(caseType, "expressionless switch case")
                val identity = constantCaseIdentity(case, caseType, tagType, caseScope)
                if (identity != null && !seenCases.add(identity)) error("duplicate case $case in switch")
            }
            inLabelBlock(clause) {
                withLocalTypeScope {
                    clause.statements.forEachIndexed { index, child ->
                        withStatementIndex(clause, index) { checkStatement(child, caseScope) }
                    }
                }
            }
        }
    }

    private fun constantCaseIdentity(
        expression: Expression,
        caseType: GoTypeSyntax,
        switchType: GoTypeSyntax?,
        scope: Scope
    ): String? {
        val identityType = when {
            !isUntyped(caseType) -> caseType
            switchType != null && underlying(switchType) is InterfaceGoType -> defaultType(caseType)
            else -> switchType ?: defaultType(caseType)
        }
        val typeKey = constantIdentityTypeKey(identityType)
        constantConvertedNumericIdentity(expression, identityType, scope)?.let { value ->
            return "$typeKey:$value"
        }
        if (isComplex(identityType)) {
            constantComplex(expression, scope)?.let { value ->
                return "$typeKey:complex:${value.real.numerator}/${value.real.denominator},${value.imaginary.numerator}/${value.imaginary.denominator}"
            }
        }
        constantInteger(expression, scope)?.let { value -> return "$typeKey:number:$value/1" }
        constantRational(expression, scope)?.let { value ->
            return "$typeKey:number:${value.numerator}/${value.denominator}"
        }
        constantStringIdentity(expression, scope)?.let { value -> return "$typeKey:string:$value" }
        return constantBoolean(expression, scope)?.let { "$typeKey:boolean:$it" }
    }

    private fun constantMapKeyIdentity(
        expression: Expression,
        keyType: GoTypeSyntax,
        scope: Scope
    ): String? {
        val sourceType = expressionType(expression, scope)
        val identityType = if (underlying(keyType) is InterfaceGoType) defaultType(sourceType) else keyType
        val typeKey = constantIdentityTypeKey(identityType)
        constantConvertedNumericIdentity(expression, identityType, scope)?.let { value ->
            return "$typeKey:$value"
        }
        if (isComplex(identityType)) {
            constantComplex(expression, scope)?.let { value ->
                return "$typeKey:complex:${value.real.numerator}/${value.real.denominator},${value.imaginary.numerator}/${value.imaginary.denominator}"
            }
        }
        constantInteger(expression, scope)?.let { value -> return "$typeKey:number:$value/1" }
        constantRational(expression, scope)?.let { value ->
            return "$typeKey:number:${value.numerator}/${value.denominator}"
        }
        constantStringIdentity(expression, scope)?.let { value -> return "$typeKey:string:$value" }
        return constantBoolean(expression, scope)?.let { "$typeKey:boolean:$it" }
    }

    private fun constantConvertedNumericIdentity(
        expression: Expression,
        type: GoTypeSyntax,
        scope: Scope
    ): String? {
        val name = (underlying(type) as? NamedGoType)?.name ?: return null
        if (name in floatNames) {
            val value = constantRational(expression, scope) ?: constantInteger(expression, scope)?.let(GoRational::of)
                ?: constantComplex(expression, scope)?.takeIf { it.imaginary == GoRational.ZERO }?.real
                ?: return null
            return constantConvertedRationalIdentity(value, type)
        }
        if (name in complexNames) {
            val value = constantComplex(expression, scope) ?: return null
            val componentType = if (name.endsWith("complex64")) predeclaredFloat32Type else predeclaredFloat64Type
            val real = constantConvertedRationalIdentity(value.real, componentType) ?: return null
            val imaginary = constantConvertedRationalIdentity(value.imaginary, componentType) ?: return null
            return "complex:$real,$imaginary"
        }
        return null
    }

    private fun constantConvertedRationalIdentity(value: GoRational, type: GoTypeSyntax): String? {
        val name = (underlying(type) as? NamedGoType)?.name ?: return null
        return if (name.endsWith("float32")) {
            val converted = value.toFloat()
            val bits = if (converted == 0f) 0 else converted.toBits()
            "float:${bits.toUInt().toString(16)}"
        } else if (name.endsWith("float64")) {
            val converted = value.toDouble()
            val bits = if (converted == 0.0) 0L else converted.toBits()
            "float:${bits.toULong().toString(16)}"
        } else null
    }

    private fun constantIdentityTypeKey(type: GoTypeSyntax): String = canonicalPredeclaredAlias(type).toString()

    private fun constantComplex(expression: Expression, scope: Scope = globals): ConstantComplexValue? = when (expression) {
        is NameExpression -> scope.constantComplex(expression.name)
            ?: if (scope.getOrNull(expression.name) == null) dotImportedConstant(expression.name)?.second?.complex else null
        is SelectorExpression -> {
            val alias = (expression.receiver as? NameExpression)?.name
            alias?.let(packagePaths::get)?.let { importedConstant(it, expression.field)?.complex }
        }
        is LiteralExpression -> if (expression.token.kind == TokenKind.IMAG) {
            runCatching { GoRational.decimal(expression.token.lexeme.removeSuffix("i")) }.getOrNull()
                ?.let { ConstantComplexValue(GoRational.ZERO, it) }
        } else constantRealValue(expression, scope)?.let { ConstantComplexValue(it, GoRational.ZERO) }
        is ParenthesizedExpression -> constantComplex(expression.expression, scope)
        is UnaryExpression -> constantComplex(expression.operand, scope)?.let { value ->
            when (expression.operator) {
                TokenKind.ADD -> value
                TokenKind.SUB -> ConstantComplexValue(value.real.negate(), value.imaginary.negate())
                else -> null
            }
        }
        is BinaryExpression -> {
            val left = constantComplex(expression.left, scope)
            val right = constantComplex(expression.right, scope)
            if (left == null || right == null) constantInteger(expression, scope)?.let {
                ConstantComplexValue(GoRational.of(it), GoRational.ZERO)
            } else when (expression.operator) {
                TokenKind.ADD -> ConstantComplexValue(left.real + right.real, left.imaginary + right.imaginary)
                TokenKind.SUB -> ConstantComplexValue(left.real - right.real, left.imaginary - right.imaginary)
                TokenKind.MUL -> ConstantComplexValue(
                    left.real * right.real - left.imaginary * right.imaginary,
                    left.real * right.imaginary + left.imaginary * right.real
                )
                TokenKind.QUO -> {
                    val denominator = right.real * right.real + right.imaginary * right.imaginary
                    if (denominator.numerator.signum() == 0) error("division by zero in constant expression")
                    ConstantComplexValue(
                        (left.real * right.real + left.imaginary * right.imaginary) / denominator,
                        (left.imaginary * right.real - left.real * right.imaginary) / denominator
                    )
                }
                else -> null
            }
        }
        is CallExpression -> {
            val target = constantConversionTarget(expression, scope)
            when {
                expression.function == NameExpression("complex") && expression.arguments.size == 2 -> {
                    val real = constantRealValue(expression.arguments[0], scope)
                    val imaginary = constantRealValue(expression.arguments[1], scope)
                    if (real == null || imaginary == null) null else ConstantComplexValue(real, imaginary)
                }
                expression.function == NameExpression("real") && expression.arguments.size == 1 ->
                    constantComplex(expression.arguments.single(), scope)?.let { ConstantComplexValue(it.real, GoRational.ZERO) }
                expression.function == NameExpression("imag") && expression.arguments.size == 1 ->
                    constantComplex(expression.arguments.single(), scope)?.let { ConstantComplexValue(it.imaginary, GoRational.ZERO) }
                target != null && isComplex(target) && expression.arguments.size == 1 && !expression.expandLastArgument ->
                    constantComplex(expression.arguments.single(), scope)
                else -> null
            }
        }
        else -> null
    }

    private fun constantRealValue(expression: Expression, scope: Scope): GoRational? =
        constantRational(expression, scope) ?: constantInteger(expression, scope)?.let(GoRational::of)
            ?: if (expressionType(expression, scope) == untypedComplex) {
                constantComplex(expression, scope)?.let { value ->
                    if (value.imaginary.numerator.signum() == 0) value.real else null
                }
            } else null

    private fun constantBoolean(expression: Expression, scope: Scope = globals): Boolean? = when (expression) {
        is NameExpression -> if (scope.getOrNull(expression.name) != null) scope.constantBoolean(expression.name)
            else when (expression.name) {
                "true" -> true
                "false" -> false
                else -> dotImportedConstant(expression.name)?.second?.boolean
            }
        is SelectorExpression -> (expression.receiver as? NameExpression)?.name?.let(packagePaths::get)
            ?.let { importedConstant(it, expression.field)?.boolean }
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
            val target = constantConversionTarget(expression, scope)
            if (target != null && underlying(target) == boolType && expression.arguments.size == 1 && !expression.expandLastArgument)
                constantBoolean(expression.arguments.single(), scope) else null
        }
        else -> null
    }

    private fun constantStringIdentity(expression: Expression, scope: Scope = globals): String? = when (expression) {
        is NameExpression -> scope.constantStringIdentity(expression.name)
            ?: if (scope.getOrNull(expression.name) == null) dotImportedConstant(expression.name)?.second?.stringIdentity else null
        is SelectorExpression -> (expression.receiver as? NameExpression)?.name?.let(packagePaths::get)
            ?.let { importedConstant(it, expression.field)?.stringIdentity }
        is LiteralExpression -> if (expression.token.kind == TokenKind.STRING)
            canonicalGoStringLiteral(expression.token.lexeme) else null
        is ParenthesizedExpression -> constantStringIdentity(expression.expression, scope)
        is BinaryExpression -> if (expression.operator == TokenKind.ADD) {
            val left = constantStringIdentity(expression.left, scope)
            val right = constantStringIdentity(expression.right, scope)
            if (left != null && right != null) left + right else null
        } else null
        is CallExpression -> {
            val target = constantConversionTarget(expression, scope)
            if (target == null || !isString(target) || expression.arguments.size != 1 || expression.expandLastArgument) null
            else constantStringIdentity(expression.arguments.single(), scope) ?: constantInteger(expression.arguments.single(), scope)?.let { value ->
                val codePoint = runCatching { value.intValueExact() }.getOrNull()
                val bytes = encodeGoCodePoint(codePoint ?: -1)
                bytes.joinToString("") { byte ->
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
        val interfaceType = expressionType(statement.guard.expression, switchScope)
        if (underlying(interfaceType) !is InterfaceGoType) error("type switch requires an interface operand")
        var sawDefault = false
        var sawNil = false
        val seenTypes = mutableListOf<GoTypeSyntax>()
        val guardUsage = statement.guard.name?.takeIf { it != "_" }?.let(switchScope::newUsageGroup)
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
                caseScope.define(statement.guard.name, singleType ?: interfaceType, usageGroup = guardUsage)
            inLabelBlock(clause) {
                withLocalTypeScope {
                    clause.statements.forEachIndexed { index, child ->
                        withStatementIndex(clause, index) { checkStatement(child, caseScope) }
                    }
                }
            }
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
                return if (arity == 2) listOf(channel.element, predeclaredBoolType) else listOf(channel.element)
            }
            if (expression is TypeAssertionExpression) {
                val asserted = expressionType(expression, scope)
                return if (arity == 2) listOf(asserted, predeclaredBoolType) else listOf(asserted)
            }
            if (expression is IndexExpression && arity == 2) {
                val map = underlying(expressionType(expression.receiver, scope)) as? MapGoType
                if (map != null) return listOf(map.value, predeclaredBoolType)
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

    private fun expressionType(
        expression: Expression, scope: Scope, expectedType: GoTypeSyntax? = null
    ): GoTypeSyntax {
        val result = expressionTypeUnchecked(expression, scope, expectedType)
        if (!isUntyped(result) && isConstantExpression(expression, scope) &&
            (isInteger(result) || isFloatArgument(result) || isComplex(result))) {
            // Typed constant operations must remain representable in their result type.
            requireIntegerConstantRepresentable(expression, result, scope)
        }
        return result
    }

    private fun expressionTypeUnchecked(
        expression: Expression, scope: Scope, expectedType: GoTypeSyntax?
    ): GoTypeSyntax = when (expression) {
        is NameExpression -> scope.getOrNull(expression.name)?.also { scope.markUsed(expression.name) } ?: when {
            scope.typeBinding(expression.name) != null || typeDeclarations.containsKey(expression.name) ||
                dotImportedType(expression.name) != null || isBuiltinType(expression.name) ->
                error("type ${expression.name} is not an expression")
            expression.name in packagePaths -> error("package ${expression.name} cannot be used as a value")
            expression.name == "true" || expression.name == "false" -> untypedBool
            expression.name == "nil" -> nilType
            expression.name == "iota" -> error("undefined: iota")
            functions.containsKey(expression.name) -> functionType(functions.getValue(expression.name))
            else -> dotImportedIdentifierType(expression.name)?.also { usedDotImportPaths += it.first }?.second
                ?: error("undefined: ${expression.name}")
        }
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> untypedInt
            TokenKind.CHAR -> {
                if (decodeCharacterConstant(expression.token.lexeme) == null) error("invalid character literal")
                untypedRune
            }
            TokenKind.FLOAT -> untypedFloat
            TokenKind.IMAG -> untypedComplex
            TokenKind.STRING -> untypedString
            else -> error("invalid literal")
        }
        is ParenthesizedExpression -> expressionType(expression.expression, scope, expectedType)
        is FunctionLiteralExpression -> {
            val parameters = expression.parameters.map { it.copy(type = resolveLocalType(it.type, scope)) }
            val results = expression.results.map { resolveLocalType(it, scope) }
            val literalScope = scope.child(trackLocalUsage = true)
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
                literalScope.unusedLocalVariable()?.let { error("$it declared and not used") }
                if (results.isNotEmpty() && !endsWithGo10Exit(expression.body))
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
            val operandContext = expectedType?.takeIf {
                expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.XOR) &&
                    containsNonConstantUntypedShift(expression.operand, scope)
            }
            val operand = expressionType(expression.operand, scope, operandContext)
            when (expression.operator) {
                TokenKind.ADD, TokenKind.SUB -> { if (!isNumeric(operand)) error("unary operator requires numeric operand"); operand }
                TokenKind.NOT -> { requireBoolean(operand, "!"); operand }
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
        is BinaryExpression -> {
            val left = expressionType(expression.left, scope)
            val right = expressionType(expression.right, scope)
            if (expression.operator in setOf(TokenKind.SHL, TokenKind.SHR)) {
                val shiftContext = if (nonConstantUntypedShift(expression, scope) != null && expectedType != null) {
                    if (underlying(expectedType) is InterfaceGoType)
                        defaultUntypedShiftType(expressionType(expression.left, scope))
                    else expectedType
                } else null
                val contextualLeft = if (shiftContext == null) left else {
                    if (!isInteger(shiftContext)) error("left operand of shift must be integer in this context")
                    requireIntegerConstantRepresentable(expression.left, shiftContext, scope)
                    shiftContext
                }
                checkBinaryType(contextualLeft, expression.operator, right, expression.left, expression.right, scope)
            } else {
                val leftHasShift = containsNonConstantUntypedShift(expression.left, scope)
                val rightHasShift = containsNonConstantUntypedShift(expression.right, scope)
                val leftContext = when {
                    !leftHasShift -> null
                    !rightHasShift && !isUntyped(right) -> right
                    expectedType != null -> expectedType
                    else -> null
                }
                val rightContext = when {
                    !rightHasShift -> null
                    !leftHasShift && !isUntyped(left) -> left
                    expectedType != null -> expectedType
                    else -> null
                }
                checkBinaryType(
                    if (leftContext == null) left else expressionType(expression.left, scope, leftContext),
                    expression.operator,
                    if (rightContext == null) right else expressionType(expression.right, scope, rightContext),
                    expression.left, expression.right, scope
                )
            }
        }
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
                requireIntegerValue(boundType, bound, "slice index", scope)
                requireValidConstantIndex(bound, null, "slice", scope)
            }
            val receiverType = expressionType(expression.receiver, scope)
            val receiver = underlying(receiverType)
            val constantLength = when (receiver) {
                is ArrayGoType -> receiver.length?.let { constantInteger(it, scope) }
                is PointerGoType -> (underlying(receiver.element) as? ArrayGoType)?.length?.let { constantInteger(it, scope) }
                else -> if (isString(receiver)) constantStringLength(expression.receiver, scope) else null
            }
            val low = expression.low?.let { constantInteger(it, scope) } ?:
                if (expression.low == null) BigInteger.ZERO else null
            val high = expression.high?.let { constantInteger(it, scope) } ?:
                if (expression.high == null) constantLength else null
            if (low != null && high != null && low > high) error("slice index low exceeds high")
            if (constantLength != null) {
                listOfNotNull(expression.low, expression.high).forEach { bound ->
                    constantInteger(bound, scope)?.let { value ->
                        if (value > constantLength) error("slice index $value is out of bounds")
                    }
                }
            }
            when (receiver) {
                is SliceGoType -> receiver
                is ArrayGoType -> {
                    if (!isAddressable(expression.receiver, scope)) error("cannot slice unaddressable array")
                    SliceGoType(receiver.element)
                }
                is PointerGoType -> when (val pointed = underlying(receiver.element)) {
                    is ArrayGoType -> SliceGoType(pointed.element)
                    else -> error("cannot slice through this pointer")
                }
                else -> if (isString(receiver)) receiverType else error("cannot slice $receiver")
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
        val receiverExpressionType = expressionType(expression.receiver, scope)
        val receiver = underlying(receiverExpressionType)
        val index = expressionType(expression.index, scope)
        return when (receiver) {
            is ArrayGoType -> {
                requireIntegerValue(index, expression.index, "array index", scope)
                requireValidConstantIndex(expression.index, receiver.length?.let { constantInteger(it, scope) }, "array", scope)
                receiver.element
            }
            is PointerGoType -> when (val pointed = underlying(receiver.element)) {
                is ArrayGoType -> {
                    requireIntegerValue(index, expression.index, "array index", scope)
                    requireValidConstantIndex(expression.index, pointed.length?.let { constantInteger(it, scope) }, "array", scope)
                    pointed.element
                }
                else -> error("cannot index through this pointer")
            }
            is SliceGoType -> {
                requireIntegerValue(index, expression.index, "slice index", scope)
                requireValidConstantIndex(expression.index, null, "slice", scope)
                receiver.element
            }
            is MapGoType -> { requireAssignable(index, receiver.key, "map index", expression.index, scope); receiver.value }
            else -> if (isString(receiver)) {
                requireIntegerValue(index, expression.index, "string index", scope)
                requireValidConstantIndex(expression.index, constantStringLength(expression.receiver, scope), "string", scope)
                byteType
            } else error("cannot index this value")
        }
    }

    private fun requireIntegerValue(type: GoTypeSyntax, expression: Expression, context: String, scope: Scope) {
        if (!isInteger(type) && !constantIntegerAssignable(type, predeclaredIntType, expression, scope))
            error("$context must be integer")
    }

    private fun requireValidConstantIndex(
        expression: Expression,
        length: BigInteger?,
        context: String,
        scope: Scope
    ) {
        requireIntegerConstantRepresentable(expression, predeclaredIntType, scope)
        val index = constantInteger(expression, scope) ?: return
        if (index.signum() < 0) error("$context index must be non-negative")
        if (length != null && index >= length) error("$context index $index is out of bounds")
    }

    private fun selectorType(expression: SelectorExpression, scope: Scope): GoTypeSyntax {
        if (expression.field == "_") error("cannot refer to blank struct field")
        if (expression.receiver is NameExpression && expression.receiver.name in packagePaths &&
            scope.getOrNull(expression.receiver.name) == null &&
            scope.typeBinding(expression.receiver.name) == null) {
            val path = importedPackagePath(expression.receiver.name)!!
            return when (standardPackageName(path)) {
                "fmt" -> GoFmtPackage.functionType(expression.field) ?: error("undefined fmt identifier ${expression.field}")
                "math" -> GoMathPackage.memberType(expression.field) ?: error("undefined math identifier ${expression.field}")
                "unsafe" -> {
                    if (expression.field in GoUnsafePackage.exportedTypes)
                        error("type unsafe.${expression.field} is not an expression")
                    GoUnsafePackage.memberType(expression.field) ?: error("undefined unsafe identifier ${expression.field}")
                }
                "runtime" -> if (expression.field in GoRuntimePackage.exportedTypes)
                    error("type runtime.${expression.field} is not an expression")
                else error("undefined runtime identifier ${expression.field}")
                else -> importedPackages[path]?.let { imported ->
                    imported.exportedFunctionType(expression.field, path) ?: imported.exportedConstant(expression.field, path)?.type
                        ?: imported.exportedVariableType(expression.field, path)
                }
                    ?: error("undefined imported identifier ${expression.field}")
            }
        }
        methodExpressionReceiver(expression.receiver, scope)?.let { receiverType ->
            val method = methodSet(receiverType)[expression.field] ?: error("undefined method ${expression.field} on $receiverType")
            methodExpressionDeclaration(receiverType, expression.field)?.let(::recordMethodDependency)
            return FunctionGoType(listOf(ParameterSyntax(null, receiverType)) + method.parameters, method.results)
        }
        val receiverType = expressionType(expression.receiver, scope)
        val receiverUnderlying = underlying(receiverType)
        if (receiverUnderlying is PointerGoType && underlying(receiverUnderlying.element) is InterfaceGoType)
            error("cannot select a member from a pointer to an interface")
        data class Candidate(
            val type: GoTypeSyntax,
            val needsAddressableReceiver: Boolean = false
        )
        data class SearchNode(val type: GoTypeSyntax, val pointer: Boolean, val ancestors: Set<String>)
        var level = listOf(SearchNode(receiverType, receiverType is PointerGoType, emptySet()))
        while (level.isNotEmpty()) {
            val candidates = mutableListOf<Candidate>()
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                when (val actual = selectorBaseType(node.type)) {
                    is InterfaceGoType -> interfaceMethods(actual)[packageMethodKey(expression.field)]?.let {
                        candidates += Candidate(it)
                    }
                    is StructGoType -> {
                        actual.fields.forEach { field ->
                            val fieldNames = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                            val externalNamedType = (node.type as? PointerGoType)?.element as? QualifiedGoType
                                ?: node.type as? QualifiedGoType
                            val fieldIsVisible = externalNamedType == null || isExportedIdentifier(expression.field)
                            if (fieldIsVisible && expression.field in fieldNames) candidates += Candidate(field.type)
                        }
                        val method = methodType(node.type, expression.field)
                        if (method != null) {
                            method.declaration?.let(::recordMethodDependency)
                            candidates += Candidate(
                                method.signature,
                                method.pointerReceiver && !node.pointer && !isAddressable(expression.receiver, scope)
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
                    else -> methodBaseName(node.type)?.let { named ->
                        methods["$named.${expression.field}"]?.let { method ->
                            recordMethodDependency(method)
                            val pointerReceiver = method.receiver?.type is PointerGoType
                            candidates += Candidate(
                                functionType(method), pointerReceiver && !node.pointer &&
                                    !isAddressable(expression.receiver, scope)
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
                return candidate.type
            }
            level = next
        }
        error("undefined field or method ${expression.field}")
    }

    private fun methodExpressionReceiver(expression: Expression, scope: Scope): GoTypeSyntax? = when (expression) {
        is NameExpression, is SelectorExpression -> methodExpressionBaseType(expression, scope)
        is ParenthesizedExpression -> {
            val pointer = expression.expression as? UnaryExpression
            if (pointer?.operator == TokenKind.MUL)
                methodExpressionBaseType(pointer.operand, scope)?.let(::PointerGoType)
            else null
        }
        else -> null
    }

    private fun methodExpressionBaseType(expression: Expression, scope: Scope): GoTypeSyntax? = when (expression) {
        is NameExpression -> if (scope.getOrNull(expression.name) != null || !isTypeName(expression.name, scope)) null else {
            resolveLocalType(scope.typeBinding(expression.name)?.let(::NamedGoType) ?: NamedGoType(expression.name), scope)
        }
        is SelectorExpression -> importedPackageType(expression, scope)
        else -> null
    }

    private fun isAddressable(expression: Expression, scope: Scope): Boolean = when (expression) {
        is NameExpression -> scope.isVariable(expression.name) || dotImportedVariable(expression.name) != null
        is ParenthesizedExpression -> isAddressable(expression.expression, scope)
        is CompositeLiteral -> true
        is UnaryExpression -> expression.operator == TokenKind.MUL &&
            underlying(expressionType(expression.operand, scope)) is PointerGoType
        is IndexExpression -> when (val receiver = underlying(expressionType(expression.receiver, scope))) {
            is SliceGoType -> true
            is ArrayGoType -> isAddressable(expression.receiver, scope)
            is PointerGoType -> underlying(receiver.element) is ArrayGoType
            else -> false
        }
        is SelectorExpression -> importedPackageVariable(expression) != null || selectorFieldAddressable(expression, scope)
        else -> false
    }

    private fun dotImportedVariable(name: String): Pair<String, GoTypeSyntax>? = dotImportPaths.firstNotNullOfOrNull { path ->
        importedPackages[path]?.exportedVariableType(name, path)?.let { path to it }
    }

    private fun importedPackageVariable(expression: SelectorExpression): Pair<String, GoTypeSyntax>? {
        val alias = (expression.receiver as? NameExpression)?.name ?: return null
        val path = packagePaths[alias] ?: return null
        if (standardPackageName(path) in setOf("fmt", "math", "unsafe")) return null
        return importedPackages[path]?.exportedVariableType(expression.field, path)?.let { path to it }
    }

    private fun methodType(type: GoTypeSyntax, name: String): TypeMethod? {
        val base = (type as? PointerGoType)?.element ?: type
        if (base is QualifiedGoType) {
            if (!isExportedIdentifier(name)) return null
            val imported = importedPackages[base.packageName] ?: return null
            val function = imported.methods["${base.name}.$name"] ?: return null
            return TypeMethod(externalizeType(imported.functionType(function), base.packageName) as FunctionGoType,
                function.receiver?.type is PointerGoType, function)
        }
        val key = "${namedType(type) ?: return null}.$name"
        val function = methods[key] ?: return null
        return TypeMethod(functionType(function), function.receiver?.type is PointerGoType, function)
    }

    private fun methodExpressionDeclaration(type: GoTypeSyntax, name: String): FunctionDeclaration? {
        if (type is PointerGoType && underlying(type.element) is InterfaceGoType) return null
        val actual = underlying(type)
        if (actual is InterfaceGoType) return null
        val target = packageMethodKey(name)
        data class SearchNode(val type: GoTypeSyntax, val pointer: Boolean, val ancestors: Set<String>)
        var level = listOf(SearchNode(type, type is PointerGoType, emptySet()))
        while (level.isNotEmpty()) {
            val declarations = mutableListOf<FunctionDeclaration>()
            var candidates = 0
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                val named = (node.type as? PointerGoType)?.element as? QualifiedGoType
                    ?: node.type as? QualifiedGoType
                if (named != null) {
                    val imported = importedPackages[named.packageName]
                    val foreignType = if (node.pointer) PointerGoType(NamedGoType(named.name)) else NamedGoType(named.name)
                    imported?.methodSet(foreignType)?.forEach { (methodName, _) ->
                        if (methodName == target) candidates++
                    }
                }
                when (val nodeType = selectorBaseType(node.type)) {
                    is InterfaceGoType -> if (target in interfaceMethods(nodeType)) candidates++
                    is StructGoType -> {
                        val baseName = methodBaseName(node.type)
                        if (baseName != null) methods.values.forEach { method ->
                            val receiverType = method.receiver?.type ?: return@forEach
                            if (method.name != name || methodBaseName(receiverType) != baseName ||
                                receiverType is PointerGoType && !node.pointer) return@forEach
                            declarations += method
                            candidates++
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
                        val baseName = methodBaseName(node.type)
                        if (baseName != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            if (method.name != name || methodBaseName(receiverType) != baseName ||
                                receiverType is PointerGoType && !node.pointer) return@methodLoop
                            declarations += method
                            candidates++
                        }
                    }
                }
            }
            if (candidates > 0) {
                return if (candidates == 1) declarations.singleOrNull() else null
            }
            level = next
        }
        return null
    }

    private fun recordMethodDependency(function: FunctionDeclaration) {
        if (methods.values.none { it === function }) return
        dependencyFunction?.let { owner ->
            calledMethodsByFunction.getOrPut(owner) { Collections.newSetFromMap(IdentityHashMap()) }.add(function)
        }
        dependencyExpression?.let { expression ->
            calledMethodsByExpression.getOrPut(expression) { Collections.newSetFromMap(IdentityHashMap()) }.add(function)
        }
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

    private fun assignmentTargetType(expression: Expression, scope: Scope): GoTypeSyntax = when (expression) {
        is ParenthesizedExpression -> assignmentTargetType(expression.expression, scope)
        is NameExpression -> scope.getOrNull(expression.name) ?: expressionType(expression, scope)
        else -> expressionType(expression, scope)
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
        val type = underlying(literalType)
        if (type !is ArrayGoType || type.length != null) validateType(literalType)
        checkCompositeElements(literalType, literal.elements, scope)
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
            requireIntegerConstantRepresentable(lengthExpression, predeclaredIntType, scope)
            return ArrayGoType(lengthExpression, type.element).also(::validateType)
        }
        return literalType
    }

    private fun resolveLocalType(type: GoTypeSyntax, scope: Scope): GoTypeSyntax = when (type) {
        is NamedGoType -> scope.typeBinding(type.name)?.let(::NamedGoType) ?: dotImportedType(type.name) ?: type
        is QualifiedGoType -> {
            val path = packagePaths[type.packageName]?.let { importedPackagePath(type.packageName) } ?: type.packageName
            if (standardPackageName(path) == "unsafe" && type.name == "Pointer")
                return QualifiedGoType(path, type.name)
            if (standardPackageName(path) == "runtime" && type.name in GoRuntimePackage.exportedTypes)
                return QualifiedGoType(path, type.name)
            if (importedPackages[path]?.hasExportedType(type.name) != true)
                error("undefined imported type ${type.packageName}.${type.name}")
            QualifiedGoType(path, type.name)
        }
        is PointerGoType -> PointerGoType(resolveLocalType(type.element, scope))
        is SliceGoType -> SliceGoType(resolveLocalType(type.element, scope))
        is ArrayGoType -> {
            val length = type.length?.let { expression ->
                requireIntegerValue(expressionType(expression, scope), expression, "array length", scope)
                val value = constantInteger(expression, scope) ?: error("array length must be constant")
                if (value.signum() < 0) error("array length must be non-negative")
                requireIntegerConstantRepresentable(expression, predeclaredIntType, scope)
                LiteralExpression(Token(TokenKind.INT, value.toString(), Position(0, 1, 1)))
            }
            ArrayGoType(length, resolveLocalType(type.element, scope))
        }
        is MapGoType -> MapGoType(resolveLocalType(type.key, scope), resolveLocalType(type.value, scope))
        is ChannelGoType -> ChannelGoType(resolveLocalType(type.element, scope), type.direction)
        is StructGoType -> StructGoType(type.fields.map { field ->
            field.copy(
                type = resolveLocalType(field.type, scope),
                declaringPackagePath = field.declaringPackagePath ?: packageIdentity ?: packageName,
                packagePath = field.packagePath ?: packageIdentity.takeIf { path ->
                    field.names.any(GoUnicode6::isUnexportedIdentifier) ||
                        field.names.isEmpty() && GoUnicode6.isUnexportedIdentifier(embeddedFieldName(field.type))
                }
            )
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
                    requireIntegerValue(expressionType(length, scope), length, "array length", scope)
                    val constant = constantInteger(length, scope) ?: error("array length must be constant")
                    if (constant.signum() < 0) error("array length must be non-negative")
                    requireIntegerConstantRepresentable(length, predeclaredIntType, scope)
                    constant
                }
                var nextIndex = BigInteger.ZERO
                val usedIndices = mutableSetOf<BigInteger>()
                elements.forEach { item ->
                    val index = item.key?.let { key ->
                        requireIntegerValue(expressionType(key, scope), key, "composite index", scope)
                        val constant = constantInteger(key, scope) ?: error("composite index must be constant")
                        if (constant.signum() < 0) error("composite index must be non-negative")
                        requireIntegerConstantRepresentable(key, predeclaredIntType, scope)
                        constant
                    } ?: nextIndex
                    if (!usedIndices.add(index)) error("duplicate composite index $index")
                    if (arrayLength != null && index >= arrayLength) error("composite index $index is out of bounds")
                    nextIndex = index + BigInteger.ONE
                    checkCompositeValue(item.value, element, "composite element", scope)
                }
            }
            is MapGoType -> {
                val constantKeys = mutableSetOf<String>()
                elements.forEach { item ->
                    val key = item.key ?: error("map literal element requires key")
                    checkCompositeValue(key, type.key, "map key", scope)
                    constantMapKeyIdentity(key, type.key, scope)?.let { identity ->
                        if (!constantKeys.add(identity)) error("duplicate constant map key")
                    }
                    checkCompositeValue(item.value, type.value, "map value", scope)
                }
            }
            is StructGoType -> {
                if (elements.isEmpty()) return
                data class LiteralField(val name: String, val type: GoTypeSyntax, val packagePath: String?)
                val fieldList = type.fields.flatMap { field ->
                    field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }.map { name ->
                        LiteralField(name, field.type, field.declaringPackagePath ?: unexportedFieldPackagePath(field, name))
                    }
                }.filter { it.name.isNotEmpty() }
                val fields = fieldList.associateBy { it.name }
                val keyed = elements.map { it.key != null }.toSet()
                if (keyed.size > 1) error("mixture of keyed and unkeyed struct literal elements")
                val currentPackage = packageIdentity ?: packageName
                if (keyed.singleOrNull() != true && fieldList.any { field ->
                        !isExportedIdentifier(field.name) &&
                            (literalType is QualifiedGoType || field.packagePath != currentPackage)
                    })
                    error("implicit assignment to unexported fields in struct literal")
                if (keyed.singleOrNull() == true) {
                    val usedFields = mutableSetOf<String>()
                    elements.forEach { item ->
                        val key = (item.key as? NameExpression)?.name ?: error("struct field key must be an identifier")
                        if (key == "_") error("cannot use blank field in keyed struct literal")
                        if (!usedFields.add(key)) error("duplicate field $key in struct literal")
                        val field = fields[key] ?: error("unknown field $key")
                        if (!isExportedIdentifier(key) &&
                            (literalType is QualifiedGoType || field.packagePath != currentPackage))
                            error("cannot refer to unexported field $key in struct literal")
                        checkCompositeValue(item.value, field.type, "struct field", scope, allowElided = false)
                    }
                } else {
                    if (elements.size != fieldList.size) error("struct literal has ${elements.size} values for ${fieldList.size} fields")
                    elements.forEachIndexed { i, item ->
                        checkCompositeValue(item.value, fieldList[i].type, "struct field", scope, allowElided = false)
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
                val embeddedUnderlying = underlying(embedded)
                if (embeddedUnderlying is PointerGoType)
                    error("embedded field type cannot be a pointer")
                if (field.type is PointerGoType && embeddedUnderlying is InterfaceGoType)
                    error("embedded field type cannot be a pointer to an interface")
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
        val target = call.function.unparenthesized()
        val unsafeName = unsafeIntrinsicName(target, scope)
        if (unsafeName != null) {
            if (call.arguments.size != 1 || call.expandLastArgument) error("unsafe intrinsic requires one argument")
            if (unsafeName == "Offsetof" && selectorPath(call.arguments.single()) == null)
                error("unsafe.Offsetof requires a struct field selector")
            expressionType(call.arguments.single(), scope)
            return listOf(predeclaredUintptrType)
        }
        if (target is SelectorExpression) {
            val importedType = importedPackageType(target, scope)
            if (importedType != null) {
                if (call.arguments.size != 1 || call.expandLastArgument) error("conversion requires one argument")
                validateType(importedType)
                val from = expressionType(call.arguments.single(), scope)
                if (!convertible(from, importedType, isConstantExpression(call.arguments.single(), scope)))
                    error("cannot convert $from to $importedType")
                requireIntegerConstantRepresentable(call.arguments.single(), importedType, scope)
                return listOf(importedType)
            }
        }
        val conversionType = (target as? TypeExpression)?.type
            ?: parenthesizedPointerConversionType(call.function, scope)
        if (conversionType != null) {
            if (call.arguments.size != 1 || call.expandLastArgument) error("conversion requires one argument")
            val to = resolveLocalType(conversionType, scope)
            validateType(to)
            val from = expressionType(call.arguments.single(), scope)
            if (!convertible(from, to, isConstantExpression(call.arguments.single(), scope))) error("cannot convert $from to $to")
            requireIntegerConstantRepresentable(call.arguments.single(), to, scope)
            return listOf(to)
        }
        val typeNameTarget = target.unparenthesized() as? NameExpression
        if (typeNameTarget != null && scope.getOrNull(typeNameTarget.name) == null) {
            if (isTypeName(typeNameTarget.name, scope)) {
                val localType = scope.typeBinding(typeNameTarget.name)?.let(::NamedGoType)
                if (call.arguments.size != 1 || call.expandLastArgument) error("conversion requires one argument")
                val from = expressionType(call.arguments.single(), scope)
                val to = resolveLocalType(localType ?: NamedGoType(typeNameTarget.name), scope)
                validateType(to)
                if (!convertible(from, to, isConstantExpression(call.arguments.single(), scope))) error("cannot convert $from to $to")
                requireIntegerConstantRepresentable(call.arguments.single(), to, scope)
                return listOf(to)
            }
            if (typeNameTarget.name !in packagePaths) {
                val builtin = builtinCall(typeNameTarget.name, call.arguments, scope, call.expandLastArgument)
                if (builtin != null) {
                    if (typeNameTarget.name == "panic") terminatingPanicCalls += call
                    if (typeNameTarget.name in setOf("len", "cap") && constantInteger(call, scope) != null)
                        return listOf(untypedInt)
                    return builtin
                }
            }
        }
        val targetType = if (call.function is SelectorExpression) selectorType(call.function, scope)
            else expressionType(call.function, scope)
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

    private fun parenthesizedPointerConversionType(expression: Expression, scope: Scope): GoTypeSyntax? = when (expression) {
        is ParenthesizedExpression -> when (val inner = expression.expression) {
            is UnaryExpression -> if (inner.operator == TokenKind.MUL)
                typeOperand(inner.operand, scope)?.let(::PointerGoType) else null
            else -> parenthesizedPointerConversionType(inner, scope)
        }
        else -> null
    }

    private fun typeOperand(expression: Expression, scope: Scope): GoTypeSyntax? = when (expression) {
        is NameExpression -> if (scope.getOrNull(expression.name) == null && isTypeName(expression.name, scope))
            resolveLocalType(scope.typeBinding(expression.name)?.let(::NamedGoType) ?: NamedGoType(expression.name), scope)
        else null
        is SelectorExpression -> importedPackageType(expression, scope)
        is TypeExpression -> resolveLocalType(expression.type, scope)
        is ParenthesizedExpression -> typeOperand(expression.expression, scope)
        is UnaryExpression -> if (expression.operator == TokenKind.MUL)
            typeOperand(expression.operand, scope)?.let(::PointerGoType) else null
        else -> null
    }

    private fun builtinCall(name: String, args: List<Expression>, scope: Scope, expandLastArgument: Boolean = false): List<GoTypeSyntax>? {
        if (expandLastArgument && name != "append")
            error("$name does not accept ...")
        val types = if (name == "make" || name == "new") {
            args.firstOrNull()?.let { typeArgument ->
                listOf(builtinTypeArgument(typeArgument, scope)) + args.drop(1).map {
                    expressionType(it, scope, predeclaredIntType.takeIf { name == "make" })
                }
            } ?: emptyList()
        } else callArgumentTypes(args, expandLastArgument, scope)
        if (expandLastArgument && name in setOf("print", "println") && args.size != 1)
            error("... requires a single final argument")
        return when (name) {
            "print", "println" -> emptyList()
            "panic" -> {
                if (expandLastArgument) error("panic does not accept ...")
                requireCount(name, args, 1, types.size)
                requireAssignable(types.single(), InterfaceGoType(emptyList()), "panic argument", args.single(), scope)
                emptyList()
            }
            "recover" -> {
                if (expandLastArgument) error("recover does not accept ...")
                requireCount(name, args, 0, types.size)
                listOf(InterfaceGoType(emptyList()))
            }
            "make" -> {
                if (expandLastArgument) error("make does not accept ...")
                if (types.isEmpty()) error("make requires a type argument")
                val type = types.first()
                when (underlying(type)) {
                    is SliceGoType -> {
                        if (args.size !in 2..3) error("make slice requires length and optional capacity")
                        args.drop(1).forEachIndexed { index, _ ->
                            requireMakeSize(types[index + 1], args[index + 1], scope)
                        }
                    }
                    is MapGoType -> {
                        if (args.size !in 1..2) error("make map accepts at most one size hint")
                        args.getOrNull(1)?.let { requireMakeSize(types[1], it, scope) }
                    }
                    is ChannelGoType -> {
                        if (args.size !in 1..2) error("make channel accepts at most one buffer size")
                        args.getOrNull(1)?.let { requireMakeSize(types[1], it, scope) }
                    }
                    else -> error("make requires slice, map, or channel type")
                }
                listOf(type)
            }
            "new" -> {
                if (expandLastArgument) error("new does not accept ...")
                requireCount(name, args, 1, types.size)
                listOf(PointerGoType(types[0]))
            }
            "close" -> {
                requireCount(name, args, 1, types.size)
                val channel = underlying(types[0]) as? ChannelGoType ?: error("close requires channel")
                if (channel.direction == ChannelDirection.RECEIVE_ONLY) error("cannot close receive-only channel")
                emptyList()
            }
            "len", "cap" -> {
                requireCount(name, args, 1, types.size)
                val type = underlying(types[0])
                val string = isString(types[0])
                val pointerToArray = type is PointerGoType && underlying(type.element) is ArrayGoType
                if ((name == "cap" && string) || (!string && !pointerToArray && type !is SliceGoType &&
                        type !is ArrayGoType && type !is MapGoType && type !is ChannelGoType))
                    error("$name not defined for this type")
                listOf(predeclaredIntType)
            }
            "append" -> {
                if (types.isEmpty()) error("append requires a slice")
                if (expandLastArgument && types.size != 2) error("append with ... requires one slice argument")
                val slice = underlying(types[0]) as? SliceGoType ?: error("append requires slice")
                if (expandLastArgument) {
                    types.drop(1).dropLast(1).forEachIndexed { i, type -> requireAssignable(type, slice.element, "append", args.getOrNull(i + 1), scope) }
                    if (!(isString(types.last()) && isByteElementType(slice.element)))
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
                    isString(types[1]) && assignable(types[0], SliceGoType(predeclaredUint8Type)) -> Unit
                    else -> error("copy requires slices, or a byte slice and string")
                }
                listOf(predeclaredIntType)
            }
            "delete" -> {
                requireCount(name, args, 2, types.size)
                val map = underlying(types[0]) as? MapGoType ?: error("delete requires a map")
                requireAssignable(types[1], map.key, "delete key", args.getOrNull(1), scope)
                emptyList()
            }
            "complex" -> {
                requireCount(name, args, 2, types.size)
                val argumentTypes = types.mapIndexed { index, type ->
                    if (type != untypedComplex) type else {
                        val value = constantComplex(args[index], scope)
                            ?: error("complex arguments must be floating-point values")
                        if (value.imaginary.numerator.signum() != 0)
                            error("complex arguments must be floating-point values")
                        untypedFloat
                    }
                }
                if (argumentTypes.any { !isFloatArgument(it) }) error("complex arguments must be floating-point values")
                val first = argumentTypes[0]
                val second = argumentTypes[1]
                if (!isUntyped(first) && !isUntyped(second) && !sameType(first, second))
                    error("complex arguments must have the same type")
                val typed = listOf(first, second).firstOrNull { !isUntyped(it) }
                listOf(when {
                    typed == null -> untypedComplex
                    underlying(typed) in setOf(NamedGoType("float32"), predeclaredFloat32Type) -> predeclaredComplex64Type
                    else -> predeclaredComplex128Type
                })
            }
            "real", "imag" -> {
                requireCount(name, args, 1, types.size)
                val type = types.single()
                if (type == untypedComplex) listOf(untypedFloat)
                else when (underlying(type)) {
                    NamedGoType("complex64"), predeclaredComplex64Type -> listOf(predeclaredFloat32Type)
                    NamedGoType("complex128"), predeclaredComplex128Type -> listOf(predeclaredFloat64Type)
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
        var operandLeft = left
        var operandRight = right
        if (operator != TokenKind.SHL && operator != TokenKind.SHR) {
            if (leftExpression?.let { nonConstantUntypedShift(it, scope) } != null &&
                !isUntyped(operandRight) && isInteger(operandRight)) {
                requireIntegerConstantRepresentable(leftExpression, operandRight, scope)
                operandLeft = operandRight
            }
            if (rightExpression?.let { nonConstantUntypedShift(it, scope) } != null &&
                !isUntyped(operandLeft) && isInteger(operandLeft)) {
                requireIntegerConstantRepresentable(rightExpression, operandLeft, scope)
                operandRight = operandLeft
            }
        }
        if (operator != TokenKind.SHL && operator != TokenKind.SHR) {
            if (isUntyped(operandLeft) && !isUntyped(operandRight)) leftExpression?.let { requireIntegerConstantRepresentable(it, operandRight, scope) }
            if (isUntyped(operandRight) && !isUntyped(operandLeft)) rightExpression?.let { requireIntegerConstantRepresentable(it, operandLeft, scope) }
        }
        if (operator == TokenKind.SHL || operator == TokenKind.SHR) {
            if (isUntyped(operandLeft)) {
                if (leftExpression?.let { constantInteger(it, scope) } == null)
                    error("left operand of shift must be an integer")
            } else if (!isInteger(operandLeft)) error("left operand of shift must be an integer")

            if (isUntyped(operandRight)) {
                val shiftExpression = rightExpression
                    ?: error("shift count must be a non-negative integer constant or unsigned integer")
                val count = constantInteger(shiftExpression, scope)
                    ?: error("shift count must be a non-negative integer constant or unsigned integer")
                if (count.signum() < 0) error("negative shift count")
                requireIntegerConstantRepresentable(shiftExpression, predeclaredUint64Type, scope)
            } else if (!isUnsignedInteger(operandRight)) {
                error("shift count must have unsigned integer type")
            }
            return if (isUntyped(operandLeft)) {
                if (rightExpression?.let { isConstantExpression(it, scope) } == false) {
                    defaultType(operandLeft)
                } else untypedInt
            } else operandLeft
        }
        val l = underlying(operandLeft); val r = underlying(operandRight)
        if (operator in setOf(TokenKind.LAND, TokenKind.LOR)) {
            requireBoolean(operandLeft, "logical operator")
            requireBoolean(operandRight, "logical operator")
            requireSameOperands(operandLeft, operandRight, leftExpression, rightExpression, scope)
            return commonType(operandLeft, operandRight)
        }
        if (operator in setOf(TokenKind.EQL, TokenKind.NEQ)) {
            if (!comparisonCompatible(operandLeft, operandRight, leftExpression, rightExpression, scope))
                error("incompatible comparison: $operandLeft and $operandRight")
            if (operandLeft == nilType) {
                if (!isNilable(operandRight)) error("cannot compare nil with $operandRight")
            } else if (operandRight == nilType) {
                if (!isNilable(operandLeft)) error("cannot compare $operandLeft with nil")
            } else if (!isComparable(operandLeft) || !isComparable(operandRight)) {
                error("cannot compare values of type $operandLeft and $operandRight")
            }
            return comparisonResultType(leftExpression, rightExpression, scope)
        }
        if (operator in setOf(TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ)) {
            if (!((isOrderedNumeric(operandLeft) && isOrderedNumeric(operandRight)) || (isString(operandLeft) && isString(operandRight)))) error("invalid ordered comparison")
            requireSameOperands(operandLeft, operandRight, leftExpression, rightExpression, scope)
            return comparisonResultType(leftExpression, rightExpression, scope)
        }
        if (operator == TokenKind.ADD && isString(operandLeft) && isString(operandRight)) {
            requireSameOperands(operandLeft, operandRight, leftExpression, rightExpression, scope)
            return commonType(operandLeft, operandRight)
        }
        if (operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.MUL, TokenKind.QUO, TokenKind.REM) && !isNumeric(operandLeft)) error("arithmetic requires numeric operands")
        if (operator in setOf(TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT, TokenKind.REM) && !isInteger(operandLeft)) error("operator requires integer operands")
        if (!isNumeric(operandLeft) && operator !in setOf(TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT, TokenKind.REM)) error("invalid binary operands")
        requireSameOperands(operandLeft, operandRight, leftExpression, rightExpression, scope)
        return commonType(operandLeft, operandRight)
    }

    private fun constantOperandsAssignable(
        left: GoTypeSyntax,
        right: GoTypeSyntax,
        leftExpression: Expression?,
        rightExpression: Expression?,
        scope: Scope
    ): Boolean = constantOperandAssignable(left, right, leftExpression, scope) ||
        constantOperandAssignable(right, left, rightExpression, scope)

    private fun comparisonCompatible(
        left: GoTypeSyntax,
        right: GoTypeSyntax,
        leftExpression: Expression?,
        rightExpression: Expression?,
        scope: Scope
    ): Boolean = constantOperandsAssignable(left, right, leftExpression, rightExpression, scope)

    private fun constantOperandAssignable(
        from: GoTypeSyntax,
        to: GoTypeSyntax,
        expression: Expression?,
        scope: Scope
    ): Boolean {
        if (assignable(from, to)) {
            if (!isUntyped(from) || expression == null) return true
            return try {
                requireIntegerConstantRepresentable(expression, to, scope)
                true
            } catch (_: GoTypeError) {
                false
            }
        }
        return constantIntegerAssignable(from, to, expression, scope)
    }

    private fun constantIntegerAssignable(from: GoTypeSyntax, to: GoTypeSyntax, expression: Expression?, scope: Scope): Boolean {
        if (expression == null || !isUntyped(from) || !isInteger(to)) return false
        val integer = constantInteger(expression, scope) ?: constantComplex(expression, scope)?.let { complex ->
            complex.takeIf { it.imaginary.numerator.signum() == 0 && it.real.isInteger() }?.real?.numerator
        } ?: return false
        if (integer.signum() < 0 && isUnsignedInteger(to)) return false
        return try {
            requireIntegerConstantRepresentable(expression, to, scope)
            true
        } catch (_: GoTypeError) {
            false
        }
    }

    private fun comparisonResultType(left: Expression?, right: Expression?, scope: Scope): GoTypeSyntax =
        if (left != null && right != null && isConstantExpression(left, scope) && isConstantExpression(right, scope))
            untypedBool else predeclaredBoolType

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

    private fun requireDefaultValues(values: List<GoTypeSyntax>, expressions: List<Expression>, context: String, scope: Scope = globals) {
        if (values.size != expressions.size) return
        values.zip(expressions).forEach { (from, expression) ->
            if (from == nilType) error("use of untyped nil in $context")
            if (isUntyped(from)) requireIntegerConstantRepresentable(expression, defaultType(from), scope)
            nonConstantUntypedShift(expression, scope)?.let { shift ->
                requireIntegerConstantRepresentable(
                    shift.left, defaultUntypedShiftType(expressionType(shift.left, scope)), scope
                )
            }
        }
    }

    private fun requireAssignable(
        from: GoTypeSyntax, to: GoTypeSyntax, context: String, expression: Expression? = null, scope: Scope = globals
    ) {
        if (expression != null && isUntyped(from) && underlying(to) is InterfaceGoType &&
            interfaceMethods(to).isEmpty()) {
            if (!isConstantExpression(expression, scope))
                error("untyped value is not assignable to $to in $context")
            requireIntegerConstantRepresentable(expression, defaultType(from), scope)
            return
        }
        if (expression != null && nonConstantUntypedShift(expression, scope) != null) {
            if (isInteger(to)) {
                requireIntegerConstantRepresentable(expression, to, scope)
                return
            }
            if (underlying(to) is InterfaceGoType) {
                val shift = nonConstantUntypedShift(expression, scope)!!
                requireIntegerConstantRepresentable(
                    expression, defaultUntypedShiftType(expressionType(shift.left, scope)), scope
                )
            } else error("left operand of shift must be integer in this context")
        }
        val contextualFrom = if (expression != null && containsNonConstantUntypedShift(expression, scope)) {
            val contextualType = if (underlying(to) is InterfaceGoType) {
                if (isUntyped(from)) defaultType(from) else from
            } else to
            expressionType(expression, scope, contextualType)
        } else from
        val integralFloatConstant = constantIntegerAssignable(contextualFrom, to, expression, scope)
        val comparisonResultAssignable = (expression?.unparenthesized() as? BinaryExpression)?.operator in
            setOf(TokenKind.EQL, TokenKind.NEQ, TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ) &&
            isBoolean(contextualFrom) && isBoolean(to)
        if (!assignable(contextualFrom, to) && !integralFloatConstant && !comparisonResultAssignable)
            error("cannot use $contextualFrom as $to in $context")
        expression?.let { requireIntegerConstantRepresentable(it, to, scope) }
    }

    private fun nonConstantUntypedShift(expression: Expression, scope: Scope): BinaryExpression? {
        val shift = expression.unparenthesized() as? BinaryExpression ?: return null
        if (shift.operator !in setOf(TokenKind.SHL, TokenKind.SHR) || !isUntyped(expressionType(shift.left, scope))) return null
        return shift.takeUnless { isConstantExpression(it.right, scope) }
    }

    private fun containsNonConstantUntypedShift(expression: Expression, scope: Scope): Boolean = when (expression) {
        is ParenthesizedExpression -> containsNonConstantUntypedShift(expression.expression, scope)
        is UnaryExpression -> containsNonConstantUntypedShift(expression.operand, scope)
        is BinaryExpression -> nonConstantUntypedShift(expression, scope) != null ||
            containsNonConstantUntypedShift(expression.left, scope) ||
            containsNonConstantUntypedShift(expression.right, scope)
        is CallExpression -> containsNonConstantUntypedShift(expression.function, scope) ||
            expression.arguments.any { containsNonConstantUntypedShift(it, scope) }
        is SelectorExpression -> containsNonConstantUntypedShift(expression.receiver, scope)
        is IndexExpression -> containsNonConstantUntypedShift(expression.receiver, scope) ||
            containsNonConstantUntypedShift(expression.index, scope)
        is SliceExpression -> containsNonConstantUntypedShift(expression.receiver, scope) ||
            listOfNotNull(expression.low, expression.high).any { containsNonConstantUntypedShift(it, scope) }
        is TypeAssertionExpression -> containsNonConstantUntypedShift(expression.receiver, scope)
        is TypeSwitchGuardExpression -> containsNonConstantUntypedShift(expression.receiver, scope)
        is CompositeLiteral -> expression.elements.any { element ->
            (element.key?.let { containsNonConstantUntypedShift(it, scope) } ?: false) ||
                containsNonConstantUntypedShift(element.value, scope)
        }
        is ElidedCompositeLiteral -> expression.elements.any { element ->
            (element.key?.let { containsNonConstantUntypedShift(it, scope) } ?: false) ||
                containsNonConstantUntypedShift(element.value, scope)
        }
        is FunctionLiteralExpression -> false
        is NameExpression, is LiteralExpression, is TypeExpression -> false
    }

    private fun requireIntegerConstantRepresentable(expression: Expression, target: GoTypeSyntax, scope: Scope = globals) {
        val shift = expression.unparenthesized() as? BinaryExpression
        if (shift != null && shift.operator in setOf(TokenKind.SHL, TokenKind.SHR) &&
            constantInteger(shift.right, scope) == null && isUntyped(expressionType(shift.left, scope))) {
            val contextualType = if (underlying(target) is InterfaceGoType)
                defaultUntypedShiftType(expressionType(shift.left, scope)) else target
            if (!isInteger(contextualType)) error("left operand of shift must be integer in this context")
            requireIntegerConstantRepresentable(shift.left, contextualType, scope)
            return
        }
        val checkedTarget = if (underlying(target) is InterfaceGoType) {
            val sourceType = expressionType(expression, scope)
            if (isUntyped(sourceType)) defaultType(sourceType) else target
        } else target
        val targetName = (underlying(checkedTarget) as? NamedGoType)?.name ?: return
        if (targetName in floatNames) {
            val value = constantRational(expression, scope) ?: constantInteger(expression, scope)?.let(GoRational::of)
                ?: constantComplex(expression, scope)?.let {
                    if (it.imaginary.numerator.signum() != 0)
                        error("constant is not representable as $checkedTarget")
                    it.real
                } ?: return
            val overflows = if (targetName in setOf("#predeclared-float32", "float32"))
                !value.toFloat().isFinite() else !value.toDouble().isFinite()
            if (overflows)
                error("constant overflows $checkedTarget")
            return
        }
        if (targetName in complexNames) {
            val value = constantComplex(expression, scope) ?: return
            val overflows = if (targetName in setOf("#predeclared-complex64", "complex64")) {
                !value.real.toFloat().isFinite() || !value.imaginary.toFloat().isFinite()
            } else !value.real.toDouble().isFinite() || !value.imaginary.toDouble().isFinite()
            if (overflows)
                error("constant overflows $checkedTarget")
            return
        }
        if (!isInteger(checkedTarget)) return
        val value = constantInteger(expression, scope) ?: constantComplex(expression, scope)?.let {
            if (it.imaginary.numerator.signum() != 0 || !it.real.isInteger())
                error("constant is not representable as $checkedTarget")
            it.real.numerator
        } ?: run {
            if (isConstantExpression(expression, scope)) error("constant is not representable as $checkedTarget")
            return
        }
        val name = (underlying(checkedTarget) as? NamedGoType)?.name ?: return
        val bits = when (name) {
            "#predeclared-int8", "#predeclared-uint8", "int8", "uint8", "byte" -> 8
            "#predeclared-int16", "#predeclared-uint16", "int16", "uint16" -> 16
            "#predeclared-int32", "#predeclared-uint32", "int32", "uint32" -> 32
            else -> 64
        }
        val unsigned = name in setOf(
            "#predeclared-uint", "#predeclared-uint8", "#predeclared-uint16", "#predeclared-uint32", "#predeclared-uint64", "#predeclared-uintptr",
            "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte"
        )
        val minimum = if (unsigned) BigInteger.ZERO else BigInteger.ONE.shiftLeft(bits - 1).negate()
        val maximum = if (unsigned) BigInteger.ONE.shiftLeft(bits).subtract(BigInteger.ONE)
            else BigInteger.ONE.shiftLeft(bits - 1).subtract(BigInteger.ONE)
        if (value < minimum || value > maximum) error("constant $value overflows $checkedTarget")
    }

    private fun assignable(from: GoTypeSyntax, to: GoTypeSyntax): Boolean {
        if (sameType(from, to)) return true
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
                f == untypedFloat -> (t as? NamedGoType)?.name?.let { it in floatNames || it in complexNames } == true
                f == untypedComplex -> isNumeric(to)
                f == untypedString -> isString(to)
                f == untypedBool -> isBoolean(to)
                else -> false
            }
        }
        if (isNamed(from) && isNamed(to)) return false
        return sameType(underlying(from), underlying(to)) && (!isNamed(from) || !isNamed(to))
    }

    private fun convertible(from: GoTypeSyntax, to: GoTypeSyntax, constant: Boolean = false): Boolean {
        if (assignable(from, to)) return true
        val source = underlying(from)
        val destination = underlying(to)
        if (sameType(source, destination)) return true
        if (from is PointerGoType && to is PointerGoType &&
            sameType(underlying(from.element), underlying(to.element))) return true
        val numericConversion = when {
            constant -> isNumeric(from) && isNumeric(to)
            isComplex(from) && isComplex(to) -> true
            (isInteger(from) || isFloatArgument(from)) && (isInteger(to) || isFloatArgument(to)) -> true
            else -> false
        }
        val unsafePointerConversion = (isUnsafePointerType(from) &&
            (underlying(to) is PointerGoType || isUintptrType(to))) ||
            (isUnsafePointerType(to) && (underlying(from) is PointerGoType || isUintptrType(from)))
        return numericConversion ||
            unsafePointerConversion ||
            (isString(from) && (isString(to) || isByteOrRuneSlice(to))) ||
            (isInteger(from) && isString(to)) ||
            (isByteOrRuneSlice(from) && isString(to))
    }

    private fun isByteOrRuneSlice(type: GoTypeSyntax): Boolean {
        val slice = underlying(type) as? SliceGoType ?: return false
        return isByteElementType(slice.element) || isRuneElementType(slice.element)
    }

    private fun isByteElementType(type: GoTypeSyntax): Boolean =
        canonicalPredeclaredAlias(type) == predeclaredUint8Type

    private fun isRuneElementType(type: GoTypeSyntax): Boolean =
        canonicalPredeclaredAlias(type) == predeclaredInt32Type

    private fun isPredeclaredRuneType(type: GoTypeSyntax): Boolean =
        canonicalPredeclaredAlias(type) == predeclaredInt32Type

    private fun validateType(type: GoTypeSyntax, active: Set<String> = emptySet(), indirect: Boolean = false) {
        when (type) {
            is NamedGoType -> {
                if (type.name in packagePaths) error("package ${type.name} is not a type")
                if (!isBuiltinType(type.name) && type.name !in typeDeclarations) error("undefined type ${type.name}")
                if (type.name in active) {
                    if (indirect) return
                    error("invalid recursive type ${type.name}")
                }
                typeDeclarations[type.name]?.let { declaredType ->
                    validateType(declaredType, active + type.name, indirect)
                    val struct = underlying(NamedGoType(type.name)) as? StructGoType
                    struct?.fields?.flatMap { field ->
                        field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                    }?.filter { it != "_" }?.forEach { fieldName ->
                        if (methods.containsKey("${type.name}.$fieldName"))
                            error("field and method name conflict: $fieldName")
                    }
                }
            }
            is QualifiedGoType -> {
                val path = packagePaths[type.packageName]?.let { importedPackagePath(type.packageName) } ?: type.packageName
                if (standardPackageName(path) == "unsafe" && type.name == "Pointer") return
                if (standardPackageName(path) == "runtime" && type.name in GoRuntimePackage.exportedTypes) return
                if (importedPackages[path]?.hasExportedType(type.name) != true)
                    error("undefined imported type ${type.packageName}.${type.name}")
            }
            is PointerGoType -> validateType(type.element, active, true)
            is SliceGoType -> validateType(type.element, active, true)
            is ArrayGoType -> {
                val length = type.length ?: error("inferred array length is only valid in a composite literal")
                requireIntegerValue(expressionType(length, globals), length, "array length", globals)
                val constant = constantInteger(length, globals) ?: error("array length must be constant")
                if (constant.signum() < 0) error("array length must be non-negative")
                requireIntegerConstantRepresentable(length, predeclaredIntType, globals)
                validateType(type.element, active, indirect)
            }
            is MapGoType -> {
                validateType(type.key, active, indirect)
                validateType(type.value, active, true)
                if (!isComparable(type.key)) error("invalid map key type")
            }
            is ChannelGoType -> validateType(type.element, active, true)
            is StructGoType -> {
                validateStructFields(type)
                type.fields.forEach { validateType(it.type, active, indirect) }
            }
            is InterfaceGoType -> {
                val names = mutableSetOf<String>()
                type.embeddedTypes.forEach {
                    validateType(it, active)
                    if (underlying(it) !is InterfaceGoType) error("embedded interface element must be an interface")
                }
                type.methods.forEach { method ->
                    if (method.name == "_") error("interface method name cannot be blank")
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

    private fun standardPackageName(path: String): String? {
        return when (path) {
            "fmt", "math", "runtime", "unsafe" -> path
            else -> null
        }
    }
    private fun resolveFunctionType(function: FunctionDeclaration, scope: Scope) = FunctionGoType(
        function.parameterTypes.mapIndexed { i, t ->
            ParameterSyntax(
                function.parameters.getOrNull(i), resolveLocalType(t, scope),
                function.variadic && i == function.parameterTypes.lastIndex
            )
        },
        function.resultTypes.map { resolveLocalType(it, scope) }
    )
    private fun functionType(function: FunctionDeclaration) = checkedFunctionTypes[function]
        ?: FunctionGoType(function.parameterTypes.mapIndexed { i, t ->
            ParameterSyntax(function.parameters.getOrNull(i), t, function.variadic && i == function.parameterTypes.lastIndex)
        }, function.resultTypes)
    private fun namedType(type: GoTypeSyntax): String? = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> "${type.packageName}.${type.name}"
        is PointerGoType -> namedType(type.element)
        else -> null
    }
    private fun methodBaseName(type: GoTypeSyntax): String? = when (val base =
        if (type is PointerGoType) type.element else type) {
        is NamedGoType -> base.name
        is QualifiedGoType -> "${base.packageName}.${base.name}"
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
            val key = interfaceMethodKey(method)
            val previous = result.putIfAbsent(key, signature)
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
                val nodeType = selectorBaseType(node.type)
                val named = (node.type as? PointerGoType)?.element as? QualifiedGoType
                    ?: node.type as? QualifiedGoType
                if (named != null && nodeType !is InterfaceGoType) {
                    val imported = importedPackages[named.packageName]
                    val foreignType = if (node.pointer) PointerGoType(NamedGoType(named.name)) else NamedGoType(named.name)
                    imported?.methodSet(foreignType)?.forEach { (name, signature) ->
                        candidates.getOrPut(name) { mutableListOf() } += imported.externalizeType(signature, named.packageName) as FunctionGoType
                    }
                }
                when (nodeType) {
                    is InterfaceGoType -> interfaceMethods(nodeType).forEach { (name, signature) ->
                        candidates.getOrPut(name) { mutableListOf() } += signature
                    }
                    is StructGoType -> {
                        val baseName = methodBaseName(node.type)
                        if (baseName != null) methods.values.forEach { method ->
                            val receiverType = method.receiver?.type ?: return@forEach
                            if (methodBaseName(receiverType) != baseName || receiverType is PointerGoType && !node.pointer) return@forEach
                            candidates.getOrPut(packageMethodKey(method.name)) { mutableListOf() } += functionType(method)
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
                        val baseName = methodBaseName(node.type)
                        if (baseName != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            if (methodBaseName(receiverType) != baseName || receiverType is PointerGoType && !node.pointer) return@methodLoop
                            candidates.getOrPut(packageMethodKey(method.name)) { mutableListOf() } += functionType(method)
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

    private fun interfaceMethodKey(method: InterfaceMethodSyntax): String =
        if (isExportedIdentifier(method.name)) method.name
        else "${method.packagePath ?: packageIdentity ?: packageName ?: "<package>"}:${method.name}"

    private fun packageMethodKey(name: String): String = if (isExportedIdentifier(name)) name
        else "${packageIdentity ?: packageName ?: "<package>"}:$name"

    private fun sameType(left: GoTypeSyntax, right: GoTypeSyntax): Boolean {
        if (left == right && !containsStructLiteral(left)) return true
        if (canonicalPredeclaredAlias(left) == canonicalPredeclaredAlias(right) &&
            !containsStructLiteral(left) && !containsStructLiteral(right)) return true
        return when {
            left is QualifiedGoType && right is QualifiedGoType -> left.packageName == right.packageName && left.name == right.name
            left is PointerGoType && right is PointerGoType -> sameType(left.element, right.element)
            left is SliceGoType && right is SliceGoType -> sameType(left.element, right.element)
            left is ArrayGoType && right is ArrayGoType -> sameArrayLength(left.length, right.length) && sameType(left.element, right.element)
            left is MapGoType && right is MapGoType -> sameType(left.key, right.key) && sameType(left.value, right.value)
            left is ChannelGoType && right is ChannelGoType -> left.direction == right.direction && sameType(left.element, right.element)
            left is StructGoType && right is StructGoType -> {
                data class FieldIdentity(
                    val name: String,
                    val packagePath: String?,
                    val type: GoTypeSyntax,
                    val tag: String,
                    val embedded: Boolean
                )
                val leftFields = left.fields.flatMap { field ->
                    field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }.map { name ->
                        FieldIdentity(name, unexportedFieldPackagePath(field, name), field.type,
                            field.tag.orEmpty(), field.names.isEmpty())
                    }
                }
                val rightFields = right.fields.flatMap { field ->
                    field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }.map { name ->
                        FieldIdentity(name, unexportedFieldPackagePath(field, name), field.type,
                            field.tag.orEmpty(), field.names.isEmpty())
                    }
                }
                leftFields.size == rightFields.size && leftFields.zip(rightFields).all { (a, b) ->
                    a.name == b.name && a.packagePath == b.packagePath && a.tag == b.tag &&
                        a.embedded == b.embedded && sameType(a.type, b.type)
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

    private fun containsStructLiteral(type: GoTypeSyntax): Boolean = when (type) {
        is PointerGoType -> containsStructLiteral(type.element)
        is SliceGoType -> containsStructLiteral(type.element)
        is ArrayGoType -> containsStructLiteral(type.element)
        is MapGoType -> containsStructLiteral(type.key) || containsStructLiteral(type.value)
        is ChannelGoType -> containsStructLiteral(type.element)
        is StructGoType -> true
        is InterfaceGoType -> type.methods.any { method ->
            method.parameters.any { containsStructLiteral(it.type) } || method.results.any(::containsStructLiteral)
        } || type.embeddedTypes.any(::containsStructLiteral)
        is FunctionGoType -> type.parameters.any { containsStructLiteral(it.type) } || type.results.any(::containsStructLiteral)
        else -> false
    }

    private fun unexportedFieldPackagePath(field: StructFieldSyntax, name: String): String? {
        if (!GoUnicode6.isUnexportedIdentifier(name)) return null
        val embeddedType = if (field.names.isEmpty()) field.type.let {
            if (it is PointerGoType) it.element else it
        } else null
        return field.packagePath ?: (embeddedType as? QualifiedGoType)?.packageName ?: packageIdentity ?: packageName
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
            else expression.name in setOf("true", "false") || dotImportedConstant(expression.name) != null ||
                dotImportedConstantRational(expression.name) != null
        is SelectorExpression -> expression.receiver is NameExpression &&
            scope.getOrNull(expression.receiver.name) == null && scope.typeBinding(expression.receiver.name) == null &&
            (packagePaths[expression.receiver.name]?.let { standardPackageName(it) == "math" &&
                GoMathPackage.constant(expression.field) != null } == true ||
                packagePaths[expression.receiver.name]?.let { standardPackageName(it) == "unsafe" &&
                    GoUnsafePackage.constant(expression.field) != null } == true ||
                packagePaths[expression.receiver.name]?.let { importedConstant(it, expression.field) != null } == true)
        is ParenthesizedExpression -> isConstantExpression(expression.expression, scope)
        is UnaryExpression -> expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.NOT, TokenKind.XOR) &&
            isConstantExpression(expression.operand, scope)
        is BinaryExpression -> isConstantExpression(expression.left, scope) && isConstantExpression(expression.right, scope)
        is CallExpression -> {
            val target = constantConversionTarget(expression, scope)
            when {
                target != null -> expression.arguments.size == 1 && isConstantValueType(target) &&
                    isConstantExpression(expression.arguments.single(), scope)
                expression.function == NameExpression("len") || expression.function == NameExpression("cap") ->
                    constantInteger(expression, scope) != null
                expression.function in setOf(NameExpression("complex"), NameExpression("real"), NameExpression("imag")) ->
                    expression.arguments.isNotEmpty() && expression.arguments.all { isConstantExpression(it, scope) }
                expression.function is SelectorExpression || expression.function is NameExpression -> unsafeConstant(expression, scope) != null
                else -> false
            }
        }
        else -> false
    }

    private fun isConstantValueType(type: GoTypeSyntax): Boolean =
        isBoolean(type) || isNumeric(type) || isString(type)

    private fun constantConversionTarget(call: CallExpression, scope: Scope): GoTypeSyntax? =
        when (val function = call.function.unparenthesized()) {
            is TypeExpression -> resolveLocalType(function.type, scope)
            is NameExpression -> if (scope.getOrNull(function.name) == null && isTypeName(function.name, scope))
                resolveLocalType(NamedGoType(function.name), scope) else null
            is SelectorExpression -> importedPackageType(function, scope)
            else -> null
        }

    private fun constantRational(expression: Expression, scope: Scope = globals): GoRational? = when (expression) {
        is NameExpression -> scope.constantRational(expression.name) ?: if (scope.getOrNull(expression.name) == null)
            dotImportedConstantRational(expression.name) else null
        is SelectorExpression -> {
            val alias = (expression.receiver as? NameExpression)?.name
            val path = alias?.takeIf { scope.getOrNull(it) == null && scope.typeBinding(it) == null }?.let(::importedPackagePath)
            if (path != null && standardPackageName(path) == "math")
                GoMathPackage.constant(expression.field)
            else if (path != null && standardPackageName(path) == "unsafe")
                GoUnsafePackage.constant(expression.field)?.let(GoRational::of)
            else path?.let { importedConstant(it, expression.field)?.rational }
        }
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
            TokenKind.XOR -> if (!value.isInteger()) null else {
                val operandType = expressionType(expression.operand, scope)
                GoRational.of(complementIntegerConstant(value.numerator, operandType))
            }
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
            val target = constantConversionTarget(expression, scope)
            if (target == null || !isNumeric(target) || expression.arguments.size != 1 || expression.expandLastArgument) null
            else constantRational(expression.arguments.single(), scope)
        }
        else -> null
    }

    private fun dotImportedConstantRational(name: String): GoRational? = dotImportPaths.firstNotNullOfOrNull { path ->
        if (standardPackageName(path) == "math") GoMathPackage.constant(name)
        else if (standardPackageName(path) == "unsafe") GoUnsafePackage.constant(name)?.let(GoRational::of)
        else importedConstant(path, name)?.rational
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
            TokenKind.XOR -> complementIntegerConstant(value, expressionType(expression.operand, scope))
            else -> null
        } }
        is CallExpression -> {
            unsafeConstant(expression, scope)?.let { return it }
            val builtinName = (expression.function as? NameExpression)?.name
            val builtinLength = builtinName in setOf("len", "cap") && builtinName != null &&
                scope.getOrNull(builtinName) == null && builtinName !in packagePaths
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
                val target = constantConversionTarget(expression, scope)
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
                TokenKind.SHL -> if (left.signum() == 0) BigInteger.ZERO else left.shiftLeft(right.intValueExact())
                TokenKind.SHR -> when {
                    right.signum() < 0 -> return@runCatching null
                    right >= BigInteger.valueOf(left.bitLength().toLong()) -> if (left.signum() < 0) BigInteger.ONE.negate() else BigInteger.ZERO
                    else -> left.shiftRight(right.intValueExact())
                }
                else -> return@runCatching null
            } }.getOrNull()
        }
        else -> null
        }
    }

    private fun unsafeIntrinsicName(function: Expression, scope: Scope): String? = when (val target = function.unparenthesized()) {
        is SelectorExpression -> {
            val alias = (target.receiver as? NameExpression)?.name ?: return null
            if (scope.getOrNull(alias) != null || scope.typeBinding(alias) != null ||
                packagePaths[alias]?.let(::standardPackageName) != "unsafe") return null
            target.field.takeIf { GoUnsafePackage.functionType(it) != null }
        }
        is NameExpression -> target.name.takeIf { scope.getOrNull(it) == null && scope.typeBinding(it) == null &&
            "unsafe" in dotImportPaths && GoUnsafePackage.functionType(it) != null }
        else -> null
    }

    private fun selectorPath(expression: Expression): Pair<Expression, List<String>>? {
        val fields = mutableListOf<String>()
        var current = expression
        while (current is SelectorExpression) {
            fields += current.field
            current = current.receiver
        }
        if (fields.isEmpty()) return null
        fields.reverse()
        return current to fields
    }

    private fun unsafeConstant(call: CallExpression, scope: Scope): BigInteger? {
        val name = unsafeIntrinsicName(call.function, scope) ?: return null
        if (call.arguments.size != 1 || call.expandLastArgument) return null
        val arrayLength: (Expression) -> BigInteger = { expression ->
            constantInteger(expression, scope) ?: throw IllegalArgumentException("array length must be constant")
        }
        return try {
            val operand = call.arguments.single()
            when (name) {
                "Sizeof", "Alignof" -> {
                    val type = expressionType(operand, scope).let { if (isUntyped(it)) defaultType(it) else it }
                    val layout = GoUnsafePackage.layout(type, ::underlying, arrayLength)
                    BigInteger.valueOf(if (name == "Sizeof") layout.size else layout.align)
                }
                "Offsetof" -> {
                    val (base, fields) = selectorPath(operand) ?: return null
                    var type = expressionType(base, scope)
                    var offset = 0L
                    fields.forEach { fieldName ->
                        val field = GoUnsafePackage.fieldOffset(type, fieldName, ::underlying, arrayLength) ?: return null
                        offset = Math.addExact(offset, field.first)
                        type = field.second
                    }
                    BigInteger.valueOf(offset)
                }
                else -> null
            }
        } catch (_: ArithmeticException) {
            error("unsafe layout overflows uintptr")
        } catch (_: IllegalArgumentException) {
            null
        }
    }

    private fun constantStringLength(expression: Expression, scope: Scope): BigInteger? = when (expression) {
        is LiteralExpression -> if (expression.token.kind == TokenKind.STRING)
            stringLiteralByteLength(expression.token.lexeme)?.let(BigInteger::valueOf) else null
        is NameExpression -> scope.constantStringLength(expression.name)
            ?: if (scope.getOrNull(expression.name) == null) dotImportedConstant(expression.name)?.second?.stringLength else null
        is SelectorExpression -> (expression.receiver as? NameExpression)?.name?.let(packagePaths::get)
            ?.let { importedConstant(it, expression.field)?.stringLength }
        is ParenthesizedExpression -> constantStringLength(expression.expression, scope)
        is BinaryExpression -> if (expression.operator == TokenKind.ADD) {
            val left = constantStringLength(expression.left, scope)
            val right = constantStringLength(expression.right, scope)
            if (left != null && right != null) left + right else null
        } else null
        is CallExpression -> {
            val target = constantConversionTarget(expression, scope)
            if (target == null || !isString(target) || expression.arguments.size != 1 || expression.expandLastArgument) null
            else constantStringLength(expression.arguments.single(), scope) ?: constantInteger(expression.arguments.single(), scope)?.let { value ->
                val codePoint = runCatching { value.intValueExact() }.getOrNull()
                val rune = if (codePoint == null || codePoint !in 0..Character.MAX_CODE_POINT) 0xfffd else codePoint
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
                is NameExpression -> scope.getOrNull(target.name) == null && isTypeName(target.name, scope)
                is SelectorExpression -> importedPackageType(target, scope) != null
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
        is FunctionLiteralExpression -> false
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
        BigInteger(decodeGoCharacterLiteral(text).toString())
    }.getOrNull()

    private fun arrayLengthSyntax(expression: Expression): Any = when (expression) {
        is LiteralExpression -> expression.token.kind to expression.token.lexeme
        is NameExpression -> "name" to expression.name
        is UnaryExpression -> "unary" to (expression.operator to arrayLengthSyntax(expression.operand))
        is BinaryExpression -> "binary" to (expression.operator to (arrayLengthSyntax(expression.left) to arrayLengthSyntax(expression.right)))
        is ParenthesizedExpression -> arrayLengthSyntax(expression.expression)
        else -> expression
    }

    private fun underlying(type: GoTypeSyntax, seen: Set<String> = emptySet()): GoTypeSyntax = when (type) {
        is NamedGoType -> when (type.name) {
            "#predeclared-error" -> errorInterfaceType
            "#predeclared-bool" -> boolType
            "#predeclared-float32", "#predeclared-float64", "#predeclared-string",
            "#predeclared-complex64", "#predeclared-complex128" -> type
            "#predeclared-int", "#predeclared-int8", "#predeclared-int16", "#predeclared-int32",
            "#predeclared-int64", "#predeclared-uint", "#predeclared-uint8", "#predeclared-uint16",
            "#predeclared-uint32", "#predeclared-uint64", "#predeclared-uintptr" -> type
            else -> typeDeclarations[type.name]?.let { if (type.name in seen) type else underlying(it, seen + type.name) }
                ?: when (type.name) {
                    "byte" -> predeclaredUint8Type
                    "rune" -> predeclaredInt32Type
                    "error" -> errorInterfaceType
                    else -> type
                }
        }
        is QualifiedGoType -> importedPackages[type.packageName]?.let { imported ->
            imported.externalizeType(imported.underlying(NamedGoType(type.name)), type.packageName)
        } ?: if (type.packageName == "unsafe" && type.name == "Pointer")
            PointerGoType(InterfaceGoType(emptyList())) else GoRuntimePackage.type(type.name)
            .takeIf { type.packageName == "runtime" } ?: type
        else -> type
    }
    private fun isNamed(type: GoTypeSyntax) = type is QualifiedGoType || type is NamedGoType &&
        (!type.name.startsWith("#") || type.name.startsWith("#predeclared-"))
    private fun isUnsafePointerType(type: GoTypeSyntax) = type == QualifiedGoType("unsafe", "Pointer")
    private fun isUintptrType(type: GoTypeSyntax) =
        (underlying(type) as? NamedGoType)?.name in setOf("#predeclared-uintptr", "uintptr")
    private fun isUntyped(type: GoTypeSyntax) = type is NamedGoType && type.name.startsWith("#untyped-")
    private fun isBuiltinType(name: String) = name in builtinTypes || name == "error" || name.startsWith("#predeclared-")
    private fun isNumeric(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedInt, untypedRune, untypedFloat, untypedComplex -> true
        is NamedGoType -> t.name in integerNames || t.name in floatNames || t.name in complexNames
        else -> false
    }
    private fun isComplex(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        untypedComplex -> true
        is NamedGoType -> t.name in complexNames
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
        (underlying(type) as? NamedGoType)?.name in setOf(
            "#predeclared-uint", "#predeclared-uint8", "#predeclared-uint16", "#predeclared-uint32", "#predeclared-uint64", "#predeclared-uintptr",
            "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte"
        )
    private fun complementIntegerConstant(value: BigInteger, type: GoTypeSyntax): BigInteger {
        if (!isUnsignedInteger(type)) return value.not()
        val mask = BigInteger.ONE.shiftLeft(integerBitWidth(type)).subtract(BigInteger.ONE)
        return value.not().and(mask)
    }
    private fun integerBitWidth(type: GoTypeSyntax): Int = when ((underlying(type) as? NamedGoType)?.name) {
        "#predeclared-int8", "#predeclared-uint8", "int8", "uint8", "byte" -> 8
        "#predeclared-int16", "#predeclared-uint16", "int16", "uint16" -> 16
        "#predeclared-uint32", "int32", "uint32" -> 32
        else -> 64
    }
    private fun isString(type: GoTypeSyntax) = underlying(type) == stringType ||
        underlying(type) == predeclaredStringType || type == untypedString
    private fun isBoolean(type: GoTypeSyntax) = underlying(type) == boolType || type == untypedBool
    private fun isNilable(type: GoTypeSyntax) = when (underlying(type)) { is PointerGoType, is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType, is InterfaceGoType -> true; else -> false }
    private fun isComparable(type: GoTypeSyntax): Boolean = when (val t = underlying(type)) {
        is SliceGoType, is MapGoType, is FunctionGoType -> false
        is ArrayGoType -> isComparable(t.element)
        is StructGoType -> t.fields.all { isComparable(it.type) }
        else -> true
    }
    private fun defaultType(type: GoTypeSyntax) = when (type) {
        untypedInt -> predeclaredIntType
        untypedRune -> predeclaredInt32Type
        untypedFloat -> predeclaredFloat64Type
        untypedComplex -> predeclaredComplex128Type
        untypedString -> predeclaredStringType
        untypedBool -> predeclaredBoolType
        else -> type
    }

    private fun defaultUntypedShiftType(type: GoTypeSyntax): GoTypeSyntax =
        if (type == untypedRune) predeclaredInt32Type else predeclaredIntType

    private fun canonicalPredeclaredAlias(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        byteType -> if ("byte" !in typeDeclarations) predeclaredUint8Type else type
        NamedGoType("uint8") -> if ("uint8" !in typeDeclarations) predeclaredUint8Type else type
        runeType -> if ("rune" !in typeDeclarations) predeclaredInt32Type else type
        intType -> if ("int" !in typeDeclarations) predeclaredIntType else type
        NamedGoType("error") -> if ("error" !in typeDeclarations) predeclaredErrorType else type
        NamedGoType("bool") -> if ("bool" !in typeDeclarations) predeclaredBoolType else type
        NamedGoType("float32") -> if ("float32" !in typeDeclarations) predeclaredFloat32Type else type
        NamedGoType("float64") -> if ("float64" !in typeDeclarations) predeclaredFloat64Type else type
        stringType -> if ("string" !in typeDeclarations) predeclaredStringType else type
        NamedGoType("complex64") -> if ("complex64" !in typeDeclarations) predeclaredComplex64Type else type
        NamedGoType("complex128") -> if ("complex128" !in typeDeclarations) predeclaredComplex128Type else type
        NamedGoType("int8") -> if ("int8" !in typeDeclarations) predeclaredInt8Type else type
        NamedGoType("int16") -> if ("int16" !in typeDeclarations) predeclaredInt16Type else type
        NamedGoType("int32") -> if ("int32" !in typeDeclarations) predeclaredInt32Type else type
        NamedGoType("int64") -> if ("int64" !in typeDeclarations) predeclaredInt64Type else type
        NamedGoType("uint") -> if ("uint" !in typeDeclarations) predeclaredUintType else type
        NamedGoType("uint16") -> if ("uint16" !in typeDeclarations) predeclaredUint16Type else type
        NamedGoType("uint32") -> if ("uint32" !in typeDeclarations) predeclaredUint32Type else type
        NamedGoType("uint64") -> if ("uint64" !in typeDeclarations) predeclaredUint64Type else type
        NamedGoType("uintptr") -> if ("uintptr" !in typeDeclarations) predeclaredUintptrType else type
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
        is NameExpression -> scope.getOrNull(target.name) == null && isTypeName(target.name, scope)
        is SelectorExpression -> importedPackageType(target, scope) != null
        else -> false
    }
    private fun isTypeName(name: String, scope: Scope): Boolean = scope.typeBinding(name) != null ||
        dotImportedType(name) != null || (name !in packagePaths && (isBuiltinType(name) || name in typeDeclarations))
    private fun requireMakeSize(type: GoTypeSyntax, expression: Expression, scope: Scope) {
        if (!isInteger(type) && !constantIntegerAssignable(type, predeclaredIntType, expression, scope))
            error("make size must be integer")
        // Go 1.0 specifies invalid sizes and values outside int as run-time panics.
    }

    private fun builtinTypeArgument(expression: Expression, scope: Scope): GoTypeSyntax {
        val requested = when (expression) {
            is TypeExpression -> expression.type
            is NameExpression -> {
                if (scope.getOrNull(expression.name) != null) error("${expression.name} is not a type")
                scope.typeBinding(expression.name)?.let(::NamedGoType)
                    ?: if (isTypeName(expression.name, scope)) NamedGoType(expression.name)
                    else error("make or new requires a type argument")
            }
            is SelectorExpression -> {
                if ((expression.receiver as? NameExpression)?.name?.let(scope::getOrNull) != null)
                    error("${expression.receiver} is not a package")
                importedPackageType(expression, scope) ?: error("make or new requires a type argument")
            }
            else -> error("make or new requires a type argument")
        }
        return resolveLocalType(requested, scope).also(::validateType)
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

    private class LocalUsage(val name: String, var used: Boolean = false)

    private class Scope(
        private val parent: Scope? = null,
        private val localUsage: MutableList<LocalUsage>? = parent?.localUsage
    ) {
        private val values = linkedMapOf<String, GoTypeSyntax>()
        private val trackedLocals = linkedMapOf<String, LocalUsage>()
        private val typeNames = linkedMapOf<String, String>()
        private val integerConstants = linkedMapOf<String, BigInteger>()
        private val constantNames = linkedSetOf<String>()
        fun child(trackLocalUsage: Boolean = false) = Scope(
            this,
            if (trackLocalUsage) mutableListOf() else localUsage
        )
        private val stringLengths = linkedMapOf<String, BigInteger>()
        private val rationalConstants = linkedMapOf<String, GoRational>()
        private val stringIdentities = linkedMapOf<String, String>()
        private val booleanConstants = linkedMapOf<String, Boolean>()
        private val complexConstants = linkedMapOf<String, ConstantComplexValue>()
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
            isFunction: Boolean = false,
            complexConstant: ConstantComplexValue? = null,
            trackUsage: Boolean = false,
            usageGroup: LocalUsage? = null
        ) {
            values[name] = type
            if ((trackUsage || usageGroup != null) && localUsage != null) {
                (usageGroup ?: LocalUsage(name).also(localUsage::add)).also {
                    trackedLocals[name] = it
                }
            } else trackedLocals.remove(name)
            if (isFunction) functionNames += name else functionNames -= name
            if (integerConstant == null) integerConstants.remove(name) else integerConstants[name] = integerConstant
            if (stringLength == null) stringLengths.remove(name) else stringLengths[name] = stringLength
            if (rationalConstant == null) rationalConstants.remove(name) else rationalConstants[name] = rationalConstant
            if (stringIdentity == null) stringIdentities.remove(name) else stringIdentities[name] = stringIdentity
            if (booleanConstant == null) booleanConstants.remove(name) else booleanConstants[name] = booleanConstant
            if (complexConstant == null) complexConstants.remove(name) else complexConstants[name] = complexConstant
            if (isConstant) constantNames += name else constantNames -= name
        }
        fun defineType(name: String, identity: String) { typeNames[name] = identity }
        fun typeBinding(name: String): String? = typeNames[name] ?: parent?.typeBinding(name)
        fun hasBinding(name: String): Boolean = name in values || name in typeNames || parent?.hasBinding(name) == true
        fun containsLocalType(name: String) = name in typeNames
        fun containsLocal(name: String) = name in values || name in typeNames
        fun get(name: String): GoTypeSyntax = getOrNull(name) ?: throw GoTypeError("undefined: $name")
        fun getOrNull(name: String): GoTypeSyntax? = values[name] ?: parent?.getOrNull(name)
        fun markUsed(name: String) {
            if (name in values) trackedLocals[name]?.used = true
            else parent?.markUsed(name)
        }
        fun newUsageGroup(name: String): LocalUsage? = localUsage?.let { usage ->
            LocalUsage(name).also(usage::add)
        }
        fun unusedLocalVariable(): String? = localUsage?.firstOrNull { !it.used }?.name
        fun isVariable(name: String): Boolean = if (name in values)
            name !in constantNames && name !in functionNames else parent?.isVariable(name) == true
        fun constantInteger(name: String): BigInteger? = if (name in values) integerConstants[name] else parent?.constantInteger(name)
        fun constantRational(name: String): GoRational? = if (name in values) rationalConstants[name]
            ?: integerConstants[name]?.let { GoRational.of(it) } else parent?.constantRational(name)
        fun constantStringLength(name: String): BigInteger? = if (name in values) stringLengths[name] else parent?.constantStringLength(name)
        fun constantStringIdentity(name: String): String? = if (name in values) stringIdentities[name] else parent?.constantStringIdentity(name)
        fun constantBoolean(name: String): Boolean? = if (name in values) booleanConstants[name] else parent?.constantBoolean(name)
        fun constantComplex(name: String): ConstantComplexValue? = if (name in values) complexConstants[name] else parent?.constantComplex(name)
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
        private val predeclaredIntType = NamedGoType("#predeclared-int")
        private val predeclaredInt8Type = NamedGoType("#predeclared-int8")
        private val predeclaredInt16Type = NamedGoType("#predeclared-int16")
        private val predeclaredInt32Type = NamedGoType("#predeclared-int32")
        private val predeclaredInt64Type = NamedGoType("#predeclared-int64")
        private val predeclaredUintType = NamedGoType("#predeclared-uint")
        private val predeclaredUint8Type = NamedGoType("#predeclared-uint8")
        private val predeclaredUint16Type = NamedGoType("#predeclared-uint16")
        private val predeclaredErrorType = NamedGoType("#predeclared-error")
        private val predeclaredBoolType = NamedGoType("#predeclared-bool")
        private val predeclaredFloat32Type = NamedGoType("#predeclared-float32")
        private val predeclaredFloat64Type = NamedGoType("#predeclared-float64")
        private val predeclaredStringType = NamedGoType("#predeclared-string")
        private val predeclaredComplex64Type = NamedGoType("#predeclared-complex64")
        private val predeclaredComplex128Type = NamedGoType("#predeclared-complex128")
        private val predeclaredUint32Type = NamedGoType("#predeclared-uint32")
        private val predeclaredUint64Type = NamedGoType("#predeclared-uint64")
        private val predeclaredUintptrType = NamedGoType("#predeclared-uintptr")
        private val byteType = predeclaredUint8Type
        private val runeType = NamedGoType("rune")
        private val boolType = NamedGoType("bool")
        private val stringType = NamedGoType("string")
        private val errorInterfaceType = InterfaceGoType(listOf(InterfaceMethodSyntax("Error", emptyList(), listOf(predeclaredStringType))))
        private val integerNames = setOf("#predeclared-int", "#predeclared-int8", "#predeclared-int16", "#predeclared-int32", "#predeclared-int64", "#predeclared-uint", "#predeclared-uint8", "#predeclared-uint16", "#predeclared-uint32", "#predeclared-uint64", "#predeclared-uintptr", "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune")
        private val floatNames = setOf("#predeclared-float32", "#predeclared-float64", "float32", "float64")
        private val complexNames = setOf("#predeclared-complex64", "#predeclared-complex128", "complex64", "complex128")
        private val builtinTypes = integerNames + floatNames + complexNames + setOf("bool", "string")
    }
}
