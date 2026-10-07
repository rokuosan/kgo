package kgo

import java.math.BigInteger
import java.math.BigDecimal
import java.util.IdentityHashMap
import java.util.concurrent.ConcurrentHashMap
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineExceptionHandler
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.async
import kotlinx.coroutines.cancel
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.suspendCancellableCoroutine
import kotlinx.coroutines.selects.selectUnbiased
import kotlinx.coroutines.yield
import org.apache.commons.math3.special.BesselJ
import org.apache.commons.math3.special.Erf
import org.apache.commons.math3.special.Gamma
import java.util.concurrent.atomic.AtomicInteger
import kotlin.math.abs
import kotlin.math.ceil
import kotlin.math.floor
import kotlin.math.ln
import kotlin.math.pow
import kotlin.math.sin
import kotlin.math.cos
import kotlin.math.sqrt

open class RuntimeGoError(message: String) : RuntimeException(message)

private class GoString(val bytes: ByteArray, val type: GoTypeSyntax = NamedGoType("string")) {
    override fun equals(other: Any?) = other is GoString && bytes.contentEquals(other.bytes)
    override fun hashCode() = bytes.contentHashCode()
    override fun toString() = decodeGoUtf8Text(bytes)
}

private val goChannelCoordinator = Any()

internal class GoRational private constructor(val numerator: BigInteger, val denominator: BigInteger) : Comparable<GoRational> {
    operator fun plus(other: GoRational) = of(numerator * other.denominator + other.numerator * denominator, denominator * other.denominator)
    operator fun minus(other: GoRational) = of(numerator * other.denominator - other.numerator * denominator, denominator * other.denominator)
    operator fun times(other: GoRational) = of(numerator * other.numerator, denominator * other.denominator)
    operator fun div(other: GoRational): GoRational {
        if (other.numerator.signum() == 0) throw RuntimeGoError("division by zero")
        return of(numerator * other.denominator, denominator * other.numerator)
    }
    fun negate() = of(numerator.negate(), denominator)
    fun isInteger() = denominator == BigInteger.ONE
    fun toDouble(): Double = roundedBinary(53, -1022, 1023)
    fun toFloat(): Float = roundedBinary(24, -126, 127).toFloat()
    override fun compareTo(other: GoRational): Int = (numerator * other.denominator).compareTo(other.numerator * denominator)
    override fun equals(other: Any?) = other is GoRational && numerator == other.numerator && denominator == other.denominator
    override fun hashCode() = 31 * numerator.hashCode() + denominator.hashCode()
    override fun toString() = toDouble().toString()

    companion object {
        val ZERO = GoRational(BigInteger.ZERO, BigInteger.ONE)
        private fun GoRational.roundedBinary(precision: Int, minimumExponent: Int, maximumExponent: Int): Double {
            if (numerator.signum() == 0) return 0.0
            val negative = numerator.signum() < 0
            val n = numerator.abs()
            val d = denominator
            var exponent = n.bitLength() - d.bitLength()
            val belowEstimate = if (exponent >= 0) n < d.shiftLeft(exponent) else n.shiftLeft(-exponent) < d
            if (belowEstimate) exponent--
            if (exponent > maximumExponent) return if (negative) Double.NEGATIVE_INFINITY else Double.POSITIVE_INFINITY

            val subnormal = exponent < minimumExponent
            if (subnormal && exponent < minimumExponent - 1) return if (negative) -0.0 else 0.0
            val scale = if (subnormal) precision - 1 - minimumExponent else precision - 1 - exponent
            val scaledNumerator = if (scale >= 0) n.shiftLeft(scale) else n
            val scaledDenominator = if (scale < 0) d.shiftLeft(-scale) else d
            val division = scaledNumerator.divideAndRemainder(scaledDenominator)
            var significand = division[0]
            val halfway = division[1].shiftLeft(1).compareTo(scaledDenominator)
            if (halfway > 0 || halfway == 0 && significand.testBit(0)) significand += BigInteger.ONE
            if (!subnormal && significand.bitLength() > precision) {
                significand = significand.shiftRight(1)
                exponent++
                if (exponent > maximumExponent)
                    return if (negative) Double.NEGATIVE_INFINITY else Double.POSITIVE_INFINITY
            }
            val binaryScale = if (subnormal) minimumExponent - (precision - 1) else exponent - (precision - 1)
            val value = Math.scalb(significand.toDouble(), binaryScale)
            return if (negative) -value else value
        }

        fun of(numerator: BigInteger, denominator: BigInteger = BigInteger.ONE): GoRational {
            if (denominator.signum() == 0) throw RuntimeGoError("division by zero")
            val sign = if (denominator.signum() < 0) BigInteger.ONE.negate() else BigInteger.ONE
            val n = numerator * sign
            val d = denominator.abs()
            val divisor = n.gcd(d)
            return GoRational(n / divisor, d / divisor)
        }
        fun decimal(text: String): GoRational {
            val value = BigDecimal(text)
            val scale = value.scale()
            return if (scale >= 0) of(value.unscaledValue(), BigInteger.TEN.pow(scale))
            else of(value.unscaledValue() * BigInteger.TEN.pow(-scale))
        }
    }
}

private data class GoExactComplex(val real: GoRational, val imaginary: GoRational)
private data class RuntimeImports(val packages: Map<String, String> = emptyMap(), val dotPackages: Set<String> = emptySet())
private val untypedRuneRuntimeType = NamedGoType("#untyped-rune")

/** Runtime for the currently implemented Go 1.0 execution subset. */
class Interpreter(
    private val output: (String) -> Unit = { print(it) },
    private val outputBytes: ((ByteArray) -> Unit)? = null
) {
    private val functions = mutableMapOf<String, FunctionDeclaration>()
    private val methods = mutableMapOf<String, FunctionDeclaration>()
    private val initFunctions = mutableListOf<FunctionDeclaration>()
    private val globals = Environment()
    private val elementPointers = IdentityHashMap<MutableList<Any?>, MutableMap<Int, GoPointer>>()
    private val unsafeAddressByLocation = IdentityHashMap<Any, Long>()
    private val unsafePointerByAddress = mutableMapOf<Long, GoPointer>()
    private var nextUnsafeAddress = 0x10000L
    private val typeDefinitions = ConcurrentHashMap<String, GoTypeSyntax>()
    private val localTypeIdentities = IdentityHashMap<TypeDeclaration, String>()
    private val functionImports = IdentityHashMap<FunctionDeclaration, RuntimeImports>()
    private val declarationImports = IdentityHashMap<Declaration, RuntimeImports>()
    private val nextLocalTypeIdentity = AtomicInteger()
    private var importedRuntimePackages: Map<String, Interpreter> = emptyMap()
    private var knownPackageNames: Map<String, String> = emptyMap()
    private var checkedTypeDefinitions: Map<String, GoTypeSyntax> = emptyMap()
    private var checkedFunctionTypes: Map<FunctionDeclaration, FunctionGoType> = emptyMap()
    private var exportedConstantNames: Set<String> = emptySet()
    private var exportedVariableNames: Set<String> = emptySet()
    private var exportedTypeNames: Set<String> = emptySet()
    private var packageShadowsIota = false
    private var packageIdentity: String? = null
    private var packageVariableInitializationOrder: List<VariableDeclaration>? = null
    private lateinit var goroutines: CoroutineScope

    fun run(file: GoFile) = run(listOf(file), emptyList())

    fun run(files: List<GoFile>) = run(files, emptyList())

    internal fun run(
        files: List<GoFile>,
        sourcePackages: List<GoSourcePackage>,
        rootTypeDefinitions: Map<String, GoTypeSyntax> = emptyMap(),
        importedTypeDefinitions: Map<String, Map<String, GoTypeSyntax>> = emptyMap(),
        rootFunctionTypes: Map<FunctionDeclaration, FunctionGoType> = emptyMap(),
        importedFunctionTypes: Map<String, Map<FunctionDeclaration, FunctionGoType>> = emptyMap(),
        rootVariableInitializationOrder: List<VariableDeclaration>? = null,
        importedVariableInitializationOrders: Map<String, List<VariableDeclaration>> = emptyMap()
    ) {
        if (files.isEmpty()) throw RuntimeGoError("no Go source files")
        val packageName = files.first().packageName
        if (files.any { it.packageName != packageName })
            throw RuntimeGoError("source files declare different package names")
        if (packageName != "main") throw RuntimeGoError("cannot run package $packageName: package name must be main")
        runBlocking {
            val goroutineFailure = CompletableDeferred<Throwable>()
            val failureHandler = CoroutineExceptionHandler { _, failure -> goroutineFailure.complete(failure) }
            goroutines = CoroutineScope(SupervisorJob() + Dispatchers.Default + failureHandler)
            try {
                knownPackageNames = sourcePackages.associate { it.importPath to it.packageName }
                val runtimes = linkedMapOf<String, Interpreter>()
                sourcePackages.forEach { sourcePackage ->
                    val runtime = Interpreter(output, outputBytes)
                    runtime.packageIdentity = sourcePackage.importPath
                    runtime.goroutines = goroutines
                    runtime.importedRuntimePackages = runtimes.toMap()
                    runtime.knownPackageNames = knownPackageNames
                    runtime.checkedTypeDefinitions = importedTypeDefinitions[sourcePackage.importPath].orEmpty()
                    runtime.checkedFunctionTypes = importedFunctionTypes[sourcePackage.importPath].orEmpty()
                    runtime.packageVariableInitializationOrder = importedVariableInitializationOrders[sourcePackage.importPath]
                    runtime.preparePackage(sourcePackage.files)
                    runtime.initializePackage(sourcePackage.files)
                    runtimes[sourcePackage.importPath] = runtime
                }
                importedRuntimePackages = runtimes
                checkedTypeDefinitions = rootTypeDefinitions
                checkedFunctionTypes = rootFunctionTypes
                packageVariableInitializationOrder = rootVariableInitializationOrder
                preparePackage(files)
                initializePackage(files)
                val main = functions["main"] ?: throw RuntimeGoError("main function not found")
                val mainExecution = async { invoke(main, emptyList()) }
                selectUnbiased<Unit> {
                    mainExecution.onAwait { }
                    goroutineFailure.onAwait { throw it }
                }
            } finally {
                // Go exits when main returns; it does not wait for remaining goroutines.
                goroutines.cancel()
            }
        }
    }

    private fun preparePackage(files: List<GoFile>) {
        functionImports.clear()
        declarationImports.clear()
        files.forEach { sourceFile ->
            val imports = runtimeImports(sourceFile)
            sourceFile.declarations.forEach { declaration ->
                declarationImports[declaration] = imports
                if (declaration is FunctionDeclaration) functionImports[declaration] = imports
            }
        }
    }

    private suspend fun initializePackage(files: List<GoFile>) {
        val packageName = files.first().packageName
        packageIdentity = packageIdentity ?: packageName
        val file = GoFile(packageName, files.flatMap { it.declarations })
        packageShadowsIota = file.declarations.any { declaration -> when (declaration) {
            is ConstantDeclaration -> "iota" in declaration.names
            is VariableDeclaration -> "iota" in declaration.names
            is TypeDeclaration -> declaration.name == "iota"
            is FunctionDeclaration -> declaration.receiver == null && declaration.name == "iota"
            else -> false
        } }
        file.declarations.filterIsInstance<FunctionDeclaration>().forEach { function ->
            if (function.name != "_") {
                if (function.receiver != null) methods[methodKey(function.receiver.type, function.name)] = function
                else if (function.name == "init") initFunctions += function
                else functions[function.name] = function
            }
        }
        file.declarations.filterIsInstance<TypeDeclaration>().forEach {
            if (it.name != "_") {
                val typeScope = globals.child().also { scope ->
                    scope.imports = declarationImports[it] ?: RuntimeImports()
                }
                typeDefinitions[it.name] = checkedTypeDefinitions[it.name] ?: resolveRuntimeType(it.type, typeScope)
                globals.defineType(it.name, NamedGoType(it.name))
            }
        }
        val packageConstants = file.declarations.filterIsInstance<ConstantDeclaration>()
        val packageVariables = file.declarations.filterIsInstance<VariableDeclaration>()
        exportedTypeNames = file.declarations.filterIsInstance<TypeDeclaration>().mapNotNullTo(mutableSetOf()) {
            it.name.takeIf { name -> name != "_" && GoUnicode6.isExportedIdentifier(name) }
        }
        exportedConstantNames = packageConstants.flatMap { it.names }.filterTo(mutableSetOf()) {
            it != "_" && GoUnicode6.isExportedIdentifier(it)
        }
        exportedVariableNames = packageVariables.flatMap { it.names }.filterTo(mutableSetOf()) {
            it != "_" && GoUnicode6.isExportedIdentifier(it)
        }
        packageConstants.forEach { declaration -> declaration.names.filter { it != "_" }.forEach { name -> globals.define(name, null, declaration.type) } }
        packageVariables.forEach { declaration -> declaration.names.filter { it != "_" }.forEach { name ->
            globals.define(name, declaration.type?.let(::zeroValue), declaration.type)
        } }
        orderPackageDeclarations(packageConstants, { it.names }, { it.values }, includeFunctionDependencies = false)
            .forEach { declaration ->
                globals.imports = declarationImports[declaration] ?: RuntimeImports()
                initializeConstant(declaration)
            }
        (packageVariableInitializationOrder ?: orderPackageDeclarations(
            packageVariables, { it.names }, { it.values }, includeFunctionDependencies = true
        ))
            .forEach { declaration ->
                globals.imports = declarationImports[declaration] ?: RuntimeImports()
                initialize(declaration.names, declaration.values, globals, declaration.type)
            }
        initFunctions.forEach { invoke(it, emptyList()) }
    }

    private fun runtimeImports(file: GoFile): RuntimeImports {
        val packages = linkedMapOf<String, String>()
        val dotPackages = linkedSetOf<String>()
        file.importBindings(knownPackageNames).forEach { binding ->
            val spec = binding.specification
            val path = binding.path
            when (spec.alias) {
                "." -> dotPackages += path
                "_" -> Unit
                else -> {
                    packages[binding.alias] = path
                }
            }
        }
        return RuntimeImports(packages, dotPackages)
    }

    private fun exportedFunction(name: String): FunctionValue? {
        if (!GoUnicode6.isExportedIdentifier(name)) return null
        val function = functions[name]?.takeIf { it.receiver == null } ?: return null
        val importPath = packageIdentity ?: return FunctionValue(function, globals, owner = this)
        val signature = externalizeRuntimeType(checkedFunctionType(function), importPath) as FunctionGoType
        return FunctionValue(function, globals, signature, this)
    }

    private fun checkedFunctionType(function: FunctionDeclaration): FunctionGoType = checkedFunctionTypes[function]
        ?: FunctionGoType(function.parameterTypes.mapIndexed { index, type ->
            ParameterSyntax(function.parameters.getOrNull(index), type,
                function.variadic && index == function.parameterTypes.lastIndex)
        }, function.resultTypes)

    private fun exportedConstant(name: String): Any? =
        if (name in exportedConstantNames) globals.getOrNull(name) else null

    private fun exportedVariable(name: String): Any? =
        if (name in exportedVariableNames) globals.getOrNull(name) else null

    private fun exportedIdentifierType(name: String): GoTypeSyntax? {
        if (name !in exportedConstantNames && name !in exportedVariableNames) return null
        val type = globals.typeOf(name) ?: runtimeType(globals.getOrNull(name)) ?: return null
        return packageIdentity?.let { externalizeRuntimeType(type, it) } ?: type
    }

    private fun importedExportedValue(path: String, name: String, value: Any?): Any? {
        val owner = importedRuntimePackages[path] ?: return value
        val type = owner.exportedIdentifierType(name) ?: return value
        return externalizeImportedResult(value, type, owner)
    }

    private fun exportedVariableTarget(name: String): RuntimeTarget? = if (name in exportedVariableNames) {
        val type = globals.typeOf(name)
        val externalType = if (type != null && packageIdentity != null)
            externalizeRuntimeType(type, packageIdentity!!) else type
        RuntimeTarget({ globals.get(name) }, { globals.set(name, it) }, externalType)
    } else null

    private fun exportedVariablePointer(name: String): GoPointer? {
        if (name !in exportedVariableNames) return null
        val pointer = globals.pointer(name)
        val type = globals.typeOf(name) ?: runtimeType(pointer.get()) ?: return pointer
        val externalType = packageIdentity?.let { externalizeRuntimeType(type, it) } ?: type
        return pointer.retype(externalType)
    }

    private fun methodDeclaration(type: GoTypeSyntax, name: String): Pair<Interpreter, FunctionDeclaration>? {
        methods[methodKey(type, name)]?.let { return this to it }
        val base = (type as? PointerGoType)?.element ?: type
        if (base is QualifiedGoType) {
            if (!GoUnicode6.isExportedIdentifier(name) && packageIdentity != base.packageName) return null
            val owner = importedRuntimePackages[base.packageName] ?: return null
            owner.methods[owner.methodKey(NamedGoType(base.name), name)]?.let { return owner to it }
        }
        return null
    }

    private suspend fun invoke(
        function: FunctionDeclaration,
        arguments: List<Any?>,
        receiver: Any? = null,
        parent: Environment = globals,
        expandedVariadic: Boolean = false,
        panicState: PanicState = parent.panicState,
        deferredCall: Boolean = false
    ): List<Any?> {
        val signature = checkedFunctionType(function)
        val priorActivePanic = panicState.activePanic
        val fixedCount = if (function.variadic) function.parameters.size - 1 else function.parameters.size
        if ((!function.variadic && arguments.size != fixedCount) ||
            (function.variadic && (arguments.size < fixedCount || (expandedVariadic && arguments.size != function.parameters.size)))) {
            throw RuntimeGoError("${function.name} has incompatible argument count: ${arguments.size}")
        }
        val boundArguments = if (!function.variadic || expandedVariadic) arguments else {
            val sliceType = signature.parameters.lastOrNull()?.type as? SliceGoType
                ?: throw RuntimeGoError("invalid variadic function signature")
            val extras = arguments.drop(fixedCount)
            arguments.take(fixedCount) + GoSlice(sliceType.element, extras.mapTo(mutableListOf(), ::copyValue), 0, extras.size, extras.size,
                type = sliceType)
        }
        val body = function.body ?: throw RuntimeGoError("function ${function.name} has no Go body")
        val env = Environment(
            parent,
            panicState = panicState,
            imports = functionImports[function] ?: parent.imports
        )
        function.receiver?.let { env.define(it.name ?: "", copyForType(receiver, it.type), it.type) }
        function.parameters.zip(boundArguments).forEachIndexed { i, (name, value) ->
            name?.let { parameterName ->
                val type = signature.parameters.getOrNull(i)?.type
                env.define(parameterName, type?.let { copyForType(value, it) } ?: value, type)
            }
        }
        val resultNames = function.resultNames.ifEmpty { List(signature.results.size) { null } }
        resultNames.forEachIndexed { index, name ->
            if (name != null && name != "_") env.define(name, zeroValue(signature.results[index]), signature.results[index])
        }
        val priorRecoverAllowed = panicState.recoverAllowed
        val deferredRecoverAllowed = deferredCall && priorRecoverAllowed
        panicState.recoverAllowed = deferredRecoverAllowed
        var defersRun = false
        return try {
            executeBlock(body, env, createScope = false)
            emptyList()
        } catch (returned: ReturnSignal) {
            if (returned.values.size == signature.results.size) {
                returned.values.forEachIndexed { i, value ->
                    val name = resultNames.getOrNull(i)
                    val normalized = if (returned.runeConstants.getOrNull(i) == true &&
                        underlying(signature.results[i]) is InterfaceGoType) asRuneValue(value) else value
                    if (name != null && name != "_") env.set(name, normalized)
                }
            }
            defersRun = true
            env.runDefers(deferredRecoverAllowed)
            val values = when {
                returned.values.isEmpty() && resultNames.isNotEmpty() && resultNames.all { it != null } ->
                    resultNames.mapIndexed { i, name ->
                        if (name == "_") zeroValue(signature.results[i]) else env.get(name!!)
                    }
                returned.values.size == signature.results.size -> returned.values.mapIndexed { i, value ->
                    val name = resultNames.getOrNull(i)
                    val normalized = if (returned.runeConstants.getOrNull(i) == true &&
                        underlying(signature.results[i]) is InterfaceGoType) asRuneValue(value) else value
                    if (name != null && name != "_") env.get(name)
                    else copyForType(normalized, signature.results[i])
                }
                else -> returned.values
            }
            values.mapIndexed { i, value -> signature.results.getOrNull(i)?.let { type ->
                val normalized = if (returned.runeConstants.getOrNull(i) == true && underlying(type) is InterfaceGoType)
                    asRuneValue(value) else value
                copyForType(normalized, type)
            } ?: value }
        } catch (panic: PanicSignal) {
            panicState.activePanic = panic
            defersRun = true
            env.runDefers(allowRecover = true)
            if (panic.recovered) recoveredResultValues(function, resultNames, env) else throw panic
        } catch (failure: RuntimeGoError) {
            val message = failure.message ?: "runtime panic"
            val panic = PanicSignal(GoRuntimeErrorValue(message), message)
            panicState.activePanic = panic
            defersRun = true
            env.runDefers(allowRecover = true)
            if (panic.recovered) recoveredResultValues(function, resultNames, env) else throw panic
        } finally {
            try {
                if (!defersRun && currentCoroutineContext().isActive)
                    env.runDefers(deferredRecoverAllowed)
            } finally {
                if (panicState.activePanic == null && priorActivePanic != null && !priorActivePanic.recovered)
                    panicState.activePanic = priorActivePanic
                panicState.recoverAllowed = priorRecoverAllowed
            }
        }
    }

    private fun recoveredResultValues(
        function: FunctionDeclaration,
        resultNames: List<String?>,
        env: Environment
    ): List<Any?> = checkedFunctionType(function).results.mapIndexed { index, type ->
        val name = resultNames.getOrNull(index)
        val value = if (name != null && name != "_") env.get(name) else zeroValue(type)
        copyForType(value, type)
    }

    private suspend fun executeBlock(block: BlockStatement, parent: Environment, createScope: Boolean = true) {
        val env = if (createScope) parent.child() else parent
        executeStatementList(block.statements, env)
    }

    private suspend fun executeStatementList(statements: List<Statement>, env: Environment) {
        var index = 0
        while (index < statements.size) {
            yield()
            try {
                execute(statements[index], env)
                index++
            } catch (jump: GotoSignal) {
                val target = statements.indexOfFirst { hasLeadingLabel(it, jump.label) }
                if (target < 0) throw jump
                env.clearLocalTypes()
                predeclareTypes(statements.take(target), env)
                index = target
            }
        }
    }

    private fun hasLeadingLabel(statement: Statement, label: String): Boolean = when (statement) {
        is LabeledStatement -> statement.label == label || hasLeadingLabel(statement.statement, label)
        else -> false
    }

    private fun predeclareTypes(statements: List<Statement>, env: Environment) {
        fun predeclare(statement: Statement) {
            when (statement) {
                is DeclarationStatement -> statement.declarations.filterIsInstance<TypeDeclaration>()
                    .forEach { defineLocalType(it, env) }
                is LabeledStatement -> predeclare(statement.statement)
                else -> Unit
            }
        }
        statements.forEach(::predeclare)
    }

    private suspend fun execute(statement: Statement, env: Environment, labels: Set<String> = emptySet()) {
        when (statement) {
            EmptyStatement -> Unit
            is LabeledStatement -> execute(statement.statement, env, labels + statement.label)
            is DeclarationStatement -> statement.declarations.forEach { declaration ->
                when (declaration) {
                    is VariableDeclaration -> initialize(declaration.names, declaration.values, env, declaration.type)
                    is ConstantDeclaration -> initializeConstantIn(declaration, env)
                    is TypeDeclaration -> defineLocalType(declaration, env)
                    else -> throw RuntimeGoError("unsupported local declaration")
                }
            }
            is BlockStatement -> executeBlock(statement, env)
            is VariableStatement -> initialize(statement.names, statement.values, env, statement.type)
            is ReturnStatement -> {
                val evaluated = statement.values.map { copyValue(evaluate(it, env)) }
                val values = if (statement.values.size == 1 && evaluated.singleOrNull() is GoMultiValue)
                    (evaluated.single() as GoMultiValue).values else evaluated
                val runeConstants = if (values.size == statement.values.size) statement.values.mapIndexed { index, expression ->
                    values.getOrNull(index) is BigInteger && isRuneConstantExpression(expression, env)
                } else List(values.size) { false }
                throw ReturnSignal(values, runeConstants)
            }
            is ExpressionStatement -> evaluate(statement.expression, env)
            is AssignmentStatement -> assign(statement, env)
            is IfStatement -> {
                val scope = env.child()
                statement.init?.let { execute(it, scope) }
                if (truth(evaluate(statement.condition, scope))) executeBlock(statement.thenBranch, scope)
                else statement.elseBranch?.let { execute(it, scope) }
            }
            is ForStatement -> {
                val scope = env.child()
                if (statement.rangeClause != null) {
                    executeRange(statement.rangeClause, statement.body, scope, labels)
                } else {
                    statement.init?.let { execute(it, scope) }
                    while (statement.condition == null || truth(evaluate(statement.condition, scope))) {
                        yield()
                        try { executeBlock(statement.body, scope) }
                        catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                        catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                        statement.post?.let { execute(it, scope) }
                    }
                }
            }
            is IncrementStatement -> {
                val target = resolveTarget(statement.target, env)
                val old = target.get()
                val operator = if (statement.delta > 0) TokenKind.ADD else TokenKind.SUB
                target.set(binary(old, operator, 1L))
            }
            is SendStatement -> {
                val channel = evaluate(statement.channel, env)
                val value = evaluate(statement.value, env)
                when (channel) {
                    is GoChannel -> channel.send(
                        if (underlying(channel.elementType) is InterfaceGoType)
                            defaultRuneValue(value, statement.value, env) else value
                    )
                    is GoNilValue -> if (underlying(channel.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("send on non-channel")
                    else -> throw RuntimeGoError("send on non-channel")
                }
            }
            is GoStatement -> {
                val call = statement.call.unparenthesized() as? CallExpression
                    ?: throw RuntimeGoError("go statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = adaptCallArguments(call, target, evaluateCallArguments(call, env), env)
                goroutines.launch { call(target, arguments, call.expandLastArgument, PanicState(), environment = env) }
            }
            is DeferStatement -> {
                val call = statement.call.unparenthesized() as? CallExpression
                    ?: throw RuntimeGoError("defer statement requires a function call")
                val target = evaluate(call.function, env)
                val arguments = adaptCallArguments(call, target, evaluateCallArguments(call, env), env)
                env.defer { call(target, arguments, call.expandLastArgument, env.panicState, deferredCall = true, environment = env) }
            }
            is BranchStatement -> when (statement.kind) {
                TokenKind.BREAK -> throw BreakSignal(statement.label)
                TokenKind.CONTINUE -> throw ContinueSignal(statement.label)
                TokenKind.GOTO -> throw GotoSignal(statement.label ?: throw RuntimeGoError("goto requires a label"))
                TokenKind.FALLTHROUGH -> throw FallthroughSignal()
                else -> throw RuntimeGoError("invalid branch statement")
            }
            is SelectStatement -> executeSelect(statement, env, labels)
            is SwitchStatement -> executeSwitch(statement, env, labels)
            is TypeSwitchStatement -> executeTypeSwitch(statement, env, labels)
        }
    }

    private fun targets(label: String?, labels: Set<String>) = label == null || label in labels

    private suspend fun assign(statement: AssignmentStatement, env: Environment) {
        if (statement.operator == TokenKind.DEFINE) {
            val values = expandValues(evaluateRhs(statement.values, statement.targets.size, env), statement.targets.size)
            assignValues(statement.targets, statement.operator, values, env, statement.values)
        } else {
            // Go 1 evaluates all left-hand index/pointer operands before the right-hand expressions,
            // then performs writes left-to-right. Resolve every target before evaluating the RHS.
            val locations = statement.targets.map { resolveTarget(it, env) }
            val previous = if (statement.operator == TokenKind.ASSIGN) emptyList() else locations.map { it.get() }
            val values = expandValues(evaluateRhs(statement.values, statement.targets.size, env), statement.targets.size)
            assignToLocations(locations, statement.operator, assignedValues(locations, values, statement.values, env), previous)
        }
    }

    private suspend fun assignValues(
        targets: List<Expression>,
        operator: TokenKind,
        values: List<Any?>,
        env: Environment,
        sourceExpressions: List<Expression>? = null,
        declaredTypes: List<GoTypeSyntax>? = null
    ) {
        if (operator == TokenKind.DEFINE) {
            val names = targets.map { (it as? NameExpression)?.name ?: throw RuntimeGoError("short declaration targets must be names") }
            if (names.size != values.size) throw RuntimeGoError("assignment count mismatch")
            val declared = mutableSetOf<String>()
            names.zip(values).forEachIndexed { index, (name, value) ->
                if (name == "_") return@forEachIndexed
                if (!declared.add(name)) throw RuntimeGoError("$name repeated on left side of :=")
                if (env.containsLocalType(name)) throw RuntimeGoError("$name redeclared in this block")
                val initialized = defaultConstantValue(value, sourceExpressions?.getOrNull(index), env)
                if (env.containsLocal(name)) env.set(name, initialized)
                else env.define(name, initialized, declaredTypes?.getOrNull(index) ?: inferredStorageType(
                    initialized, sourceExpressions?.getOrNull(index), env,
                    if (sourceExpressions?.size == 1) index else 0
                ))
            }
            return
        }
        if (targets.size != values.size) throw RuntimeGoError("assignment count mismatch")
        val locations = targets.map { resolveTarget(it, env) }
        assignToLocations(locations, operator, assignedValues(locations, values, sourceExpressions, env),
            if (operator == TokenKind.ASSIGN) emptyList() else locations.map { it.get() })
    }

    private fun assignedValues(
        locations: List<RuntimeTarget>,
        values: List<Any?>,
        sourceExpressions: List<Expression>?,
        env: Environment
    ): List<Any?> = values.mapIndexed { index, value ->
        val sharedExpression = sourceExpressions?.singleOrNull()?.takeIf { values.size > 1 }
        locations[index].type?.let { type ->
            boxInterfaceAssignment(
                value, type, sourceExpressions?.getOrNull(index) ?: sharedExpression, env,
                if (sharedExpression != null) index else 0
            )
        } ?: value
    }

    private fun boxInterfaceAssignment(
        value: Any?, targetType: GoTypeSyntax, expression: Expression?, env: Environment, resultIndex: Int = 0
    ): Any? {
        if (underlying(targetType) !is InterfaceGoType) return value
        val normalized = defaultRuneValue(value, expression, env)
        if (normalized == null || normalized is GoInterfaceValue) return normalized
        val sourceType = expression?.let {
            (staticExpressionResultType(it, resultIndex, env) ?: staticExpressionType(it, env))
                .let { type -> type?.let { resolveRuntimeType(it, env) } }
        }
        val dynamicType = sourceType?.takeUnless { it is NamedGoType && it.name.startsWith("#untyped-") }
            ?: runtimeType(normalized) ?: return normalized
        return boxInterfaceValue(normalized, dynamicType)
    }

    private fun assignToLocations(
        locations: List<RuntimeTarget>,
        operator: TokenKind,
        values: List<Any?>,
        previous: List<Any?> = emptyList()
    ) {
        if (locations.size != values.size) throw RuntimeGoError("assignment count mismatch")
        locations.indices.forEach { i ->
            val value = if (operator == TokenKind.ASSIGN) values[i] else binary(previous[i], compoundOperator(operator), values[i])
            locations[i].set(value)
        }
    }

    private suspend fun resolveTarget(target: Expression, env: Environment): RuntimeTarget = when (target) {
        is ParenthesizedExpression -> resolveTarget(target.expression, env)
        is NameExpression -> if (target.name == "_") RuntimeTarget({ null }, {})
            else env.imports.dotPackages.firstNotNullOfOrNull { path ->
                importedRuntimePackages[path]?.exportedVariableTarget(target.name)
            } ?: RuntimeTarget({ env.get(target.name) }, { env.set(target.name, it) }, env.typeOf(target.name))
        is IndexExpression -> {
            val receiver = evaluateAssignmentReceiver(target.receiver, env)
            val key = evaluate(target.index, env)
            when (receiver) {
                is GoSlice -> {
                    fun index() = collectionIndex(key, "index")
                    RuntimeTarget({ receiver.get(index()) }, { receiver.set(index(), it) }, receiver.elementType)
                }
                is GoArray -> {
                    fun index() = collectionIndex(key, "index").toLong()
                    RuntimeTarget({ arrayElement(receiver, index()) }, { setArrayElement(receiver, index(), it) }, receiver.elementType)
                }
                is GoPointer -> {
                    fun index() = collectionIndex(key, "index").toLong()
                    RuntimeTarget({
                        val array = pointedArray(receiver)
                        arrayElement(array, index())
                    }, {
                        val array = pointedArray(receiver)
                        setArrayElement(array, index(), it)
                    }, (receiver.pointeeType?.let { underlying(it) as? ArrayGoType })?.element ?: staticExpressionType(target, env))
                }
                is GoMap -> {
                    RuntimeTarget(
                        {
                            val mapIndex = if (underlying(receiver.keyType) is InterfaceGoType)
                                defaultRuneValue(key, target.index, env) else key
                            mapValue(receiver, mapKey(mapIndex, receiver.keyType))
                        },
                        {
                            val mapIndex = if (underlying(receiver.keyType) is InterfaceGoType)
                                defaultRuneValue(key, target.index, env) else key
                            receiver.values[mapKey(mapIndex, receiver.keyType)] = copyForType(it, receiver.valueType)
                        },
                        receiver.valueType
                    )
                }
                is GoNilValue -> {
                    val mapType = underlying(receiver.type) as? MapGoType
                        ?: throw RuntimeGoError("cannot assign through index")
                    RuntimeTarget({ zeroValue(mapType.value) }, {
                        val mapIndex = if (underlying(mapType.key) is InterfaceGoType)
                            defaultRuneValue(key, target.index, env) else key
                        mapKey(mapIndex, mapType.key)
                        throw RuntimeGoError("assignment to entry in nil map")
                    }, mapType.value)
                }
                else -> throw RuntimeGoError("cannot assign through index")
            }
        }
        is SelectorExpression -> {
            if (target.receiver is NameExpression && !env.contains(target.receiver.name)) {
                val path = env.imports.packages[target.receiver.name]
                if (path != null) importedRuntimePackages[path]?.exportedVariableTarget(target.field)?.let { return it }
            }
            val receiver = evaluateAssignmentReceiver(target.receiver, env)
            val type = staticExpressionType(target, env)
            RuntimeTarget(
                { pointerToStructField(receiver, target.field).get() },
                { value ->
                    val field = pointerToStructField(receiver, target.field)
                    field.set(copyForType(value, field.pointeeType ?: type ?: runtimeType(field.get()) ?: NamedGoType("<unknown>")))
                },
                type
            )
        }
        is UnaryExpression -> {
            if (target.operator != TokenKind.MUL) throw RuntimeGoError("invalid assignment target")
            val pointerValue = evaluate(target.operand, env)
            val type = staticExpressionType(target, env)
            fun pointer() = pointerValue as? GoPointer ?: throw RuntimeGoError("dereference of non-pointer")
            RuntimeTarget({ pointer().get() }, { value ->
                val resolved = pointer()
                resolved.set(copyForType(value, resolved.pointeeType ?: type ?: runtimeType(resolved.get()) ?: NamedGoType("<unknown>")))
            }, type)
        }
        else -> throw RuntimeGoError("invalid assignment target")
    }

    private suspend fun evaluateAssignmentReceiver(expression: Expression, env: Environment): Any? {
        val dereference = expression.unparenthesized() as? UnaryExpression
        return if (dereference?.operator == TokenKind.MUL) evaluate(dereference.operand, env)
        else evaluate(expression, env)
    }

    private fun pointedArray(pointer: GoPointer): GoArray {
        var value: Any? = pointer
        while (value is GoPointer) value = value.get()
        return value as? GoArray ?: throw RuntimeGoError("index requires pointer to array")
    }

    private suspend fun executeSelect(statement: SelectStatement, env: Environment, labels: Set<String>) {
        val operations = statement.cases.mapIndexedNotNull { caseIndex, clause ->
            when (val communication = clause.communication) {
                null -> null
                is SendStatement -> {
                    val channelValue = evaluate(communication.channel, env)
                    val sendValue = evaluate(communication.value, env)
                    val channel = selectChannelOrNull(channelValue) ?: return@mapIndexedNotNull null
                    val value = if (underlying(channel.elementType) is InterfaceGoType)
                        defaultRuneValue(sendValue, communication.value, env) else sendValue
                    SelectSend(caseIndex, channel, copyForType(value, channel.elementType))
                }
                is ExpressionStatement -> {
                    val receive = communication.expression.unparenthesized() as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("invalid select receive clause")
                    val channel = selectChannelOrNull(evaluate(receive.operand, env)) ?: return@mapIndexedNotNull null
                    SelectReceive(caseIndex, channel, null)
                }
                is AssignmentStatement -> {
                    val receive = communication.values.singleOrNull()?.unparenthesized() as? UnaryExpression
                    if (receive?.operator != TokenKind.ARROW) throw RuntimeGoError("select assignment must receive from a channel")
                    val channel = selectChannelOrNull(evaluate(receive.operand, env)) ?: return@mapIndexedNotNull null
                    SelectReceive(caseIndex, channel, communication)
                }
                else -> throw RuntimeGoError("invalid select communication clause")
            }
        }
        val defaultIndex = statement.cases.indexOfFirst { it.communication == null }
        val selected = awaitChannelSelect(operations, defaultIndex)
        selected.failure?.let { throw it }
        val receive = operations.filterIsInstance<SelectReceive>().firstOrNull { it.caseIndex == selected.caseIndex }
        executeSelectedCase(statement.cases[selected.caseIndex], env, labels, receive?.assignment,
            selected.received, receive?.channel?.elementType)
    }

    private suspend fun awaitChannelSelect(
        operations: List<SelectOperation>,
        defaultIndex: Int
    ): SelectSelection {
        if (operations.isEmpty() && defaultIndex < 0) awaitCancellation()
        return suspendCancellableCoroutine { continuation ->
            val decision = ChannelDecision { continuation.resumeWith(Result.success(it)) }
            continuation.invokeOnCancellation { decision.cancel() }
            val completions = mutableListOf<() -> Unit>()
            synchronized(goChannelCoordinator) {
                if (!continuation.isActive) return@synchronized
                operations.shuffled().forEach { operation ->
                    if (decision.selected) return@forEach
                    val element = (operation as? SelectSend)?.let {
                        GoChannelElement(copyForType(it.value, it.channel.elementType))
                    }
                    operation.channel.register(
                        ChannelWaiter(operation.channel, decision, operation.caseIndex, element),
                        enqueue = defaultIndex < 0,
                        completions
                    )
                }
                if (!decision.selected && defaultIndex >= 0)
                    decision.claim(defaultIndex, null, null, completions)
            }
            completions.forEach { it() }
        }
    }

    private fun selectChannelOrNull(value: Any?): GoChannel? = when (value) {
        is GoChannel -> value
        is GoNilValue -> if (underlying(value.type) is ChannelGoType) null else throw RuntimeGoError("select operation requires a channel")
        else -> throw RuntimeGoError("select operation requires a channel")
    }

    private suspend fun executeSelectedCase(
        clause: SelectCase,
        parent: Environment,
        labels: Set<String>,
        assignment: AssignmentStatement? = null,
        received: GoReceiveResult? = null,
        receiveElementType: GoTypeSyntax? = null
    ) {
        val env = parent.child()
        if (assignment != null && received != null) {
            val declaredTypes = if (assignment.operator == TokenKind.DEFINE && receiveElementType != null)
                listOf(receiveElementType) + if (assignment.targets.size > 1) listOf(NamedGoType("bool")) else emptyList()
            else null
            assignValues(assignment.targets, assignment.operator,
                expandValues(listOf(received), assignment.targets.size), env, declaredTypes = declaredTypes)
        }
        try { executeStatementList(clause.statements, env) }
        catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal }
    }

    private suspend fun executeSwitch(statement: SwitchStatement, env: Environment, labels: Set<String>) {
        val scope = env.child()
        statement.init?.let { execute(it, scope) }
        val tag = statement.tag?.let { copyValue(evaluate(it, scope)) } ?: if (statement.tag == null) true else null
        var selected = -1
        for ((clauseIndex, clause) in statement.clauses.withIndex()) {
            if (clause.expressions?.any { expression ->
                    val caseValue = copyValue(evaluate(expression, scope))
                    val (comparedCase, comparedTag) = interfaceComparisonOperands(
                        expression, caseValue, statement.tag, tag, scope
                    )
                    goEqual(comparedCase, comparedTag)
                } == true) {
                selected = clauseIndex
                break
            }
        }
        if (selected < 0) selected = statement.clauses.indexOfFirst { it.expressions == null }
        if (selected < 0) return
        var index = selected
        while (index < statement.clauses.size) {
            try {
                val caseScope = scope.child()
                executeStatementList(statement.clauses[index].statements, caseScope)
                return
            } catch (_: FallthroughSignal) {
                if (index == statement.clauses.lastIndex) throw RuntimeGoError("fallthrough in final switch clause")
                index++
            } catch (signal: BreakSignal) {
                if (!targets(signal.label, labels)) throw signal
                return
            }
        }
    }

    private suspend fun executeTypeSwitch(statement: TypeSwitchStatement, env: Environment, labels: Set<String>) {
        val scope = env.child()
        statement.init?.let { execute(it, scope) }
        val value = copyValue(evaluate(statement.guard.expression, scope))
        val dynamicType = (value as? GoInterfaceValue)?.dynamicType
        val resolvedClauses = statement.clauses.map { clause ->
            clause.types?.map { resolveRuntimeType(it, scope) }
        }
        val selected = statement.clauses.indices.firstOrNull { clauseIndex ->
            resolvedClauses[clauseIndex]?.any { type ->
                if (type == NamedGoType("nil")) value == null
                else dynamicType != null && matchesDynamicType(dynamicType, type)
            } == true
        } ?: statement.clauses.indexOfFirst { clause -> clause.types == null }
        if (selected < 0) return
        val clause = statement.clauses[selected]
        val singleType = resolvedClauses[selected]?.singleOrNull()?.takeUnless { it == NamedGoType("nil") }
        val caseValue = when {
            singleType == null -> value
            underlying(singleType) is InterfaceGoType -> value
            else -> (value as? GoInterfaceValue)?.value
        }
        val caseScope = scope.child()
        if (statement.guard.name != null && statement.guard.name != "_")
            caseScope.define(statement.guard.name, caseValue, singleType ?: interfaceOperandType(statement.guard.expression, scope))
        try {
            executeStatementList(clause.statements, caseScope)
        } catch (signal: BreakSignal) {
            if (!targets(signal.label, labels)) throw signal
        } catch (_: FallthroughSignal) {
            throw RuntimeGoError("fallthrough in type switch")
        }
    }

    private fun matchesDynamicType(dynamicType: GoTypeSyntax, target: GoTypeSyntax): Boolean {
        val interfaceType = underlying(target) as? InterfaceGoType
        return if (interfaceType != null) implementsInterface(dynamicType, interfaceType) else sameRuntimeType(dynamicType, target)
    }

    private fun sameRuntimeType(left: GoTypeSyntax, right: GoTypeSyntax): Boolean {
        val a = canonicalAliasType(left)
        val b = canonicalAliasType(right)
        if (a == b && !containsStructLiteral(a)) return true
        return when {
            a is PointerGoType && b is PointerGoType -> sameRuntimeType(a.element, b.element)
            a is SliceGoType && b is SliceGoType -> sameRuntimeType(a.element, b.element)
            a is ArrayGoType && b is ArrayGoType ->
                sameRuntimeArrayLength(a.length, b.length) && sameRuntimeType(a.element, b.element)
            a is MapGoType && b is MapGoType ->
                sameRuntimeType(a.key, b.key) && sameRuntimeType(a.value, b.value)
            a is ChannelGoType && b is ChannelGoType ->
                a.direction == b.direction && sameRuntimeType(a.element, b.element)
            a is StructGoType && b is StructGoType -> {
                val leftFields = a.fields.flatMap { field ->
                    field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                        .map { name -> Triple(name, unexportedFieldPackagePath(field, name), field.type to field.tag.orEmpty()) }
                }
                val rightFields = b.fields.flatMap { field ->
                    field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                        .map { name -> Triple(name, unexportedFieldPackagePath(field, name), field.type to field.tag.orEmpty()) }
                }
                leftFields.size == rightFields.size && leftFields.zip(rightFields).all { (leftField, rightField) ->
                    leftField.first == rightField.first && leftField.second == rightField.second &&
                        leftField.third.second == rightField.third.second &&
                        sameRuntimeType(leftField.third.first, rightField.third.first)
                }
            }
            a is InterfaceGoType && b is InterfaceGoType -> {
                val leftMethods = interfaceMethodsRuntime(a)
                val rightMethods = interfaceMethodsRuntime(b)
                leftMethods.keys == rightMethods.keys && leftMethods.all { (name, signature) ->
                    rightMethods[name]?.let { sameFunctionType(signature, it) } == true
                }
            }
            a is FunctionGoType && b is FunctionGoType -> sameFunctionType(a, b)
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

    private fun sameRuntimeArrayLength(left: Expression?, right: Expression?): Boolean {
        if (left == null || right == null) return left == right
        return runCatching { integerLiteral(left) == integerLiteral(right) }.getOrDefault(false)
    }

    private fun canonicalAliasType(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        NamedGoType("byte") -> if (!typeDefinitions.containsKey("byte")) predeclaredUInt8RuntimeType else type
        NamedGoType("uint8") -> if (!typeDefinitions.containsKey("uint8")) predeclaredUInt8RuntimeType else type
        NamedGoType("rune") -> if (!typeDefinitions.containsKey("rune")) predeclaredIntRuntimeType else type
        NamedGoType("int") -> if (!typeDefinitions.containsKey("int")) predeclaredIntRuntimeType else type
        is PointerGoType -> PointerGoType(canonicalAliasType(type.element))
        is SliceGoType -> SliceGoType(canonicalAliasType(type.element))
        is ArrayGoType -> ArrayGoType(type.length, canonicalAliasType(type.element))
        is MapGoType -> MapGoType(canonicalAliasType(type.key), canonicalAliasType(type.value))
        is ChannelGoType -> ChannelGoType(canonicalAliasType(type.element), type.direction)
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = canonicalAliasType(it.type)) },
            type.results.map(::canonicalAliasType)
        )
        is StructGoType -> StructGoType(type.fields.map { it.copy(type = canonicalAliasType(it.type), tag = it.tag.orEmpty()) })
        is InterfaceGoType -> InterfaceGoType(
            type.methods.map { method -> method.copy(
                parameters = method.parameters.map { it.copy(type = canonicalAliasType(it.type)) },
                results = method.results.map(::canonicalAliasType)
            ) },
            type.embeddedTypes.map(::canonicalAliasType)
        )
        else -> type
    }

    private fun interfaceOperandType(expression: Expression, env: Environment): GoTypeSyntax = when (expression) {
        is NameExpression -> env.typeOf(expression.name) ?: InterfaceGoType(emptyList())
        is ParenthesizedExpression -> interfaceOperandType(expression.expression, env)
        else -> InterfaceGoType(emptyList())
    }

    private suspend fun executeRange(range: RangeClause, body: BlockStatement, env: Environment, labels: Set<String>) {
        val onlyIndexIsUsed = range.targets.size <= 1 || range.targets.getOrNull(1).isBlankIdentifier()
        val declarationTypes = if (range.operator == TokenKind.DEFINE) rangeVariableTypes(range, env) else null
        // A := range clause declares its variables in the for statement's scope.
        // Keep that scope separate so a same-named variable in the enclosing block
        // is shadowed, and reuse the new bindings across Go 1.0 loop iterations.
        val loopEnv = if (range.operator == TokenKind.DEFINE) env.child() else env
        if (onlyIndexIsUsed && !containsCallOrReceive(range.expression, env)) {
            val arrayLength = staticRangeArrayLength(range.expression, env)
            if (arrayLength != null) {
                // A constant array length lets range skip an expression without calls or receives.
                rangeIndexed(arrayLength, range, body, loopEnv, labels, declarationTypes) { index -> listOf(index.toLong()) }
                return
            }
        }
        val evaluated = copyValue(evaluate(range.expression, env))
        val pointerToArray = (evaluated as? GoPointer)?.takeIf { pointer ->
            pointer.pointeeType?.let { underlying(it) is ArrayGoType } == true || (!pointer.isNil && pointer.get() is GoArray)
        }
        val value = if (pointerToArray == null) evaluated else pointerToArray
        when (value) {
            is GoChannel -> while (true) {
                val received = value.receive()
                if (!received.ok) break
                if (range.targets.isNotEmpty()) {
                    val values = listOf(received.value).take(range.targets.size)
                    assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, loopEnv,
                        declaredTypes = declarationTypes)
                }
                try { executeBlock(body, loopEnv) }
                catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
            }
            is GoNilValue -> when (underlying(value.type)) {
                is SliceGoType, is MapGoType -> Unit
                is ChannelGoType -> awaitCancellation()
                else -> throw RuntimeGoError("range over this value is not implemented")
            }
            is GoString -> {
                var byteIndex = 0
                while (byteIndex < value.bytes.size) {
                    yield()
                    val (cp, width) = decodeUtf8Rune(value.bytes, byteIndex)
                    if (range.targets.isNotEmpty()) {
                        val values = listOf(byteIndex.toLong(), GoInteger(cp.toLong(), predeclaredIntRuntimeType)).take(range.targets.size)
                        assignValues(range.targets, range.operator ?: TokenKind.ASSIGN, values, loopEnv,
                            declaredTypes = declarationTypes)
                    }
                    try { executeBlock(body, loopEnv) }
                    catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                    catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                    byteIndex += width
                }
            }
            is GoSlice -> rangeIndexed(value.length, range, body, loopEnv, labels, declarationTypes) { i ->
                if (onlyIndexIsUsed) listOf(i.toLong()) else listOf(i.toLong(), value.get(i))
            }
            is GoPointer -> {
                val arrayLength = staticRangeArrayLength(range.expression, env)
                    ?: if (!value.isNil) (value.get() as? GoArray)?.values?.size
                        ?: throw RuntimeGoError("range over pointer requires an array")
                    else throw RuntimeGoError("range over nil pointer requires a known array length")
                rangeIndexed(arrayLength, range, body, loopEnv, labels, declarationTypes) { index ->
                    if (onlyIndexIsUsed) listOf(index.toLong()) else {
                        val array = value.get() as? GoArray ?: throw RuntimeGoError("range over pointer requires an array")
                        listOf(index.toLong(), array.values[index])
                    }
                }
            }
            is GoArray -> rangeIndexed(value.values.size, range, body, loopEnv, labels, declarationTypes) { i ->
                if (onlyIndexIsUsed) listOf(i.toLong()) else listOf(i.toLong(), value.values[i])
            }
            is GoMap -> {
                // Go 1 leaves map iteration order unspecified. Snapshot keys, then
                // recheck membership and read values as each entry is reached so
                // deleting an unreached entry suppresses that iteration value.
                for (key in value.values.keys.toList().shuffled()) {
                    yield()
                    if (!value.values.containsKey(key)) continue
                    val entryValue = if (onlyIndexIsUsed) null else value.values[key]
                    if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN,
                        (if (onlyIndexIsUsed) listOf(copyValue(key.value)) else listOf(copyValue(key.value), entryValue))
                            .take(range.targets.size), loopEnv, declaredTypes = declarationTypes)
                    try { executeBlock(body, loopEnv) }
                    catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
                    catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
                }
            }
            else -> throw RuntimeGoError("range over this value is not implemented")
        }
    }

    private fun rangeVariableTypes(range: RangeClause, env: Environment): List<GoTypeSyntax> {
        val source = staticExpressionType(range.expression, env)?.let(::underlying) ?: return emptyList()
        val pair = when (source) {
            is ArrayGoType -> NamedGoType("int") to source.element
            is PointerGoType -> (underlying(source.element) as? ArrayGoType)?.let {
                NamedGoType("int") to it.element
            }
            is SliceGoType -> NamedGoType("int") to source.element
            is MapGoType -> source.key to source.value
            is ChannelGoType -> null to source.element
            NamedGoType("string") -> NamedGoType("int") to predeclaredIntRuntimeType
            else -> null
        } ?: return emptyList()
        return listOfNotNull(pair.first, pair.second).take(range.targets.size)
    }

    private fun Expression?.isBlankIdentifier(): Boolean = when (this) {
        is NameExpression -> name == "_"
        is ParenthesizedExpression -> expression.isBlankIdentifier()
        else -> false
    }

    private fun staticRangeArrayLength(expression: Expression, env: Environment): Int? {
        val type = staticExpressionType(expression, env) ?: return null
        val actual = underlying(type)
        val array = when (actual) {
            is ArrayGoType -> actual
            is PointerGoType -> underlying(actual.element) as? ArrayGoType
            else -> null
        } ?: return null
        val length = array.length?.let { integerLiteral(it, env).intValueExact() }
            ?: arrayCompositeLiteral(expression, env)?.let { inferredArrayLiteralLength(it, env) }
            ?: return null
        if (length < 0) throw RuntimeGoError("negative array length")
        return length
    }

    private fun pointerArrayLength(pointer: GoPointer, env: Environment?): Long {
        val arrayType = pointer.pointeeType?.let(::underlying) as? ArrayGoType
        if (arrayType != null) {
            arrayType.length?.let { return integerLiteral(it, env).longValueExact() }
        }
        if (!pointer.isNil) {
            val array = pointer.get() as? GoArray
                ?: throw RuntimeGoError("len or cap requires pointer to array")
            return array.values.size.toLong()
        }
        throw RuntimeGoError("len or cap requires pointer to array with a known length")
    }

    private fun arrayCompositeLiteral(expression: Expression, env: Environment): CompositeLiteral? = when (expression) {
        is CompositeLiteral -> expression.takeIf { underlying(resolveRuntimeType(it.type, env)) is ArrayGoType }
        is ParenthesizedExpression -> arrayCompositeLiteral(expression.expression, env)
        is UnaryExpression -> if (expression.operator == TokenKind.AND) arrayCompositeLiteral(expression.operand, env) else null
        else -> null
    }

    private fun runtimeNamedType(name: String, path: String?): GoTypeSyntax =
        path?.takeIf { it != packageIdentity }?.let { QualifiedGoType(it, name) } ?: NamedGoType(name)

    private fun inferredArrayLiteralLength(literal: CompositeLiteral, env: Environment): Int {
        var nextIndex = 0
        var largestIndex = -1
        literal.elements.forEach { element ->
            val index = element.key?.let { integerLiteral(it, env).intValueExact() } ?: nextIndex
            if (index < 0) throw RuntimeGoError("negative array index")
            largestIndex = maxOf(largestIndex, index)
            nextIndex = index + 1
        }
        return largestIndex + 1
    }

    private fun staticExpressionType(expression: Expression, env: Environment): GoTypeSyntax? = when (expression) {
        is NameExpression -> env.typeOf(expression.name) ?: functions[expression.name]?.let(::checkedFunctionType)
            ?: env.imports.dotPackages.firstNotNullOfOrNull { path ->
            importedRuntimePackages[path]?.exportedFunction(expression.name)?.function?.let { importedFunctionType(path, it) }
        }
        is ParenthesizedExpression -> staticExpressionType(expression.expression, env)
        is CompositeLiteral -> resolveRuntimeType(expression.type, env)
        is TypeAssertionExpression -> resolveRuntimeType(expression.type, env)
        is SelectorExpression -> {
            val packageAlias = (expression.receiver as? NameExpression)?.name
            val importedPath = packageAlias?.let(env.imports.packages::get)
            if (importedPath != null) {
                importedRuntimePackages[importedPath]?.exportedFunction(expression.field)?.function?.let {
                    return importedFunctionType(importedPath, it)
                }
            }
            val receiverType = staticExpressionType(expression.receiver, env)?.let { resolveRuntimeType(it, env) }
            val method = receiverType?.let { methodDeclaration(it, expression.field) }
            if (method != null) {
                val signature = method.first.checkedFunctionType(method.second)
                val importPath = method.first.packageIdentity
                if (method.first !== this && importPath != null)
                    method.first.externalizeRuntimeType(signature, importPath) as FunctionGoType
                else signature
            } else {
                val struct = receiverType?.let(::underlying).let { if (it is PointerGoType) underlying(it.element) else it }
                when (struct) {
                    is StructGoType -> staticPromotedFieldType(struct, expression.field, env)
                    is InterfaceGoType -> interfaceMethodsRuntime(struct)[runtimePackageMethodKey(expression.field)]
                    else -> null
                }
            }
        }
        is UnaryExpression -> when (expression.operator) {
            TokenKind.AND -> staticExpressionType(expression.operand, env)?.let(::PointerGoType)
            TokenKind.MUL -> (staticExpressionType(expression.operand, env)?.let(::underlying) as? PointerGoType)?.element
            else -> null
        }
        is CallExpression -> staticExpressionResultType(expression, 0, env)
        is BinaryExpression -> when (expression.operator) {
            TokenKind.EQL, TokenKind.NEQ, TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ -> NamedGoType("bool")
            TokenKind.LAND, TokenKind.LOR -> staticExpressionType(expression.left, env) ?: staticExpressionType(expression.right, env)
            else -> null
        }
        is IndexExpression -> when (val receiver = staticExpressionType(expression.receiver, env)?.let(::underlying)) {
            is ArrayGoType -> receiver.element
            is SliceGoType -> receiver.element
            is MapGoType -> receiver.value
            else -> null
        }
        else -> null
    }

    private fun importedFunctionType(path: String, function: FunctionDeclaration): FunctionGoType {
        val owner = importedRuntimePackages[path] ?: this
        return owner.externalizeRuntimeType(owner.checkedFunctionType(function), path) as FunctionGoType
    }

    private fun staticExpressionResultType(expression: Expression, resultIndex: Int, env: Environment): GoTypeSyntax? = when (expression) {
        is ParenthesizedExpression -> staticExpressionResultType(expression.expression, resultIndex, env)
        is TypeAssertionExpression -> when (resultIndex) {
            0 -> resolveRuntimeType(expression.type, env)
            1 -> NamedGoType("bool")
            else -> null
        }
        is UnaryExpression -> if (expression.operator == TokenKind.ARROW) {
            val channel = staticExpressionType(expression.operand, env)?.let(::underlying) as? ChannelGoType
            when (resultIndex) {
                0 -> channel?.element
                1 -> NamedGoType("bool")
                else -> null
            }
        } else if (resultIndex == 0) staticExpressionType(expression, env) else null
        is IndexExpression -> {
            val receiver = staticExpressionType(expression.receiver, env)?.let(::underlying)
            if (resultIndex == 1 && receiver is MapGoType) NamedGoType("bool")
            else if (resultIndex == 0) staticExpressionType(expression, env) else null
        }
        is CallExpression -> {
            val conversionType = runtimeTypeConversion(expression, env)
            if (conversionType != null) conversionType.takeIf { resultIndex == 0 }
            else {
                val functionType = when (val target = expression.function) {
                    is FunctionLiteralExpression -> FunctionGoType(target.parameters, target.results)
                    else -> staticExpressionType(target, env)?.let(::underlying) as? FunctionGoType
                }
                functionType?.results?.getOrNull(resultIndex)?.let { resolveRuntimeType(it, env) }
            }
        }
        else -> if (resultIndex == 0) staticExpressionType(expression, env) else null
    }

    private fun isNilOperand(expression: Expression, env: Environment): Boolean = when (expression) {
        is ParenthesizedExpression -> isNilOperand(expression.expression, env)
        is NameExpression -> expression.name == "nil" && !env.contains(expression.name)
        else -> false
    }

    private fun interfaceComparisonOperands(
        leftExpression: Expression?,
        leftValue: Any?,
        rightExpression: Expression?,
        rightValue: Any?,
        env: Environment
    ): Pair<Any?, Any?> {
        fun operandType(expression: Expression?, value: Any?): GoTypeSyntax? =
            expression?.let { staticExpressionType(it, env) }?.let { resolveRuntimeType(it, env) } ?: runtimeType(value)
        var left = leftValue
        var right = rightValue
        val leftType = operandType(leftExpression, leftValue)
        val rightType = operandType(rightExpression, rightValue)
        val leftIsInterface = leftType?.let { underlying(it) is InterfaceGoType } == true
        val rightIsInterface = rightType?.let { underlying(it) is InterfaceGoType } == true
        val leftIsUntypedNil = leftType == null && leftExpression?.let { isNilOperand(it, env) } == true
        val rightIsUntypedNil = rightType == null && rightExpression?.let { isNilOperand(it, env) } == true
        if (!leftIsInterface && !leftIsUntypedNil && rightIsInterface) {
            left = boxInterface(leftExpression?.let { defaultRuneValue(leftValue, it, env) } ?: leftValue, rightType)
        }
        if (!rightIsInterface && !rightIsUntypedNil && leftIsInterface) {
            right = boxInterface(rightExpression?.let { defaultRuneValue(rightValue, it, env) } ?: rightValue, leftType)
        }
        return left to right
    }

    private fun logicalResultType(
        leftExpression: Expression,
        leftValue: Any?,
        rightExpression: Expression,
        env: Environment
    ): GoTypeSyntax? {
        fun operandType(expression: Expression, value: Any?): GoTypeSyntax? =
            staticExpressionType(expression, env) ?: when {
                expression.unparenthesized() is NameExpression &&
                    (expression.unparenthesized() as NameExpression).name in setOf("true", "false") -> null
                value is Boolean -> null
                else -> runtimeType(value)
            }

        val left = operandType(leftExpression, leftValue)
        val right = operandType(rightExpression, null)
        return (left ?: right)?.let { resolveRuntimeType(it, env) }
    }

    private fun staticPromotedFieldType(type: StructGoType, name: String, env: Environment): GoTypeSyntax? {
        data class Node(val type: GoTypeSyntax, val ancestors: Set<String>)
        var level = listOf(Node(type, emptySet()))
        while (level.isNotEmpty()) {
            val matches = mutableListOf<GoTypeSyntax>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                val actual = when (val resolved = underlying(resolveRuntimeType(node.type, env))) {
                    is PointerGoType -> underlying(resolved.element)
                    else -> resolved
                } as? StructGoType ?: return@forEach
                actual.fields.forEach { field ->
                    if (name in field.names) matches += resolveRuntimeType(field.type, env)
                    if (field.names.isEmpty()) {
                        val embedded = resolveRuntimeType(field.type, env)
                        val key = "${actual.hashCode()}:${embedded}"
                        if (key !in node.ancestors) next += Node(embedded, node.ancestors + key)
                    }
                }
            }
            if (matches.isNotEmpty()) return matches.singleOrNull()
            level = next
        }
        return null
    }

    private suspend fun rangeIndexed(
        length: Int,
        range: RangeClause,
        body: BlockStatement,
        env: Environment,
        labels: Set<String>,
        declaredTypes: List<GoTypeSyntax>?,
        values: (Int) -> List<Any?>
    ) {
        for (i in 0 until length) {
            yield()
            if (range.targets.isNotEmpty()) assignValues(range.targets, range.operator ?: TokenKind.ASSIGN,
                values(i).take(range.targets.size), env, declaredTypes = declaredTypes)
            try { executeBlock(body, env) }
            catch (signal: ContinueSignal) { if (!targets(signal.label, labels)) throw signal }
            catch (signal: BreakSignal) { if (!targets(signal.label, labels)) throw signal else break }
        }
    }

    private suspend fun initialize(names: List<String>, expressions: List<Expression>, env: Environment, type: GoTypeSyntax? = null) {
        val resolvedType = type?.let { resolveRuntimeType(it, env) }
        val values = expandValues(evaluateRhs(expressions, names.size, env), names.size)
        if (values.isNotEmpty() && values.size != names.size) throw RuntimeGoError("initializer count mismatch")
        names.forEachIndexed { i, name ->
            val value = if (values.isNotEmpty()) values[i].let {
                val sourceExpression = expressions.getOrNull(i)
                if (resolvedType != null) convert(resolvedType, defaultRuneValue(it, sourceExpression, env))
                else defaultConstantValue(it, sourceExpression, env)
            }
            else if (resolvedType != null) zeroValue(resolvedType) else GoInteger(0L, NamedGoType("int"))
            if (name != "_") env.define(name, value, resolvedType ?: inferredStorageType(
                value, expressions.getOrNull(i), env, if (expressions.size == 1) i else 0
            ))
        }
    }

    private fun inferredStorageType(
        value: Any?, expression: Expression?, env: Environment, resultIndex: Int = 0
    ): GoTypeSyntax? = expression?.let { staticExpressionResultType(it, resultIndex, env) }
            ?: if (value == null || value is GoInterfaceValue) InterfaceGoType(emptyList()) else runtimeType(value)

    private suspend fun initializeConstant(declaration: ConstantDeclaration) {
        initializeConstantIn(declaration, globals)
    }

    private suspend fun initializeConstantIn(declaration: ConstantDeclaration, target: Environment) {
        val resolvedType = declaration.type?.let { resolveRuntimeType(it, target) }
        val scope = target.child()
        val iotaIsShadowed = "iota" in scope.imports.packages ||
            if (target === globals) packageShadowsIota else target.binding("iota") != null
        if (!iotaIsShadowed) scope.define("iota", BigInteger.valueOf(declaration.iotaIndex.toLong()))
        val values = expandValues(declaration.values.map { evaluate(it, scope) }, declaration.names.size)
        if (values.size != declaration.names.size) throw RuntimeGoError("constant initializer count mismatch")
        declaration.names.zip(values).forEachIndexed { index, (name, value) ->
            val expression = declaration.values.getOrNull(index)
            val initialized = resolvedType?.let { convert(it, defaultRuneValue(value, expression, scope)) } ?: value
            val type = resolvedType ?: if (expression != null && isRuneConstantExpression(expression, scope)) untypedRuneRuntimeType else null
            if (name != "_") target.define(name, initialized, type)
        }
    }

    private fun <T> orderPackageDeclarations(
        declarations: List<T>,
        names: (T) -> List<String>,
        expressions: (T) -> List<Expression>,
        includeFunctionDependencies: Boolean
    ): List<T> {
        val declarationByName = mutableMapOf<String, Int>()
        declarations.forEachIndexed { index, declaration -> names(declaration).forEach { name ->
            if (name != "_") declarationByName[name] = index
        } }
        val dependencies = declarations.indices.map { index ->
            val refs = expressions(declarations[index]).flatMapTo(linkedSetOf(), ::expressionNames)
            if (includeFunctionDependencies) addFunctionDependencies(refs)
            refs.mapNotNullTo(linkedSetOf()) { declarationByName[it] }
        }
        val initialized = BooleanArray(declarations.size)
        val ordered = mutableListOf<T>()
        while (ordered.size < declarations.size) {
            val next = declarations.indices.firstOrNull { i ->
                !initialized[i] && dependencies[i].all { initialized[it] }
            } ?: throw RuntimeGoError("package initialization cycle")
            initialized[next] = true
            ordered += declarations[next]
        }
        return ordered
    }

    private fun addFunctionDependencies(references: MutableSet<String>) {
        val pending = ArrayDeque(references.filter { it in functions })
        val visited = mutableSetOf<String>()
        while (pending.isNotEmpty()) {
            val name = pending.removeFirst()
            if (!visited.add(name)) continue
            val function = functions[name] ?: continue
            val functionReferences = GoPackageDependencies.functionReferences(function)
            functionReferences.filter { it !in references && it in functions }.forEach(pending::addLast)
            references += functionReferences
        }
    }

    private fun expressionNames(expression: Expression): Set<String> = when (expression) {
        is NameExpression -> setOf(expression.name)
        is LiteralExpression, is TypeExpression -> emptySet()
        is UnaryExpression -> expressionNames(expression.operand)
        is BinaryExpression -> expressionNames(expression.left) + expressionNames(expression.right)
        is CallExpression -> expressionNames(expression.function) + expression.arguments.flatMap(::expressionNames)
        is SelectorExpression -> expressionNames(expression.receiver)
        is IndexExpression -> expressionNames(expression.receiver) + expressionNames(expression.index)
        is SliceExpression -> expressionNames(expression.receiver) + listOfNotNull(expression.low, expression.high).flatMap(::expressionNames)
        is TypeAssertionExpression -> expressionNames(expression.receiver)
        is TypeSwitchGuardExpression -> expressionNames(expression.receiver)
        is ParenthesizedExpression -> expressionNames(expression.expression)
        is CompositeLiteral -> expression.elements.flatMapTo(linkedSetOf()) { element ->
            (element.key?.let(::expressionNames) ?: emptySet()) + expressionNames(element.value)
        }
        is ElidedCompositeLiteral -> expression.elements.flatMapTo(linkedSetOf()) { element ->
            (element.key?.let(::expressionNames) ?: emptySet()) + expressionNames(element.value)
        }
        is FunctionLiteralExpression -> GoPackageDependencies.functionLiteralReferences(
            expression.parameters, expression.resultNames, expression.body
        )
    }

    private suspend fun evaluateRhs(expressions: List<Expression>, arity: Int, env: Environment): List<Any?> {
        if (expressions.size == 1 && arity == 2 && expressions[0] is TypeAssertionExpression) {
            val assertion = expressions[0] as TypeAssertionExpression
            return listOf(assertType(evaluate(assertion.receiver, env), assertion.type))
        }
        if (expressions.size == 1 && expressions[0] is UnaryExpression &&
            (expressions[0] as UnaryExpression).operator == TokenKind.ARROW) {
            val receive = expressions[0] as UnaryExpression
            return listOf(receiveResult(evaluate(receive.operand, env)))
        }
        if (expressions.size == 1 && arity == 2 && expressions[0] is IndexExpression) {
            val index = expressions[0] as IndexExpression
            val receiver = evaluate(index.receiver, env)
            val key = evaluate(index.index, env)
            if (receiver is GoMap) {
                val keyType = receiver.keyType
                val mapIndex = if (underlying(keyType) is InterfaceGoType)
                    defaultRuneValue(key, index.index, env) else key
                val mapKey = mapKey(mapIndex, keyType)
                val found = receiver.values.containsKey(mapKey)
                return listOf(MapLookupResult(mapValue(receiver, mapKey), found))
            }
            if (receiver is GoNilValue && underlying(receiver.type) is MapGoType) {
                val mapType = underlying(receiver.type) as MapGoType
                return listOf(MapLookupResult(zeroValue(mapType.value), false))
            }
        }
        return expressions.map { evaluate(it, env) }
    }

private suspend fun evaluate(expression: Expression, env: Environment): Any? = when (expression) {
        is NameExpression -> {
            val binding = env.binding(expression.name)
            val dotImportedFunction = env.imports.dotPackages.firstNotNullOfOrNull { path ->
                importedRuntimePackages[path]?.exportedFunction(expression.name)
            }
            val dotImportedConstant = env.imports.dotPackages.firstNotNullOfOrNull { path ->
                importedRuntimePackages[path]?.exportedConstant(expression.name)?.let { value ->
                    importedExportedValue(path, expression.name, value)
                }
            }
            val dotImportedVariablePath = env.imports.dotPackages.firstOrNull { path ->
                expression.name in importedRuntimePackages[path]?.exportedVariableNames.orEmpty()
            }
            val dotImportedTypePath = env.imports.dotPackages.firstOrNull { path ->
                expression.name in importedRuntimePackages[path]?.exportedTypeNames.orEmpty()
            }
            if (binding != null) binding.value
            else typeDefinitions[expression.name]?.let { TypeValue(NamedGoType(expression.name)) }
                ?: functions[expression.name]?.let { FunctionValue(it, globals, owner = this) }
                ?: dotImportedFunction
                ?: dotImportedConstant
                ?: dotImportedVariablePath?.let { path -> importedRuntimePackages[path]?.exportedVariable(expression.name)?.let { value ->
                    importedExportedValue(path, expression.name, value)
                } }
                ?: dotImportedTypePath?.let { path -> TypeValue(QualifiedGoType(path, expression.name)) }
                ?: when {
                    "fmt" in env.imports.dotPackages && expression.name in GoFmtPackage.exportedNames ->
                        BuiltinValue(expression.name, GoFmtPackage.functionType(expression.name))
                    "math" in env.imports.dotPackages && expression.name in GoMathPackage.exportedNames -> evaluateMathPackageMember(expression.name)
                    "unsafe" in env.imports.dotPackages && expression.name in GoUnsafePackage.exportedNames ->
                        evaluateUnsafePackageMember(expression.name)
                    else -> when (expression.name) {
                    "true" -> true
                    "false" -> false
                    "nil" -> null
                    "make", "new", "close", "len", "cap", "append", "copy", "delete", "print", "println", "panic", "recover", "complex", "real", "imag" -> BuiltinValue(expression.name)
                    in builtinTypes -> TypeValue(NamedGoType(expression.name))
                    else -> throw RuntimeGoError("undefined: ${expression.name}")
                    }
                }
        }
        is LiteralExpression -> literal(expression.token)
        is ParenthesizedExpression -> evaluate(expression.expression, env)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.AND -> addressOf(expression.operand, env)
            TokenKind.MUL -> {
                val pointer = evaluate(expression.operand, env) as? GoPointer
                    ?: throw RuntimeGoError("dereference of non-pointer")
                val pointedType = pointer.pointeeType
                    ?: throw RuntimeGoError("pointer has no static element type")
                copyForType(pointer.get(), pointedType)
            }
            TokenKind.ARROW -> receiveResult(evaluate(expression.operand, env)).value
            else -> unary(expression.operator, evaluate(expression.operand, env))
        }
        is BinaryExpression -> {
            val left = copyValue(evaluate(expression.left, env))
            if (expression.operator == TokenKind.LAND || expression.operator == TokenKind.LOR) {
                val leftBoolean = booleanValue(left, expression.operator.name)
                val result = when {
                    expression.operator == TokenKind.LAND && !leftBoolean -> false
                    expression.operator == TokenKind.LOR && leftBoolean -> true
                    else -> booleanValue(evaluate(expression.right, env), expression.operator.name)
                }
                logicalResultType(expression.left, left, expression.right, env)?.let { GoBoolean(result, it) } ?: result
            } else {
                val right = copyValue(evaluate(expression.right, env))
                if (expression.operator == TokenKind.EQL || expression.operator == TokenKind.NEQ) {
                    val (comparedLeft, comparedRight) = interfaceComparisonOperands(
                        expression.left, left, expression.right, right, env
                    )
                    binary(comparedLeft, expression.operator, comparedRight)
                } else {
                    binary(left, expression.operator, right)
                }
            }
        }
        is SelectorExpression -> {
            val methodReceiverType = methodExpressionReceiver(expression.receiver, env)
            if (methodReceiverType != null) {
                val method = runtimeMethodSet(methodReceiverType)[expression.field]
                    ?: throw RuntimeGoError("undefined method ${expression.field} on $methodReceiverType")
                MethodExpressionValue(
                    methodReceiverType,
                    expression.field,
                    FunctionGoType(listOf(ParameterSyntax(null, methodReceiverType)) + method.parameters, method.results)
                )
            } else if (expression.receiver is NameExpression && !env.contains(expression.receiver.name) &&
                env.imports.packages[expression.receiver.name] == "fmt") BuiltinValue(expression.field)
            else if (expression.receiver is NameExpression && !env.contains(expression.receiver.name) &&
                env.imports.packages[expression.receiver.name] == "math") evaluateMathPackageMember(expression.field)
            else if (expression.receiver is NameExpression && !env.contains(expression.receiver.name) &&
                env.imports.packages[expression.receiver.name] == "unsafe")
                evaluateUnsafePackageMember(expression.field)
            else if (expression.receiver is NameExpression && !env.contains(expression.receiver.name) &&
                env.imports.packages[expression.receiver.name]?.let(importedRuntimePackages::containsKey) == true) {
                val path = env.imports.packages.getValue(expression.receiver.name)
                val imported = importedRuntimePackages.getValue(path)
                when {
                    imported.exportedFunction(expression.field) != null -> imported.exportedFunction(expression.field)
                    expression.field in imported.exportedConstantNames -> imported.exportedConstant(expression.field)?.let { value ->
                        importedExportedValue(path, expression.field, value)
                    }
                    expression.field in imported.exportedVariableNames -> imported.exportedVariable(expression.field)?.let { value ->
                        importedExportedValue(path, expression.field, value)
                    }
                    expression.field in imported.exportedTypeNames -> TypeValue(QualifiedGoType(path, expression.field))
                    else -> throw RuntimeGoError("undefined imported identifier ${expression.field}")
                }
            }
            else {
                val receiver = evaluate(expression.receiver, env)
                if (receiver is GoPointer && receiver.isNil) {
                    val baseType = receiver.pointeeType ?: throw RuntimeGoError("nil pointer has no static type")
                    val (owner, method) = methodDeclaration(baseType, expression.field)
                        ?: throw RuntimeGoError("unknown field or method: ${expression.field}")
                    if (method.receiver?.type !is PointerGoType)
                        throw RuntimeGoError("invalid memory address or nil pointer dereference")
                    MethodValue(method, receiver, owner)
                } else if (receiver is GoInterfaceValue) {
                    val (owner, method) = methodDeclaration(receiver.dynamicType, expression.field)
                        ?: throw RuntimeGoError("unknown interface method: ${expression.field}")
                    val pointerReceiver = method.receiver?.type is PointerGoType
                    val boundReceiver = when {
                        pointerReceiver && receiver.value is GoPointer -> receiver.value
                        pointerReceiver -> throw RuntimeGoError("interface value does not contain a pointer receiver")
                        receiver.value is GoPointer -> copyValue(dereference(receiver.value))
                        else -> copyValue(receiver.value)
                    }
                    MethodValue(method, boundReceiver, owner)
                } else {
                    selectStructMember(receiver, expression.field, expression.receiver, env)
                }
            }
        }
        is CallExpression -> call(expression, env)
        is IndexExpression -> index(
            evaluate(expression.receiver, env), evaluate(expression.index, env), expression.index, env
        )
        is SliceExpression -> slice(evaluate(expression.receiver, env), expression.low?.let { evaluate(it, env) },
            expression.high?.let { evaluate(it, env) })
        is TypeAssertionExpression -> {
            val assertion = assertType(evaluate(expression.receiver, env), resolveRuntimeType(expression.type, env))
            if (!assertion.ok) throw RuntimeGoError("type assertion failed: ${assertion.dynamicType} is not ${expression.type}")
            assertion.value
        }
        is TypeSwitchGuardExpression -> throw RuntimeGoError("type switch guard used outside a type switch")
        is TypeExpression -> TypeValue(resolveRuntimeType(expression.type, env))
        is CompositeLiteral -> composite(expression.copy(type = resolveRuntimeType(expression.type, env)), env)
        is ElidedCompositeLiteral -> throw RuntimeGoError("elided composite literal requires an element type")
        is FunctionLiteralExpression -> {
            val parameters = expression.parameters.map { it.copy(type = resolveRuntimeType(it.type, env)) }
            val results = expression.results.map { resolveRuntimeType(it, env) }
            val declaration = FunctionDeclaration(
                "<function literal>", parameters.map { it.name }, expression.body,
                parameters.map { it.type }, results, null, expression.variadic, expression.resultNames
            )
            FunctionValue(declaration, env, FunctionGoType(parameters, results), this)
        }
    }

    private fun methodExpressionReceiver(expression: Expression, env: Environment): GoTypeSyntax? = when (expression) {
        is NameExpression -> if (env.contains(expression.name)) null else {
            env.typeBinding(expression.name) ?: if (expression.name in env.imports.packages) null
            else typeDefinitions[expression.name]?.let { NamedGoType(expression.name) }
                ?: if (expression.name in builtinTypes) NamedGoType(expression.name) else null
        }
        is ParenthesizedExpression -> methodExpressionReceiver(expression.expression, env)
        is SelectorExpression -> {
            val alias = (expression.receiver as? NameExpression)?.name
            val path = alias?.let(env.imports.packages::get)
            if (path != null && expression.field in importedRuntimePackages[path]?.exportedTypeNames.orEmpty())
                QualifiedGoType(path, expression.field) else null
        }
        is UnaryExpression -> if (expression.operator == TokenKind.MUL) {
            methodExpressionReceiver(expression.operand, env)?.let(::PointerGoType)
        } else null
        else -> null
    }

    private suspend fun addressOf(expression: Expression, env: Environment): GoPointer = when (expression) {
        is ParenthesizedExpression -> addressOf(expression.expression, env)
        is NameExpression -> env.imports.dotPackages.firstNotNullOfOrNull { path ->
            importedRuntimePackages[path]?.exportedVariablePointer(expression.name)
        } ?: env.pointer(expression.name)
        is SelectorExpression -> {
            val pointer = if (expression.receiver is NameExpression && !env.contains(expression.receiver.name)) {
                env.imports.packages[expression.receiver.name]?.let { path ->
                    importedRuntimePackages[path]?.exportedVariablePointer(expression.field)
                }
            } else null
            pointer ?: pointerToStructField(evaluate(expression.receiver, env), expression.field)
        }
        is IndexExpression -> {
            val receiver = evaluate(expression.receiver, env)
            val key = collectionIndex(evaluate(expression.index, env), "index")
            when (receiver) {
                is GoSlice -> receiver.pointerAt(key)
                is GoArray -> receiver.pointerAt(key)
                is GoPointer -> (receiver.get() as? GoArray)?.pointerAt(key)
                    ?: throw RuntimeGoError("address-of index requires pointer to array")
                else -> throw RuntimeGoError("address-of index requires an array or slice element")
            }
        }
        is UnaryExpression -> if (expression.operator == TokenKind.MUL) {
            evaluate(expression.operand, env) as? GoPointer ?: throw RuntimeGoError("cannot take address through a non-pointer")
        } else throw RuntimeGoError("expression is not addressable")
        is CompositeLiteral -> addressableCell(composite(expression, env), resolveRuntimeType(expression.type, env))
        else -> throw RuntimeGoError("expression is not addressable")
    }

    private fun pointerToStructField(receiver: Any?, name: String): GoPointer {
        data class Node(val value: Any?, val ancestors: Set<String>)
        var level = listOf(Node(receiver, emptySet()))
        while (level.isNotEmpty()) {
            val matches = mutableListOf<GoPointer>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                var receiver = node.value
                while (receiver is GoPointer) receiver = receiver.get()
                val struct = receiver as? GoStruct ?: return@forEach
                if (name in struct.fields) matches += struct.pointer(name)
                struct.embeddedFields.forEach { embeddedName ->
                    val embeddedValue = struct.fields[embeddedName] ?: return@forEach
                    val key = "${struct.packagePath}:${struct.namedType}.$embeddedName"
                    if (key !in node.ancestors) {
                        val child = if (embeddedValue is GoPointer) embeddedValue else struct.pointer(embeddedName)
                        next += Node(child, node.ancestors + key)
                    }
                }
            }
            if (matches.isNotEmpty()) {
                if (matches.size != 1) throw RuntimeGoError("ambiguous selector $name")
                return matches.single()
            }
            level = next
        }
        throw RuntimeGoError("unknown struct field: $name")
    }

    private suspend fun selectStructMember(receiver: Any?, name: String, receiverExpression: Expression, env: Environment): Any? {
        data class Node(val value: Any?, val ancestors: Set<String>)
        data class Candidate(
            val owner: GoStruct?,
            val method: FunctionDeclaration?,
            val receiver: Any?,
            val runtimeError: GoRuntimeErrorValue? = null,
            val methodOwner: Interpreter? = null
        )
        var level = listOf(Node(receiver, emptySet()))
        while (level.isNotEmpty()) {
            val candidates = mutableListOf<Candidate>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                if (node.value is GoPointer && node.value.isNil) {
                    val embeddedType = node.value.pointeeType
                    if (embeddedType != null) methodDeclaration(embeddedType, name)?.let { (owner, method) ->
                        candidates += Candidate(null, method, node.value, methodOwner = owner)
                    }
                    return@forEach
                }
                val current = dereference(node.value)
                if (current is GoInterfaceValue) {
                    if (current.value is GoRuntimeErrorValue && name == "Error")
                        candidates += Candidate(null, null, current, current.value)
                    else (current.implementationOwner ?: this).methodDeclaration(current.dynamicType, name)?.let { (owner, method) ->
                        candidates += Candidate(null, method, current, methodOwner = owner)
                    }
                    return@forEach
                }
                val struct = current as? GoStruct
                if (struct == null) {
                    if (current is GoRuntimeErrorValue && name == "Error") {
                        candidates += Candidate(null, null, current, current)
                        return@forEach
                    }
                    val valueType = (node.value as? GoPointer)?.pointeeType ?: runtimeType(current) ?: return@forEach
                    methodDeclaration(valueType, name)?.let { (owner, method) ->
                        candidates += Candidate(null, method, node.value, methodOwner = owner)
                    }
                    return@forEach
                }
                if (name in struct.fields) candidates += Candidate(struct, null, node.value)
                val receiverType = (node.value as? GoPointer)?.pointeeType ?: runtimeType(current)
                receiverType?.let { methodDeclaration(it, name) }?.let { (owner, method) ->
                    candidates += Candidate(null, method, node.value, methodOwner = owner)
                }
                struct.embeddedFields.forEach { embeddedName ->
                    val embeddedValue = struct.fields[embeddedName] ?: return@forEach
                    val key = "${struct.packagePath}:${struct.namedType}.$embeddedName"
                    if (key !in node.ancestors) {
                        val child = if (embeddedValue is GoPointer) embeddedValue else struct.pointer(embeddedName)
                        next += Node(child, node.ancestors + key)
                    }
                }
            }
            if (candidates.isNotEmpty()) {
                if (candidates.size != 1) throw RuntimeGoError("ambiguous selector $name")
                val candidate = candidates.single()
                candidate.owner?.let { owner -> return owner.fields[name] }
                candidate.runtimeError?.let { return RuntimeErrorMethodValue(it) }
                val method = candidate.method ?: throw RuntimeGoError("unknown selector $name")
                val pointerReceiver = method.receiver?.type is PointerGoType
                val methodReceiver = when {
                    candidate.receiver is GoInterfaceValue -> {
                        val value = candidate.receiver
                        when {
                            pointerReceiver && value.value is GoPointer -> value.value
                            pointerReceiver -> throw RuntimeGoError("interface value does not contain a pointer receiver")
                            value.value is GoPointer -> copyValue(dereference(value.value))
                            else -> copyValue(value.value)
                        }
                    }
                    pointerReceiver && candidate.receiver is GoPointer -> candidate.receiver
                    pointerReceiver -> addressOf(receiverExpression, env)
                    candidate.receiver is GoPointer && candidate.receiver.isNil ->
                        throw RuntimeGoError("invalid memory address or nil pointer dereference")
                    candidate.receiver is GoPointer -> copyValue(dereference(candidate.receiver))
                    else -> copyValue(candidate.receiver)
                }
                return MethodValue(method, methodReceiver, candidate.methodOwner ?: this)
            }
            level = next
        }
        throw RuntimeGoError("unknown struct field or method: $name")
    }

    private fun unsafeIntrinsicName(function: Expression, env: Environment): String? = when (val target = function.unparenthesized()) {
        is SelectorExpression -> {
            val alias = (target.receiver as? NameExpression)?.name ?: return null
            if (env.contains(alias) || env.typeBinding(alias) != null || env.imports.packages[alias] != "unsafe") return null
            target.field.takeIf { GoUnsafePackage.functionType(it) != null }
        }
        is NameExpression -> if (!env.contains(target.name) && env.typeBinding(target.name) == null &&
            "unsafe" in env.imports.dotPackages && target.name in GoUnsafePackage.exportedNames) target.name else null
        else -> null
    }

    private fun unsafeIntrinsicValue(name: String, expression: Expression, env: Environment): Long {
        val sourceType = staticExpressionType(expression, env)
            ?: throw RuntimeGoError("cannot determine unsafe intrinsic argument type")
        val type = when (sourceType) {
            NamedGoType("#untyped-bool") -> NamedGoType("bool")
            NamedGoType("#untyped-int") -> NamedGoType("int")
            NamedGoType("#untyped-rune") -> predeclaredIntRuntimeType
            NamedGoType("#untyped-float") -> NamedGoType("float64")
            NamedGoType("#untyped-complex") -> NamedGoType("complex128")
            NamedGoType("#untyped-string") -> NamedGoType("string")
            else -> sourceType
        }
        val arrayLength: (Expression) -> BigInteger = { integerLiteral(it, env) }
        try {
            return when (name) {
                "Sizeof", "Alignof" -> {
                    val layout = GoUnsafePackage.layout(type, ::underlying, arrayLength)
                    if (name == "Sizeof") layout.size else layout.align
                }
                "Offsetof" -> {
                    val (base, fields) = selectorPath(expression)
                        ?: throw RuntimeGoError("unsafe.Offsetof requires a struct field selector")
                    var currentType = staticExpressionType(base, env)
                        ?: throw RuntimeGoError("cannot determine unsafe.Offsetof base type")
                    var offset = 0L
                    fields.forEach { fieldName ->
                        val field = GoUnsafePackage.fieldOffset(currentType, fieldName, ::underlying, arrayLength)
                            ?: throw RuntimeGoError("unknown or ambiguous struct field $fieldName")
                        offset = Math.addExact(offset, field.first)
                        currentType = field.second
                    }
                    offset
                }
                else -> throw RuntimeGoError("undefined unsafe intrinsic $name")
            }
        } catch (failure: ArithmeticException) {
            throw RuntimeGoError("unsafe layout overflows uintptr")
        } catch (failure: IllegalArgumentException) {
            throw RuntimeGoError(failure.message ?: "invalid unsafe layout")
        }
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

    private suspend fun call(call: CallExpression, env: Environment): Any? {
        val parenthesizedType = call.function.unparenthesized() as? TypeExpression
        if (parenthesizedType != null && call.arguments.size == 1 && !call.expandLastArgument) {
            val value = evaluate(call.arguments.single(), env)
            val source = call.arguments.single()
            return convert(resolveRuntimeType(parenthesizedType.type, env), defaultRuneValue(value, source, env))
        }
        unsafeIntrinsicName(call.function, env)?.let { name ->
            val argument = call.arguments.singleOrNull() ?: throw RuntimeGoError("unsafe intrinsic requires one argument")
            return GoInteger(unsafeIntrinsicValue(name, argument, env), NamedGoType("uintptr"))
        }
        val builtinName = (call.function as? NameExpression)?.name
        if (builtinName in setOf("len", "cap") && builtinName?.let {
                !env.contains(it) && env.typeBinding(it) == null && !functions.containsKey(it) && !typeDefinitions.containsKey(it)
            } == true &&
            call.arguments.size == 1 && !call.expandLastArgument && !containsCallOrReceive(call.arguments.single(), env)) {
            staticRangeArrayLength(call.arguments.single(), env)?.let { return it.toLong() }
        }
        val target = evaluate(call.function, env)
        val rawArgs = evaluateCallArguments(call, env)
        val args = adaptCallArguments(call, target, rawArgs, env).let { arguments ->
            if (target is TypeValue && arguments.size == 1 && call.arguments.size == 1 && !call.expandLastArgument)
                listOf(defaultRuneValue(arguments.single(), call.arguments.single(), env))
            else arguments
        }
        return call(target, args, call.expandLastArgument, env.panicState, environment = env)
    }

    private fun adaptCallArguments(
        call: CallExpression,
        target: Any?,
        rawArgs: List<Any?>,
        env: Environment
    ): List<Any?> {
        val parameterTypes = when (target) {
            is FunctionValue -> target.owner.checkedFunctionType(target.function).parameters.map { it.type }
            is MethodValue -> target.owner.checkedFunctionType(target.function).parameters.map { it.type }
            is MethodExpressionValue -> (target.type as? FunctionGoType)?.parameters?.map { it.type }.orEmpty()
            else -> emptyList()
        }
        val variadicParameterIndex = when (target) {
            is FunctionValue -> target.owner.checkedFunctionType(target.function).parameters.lastIndex.takeIf { target.function.variadic }
            is MethodValue -> target.owner.checkedFunctionType(target.function).parameters.lastIndex.takeIf { target.function.variadic }
            is MethodExpressionValue -> (target.type as? FunctionGoType)?.parameters?.let { parameters ->
                parameters.lastIndex.takeIf { parameters[it].variadic }
            }
            else -> null
        }
        val variadicElementType = variadicParameterIndex?.let { index ->
            (parameterTypes.getOrNull(index) as? SliceGoType)?.element
        }
        val appendElementType = if (target == BuiltinValue("append") && !call.expandLastArgument) {
            call.arguments.firstOrNull()?.let { staticExpressionType(it, env) }?.let(::underlying)
                .let { it as? SliceGoType }?.element
        } else null
        val deleteKeyType = if (target == BuiltinValue("delete")) {
            call.arguments.firstOrNull()?.let { staticExpressionType(it, env) }?.let(::underlying)
                .let { it as? MapGoType }?.key
        } else null
        return rawArgs.mapIndexed { index, value ->
            val sharedExpression = call.arguments.singleOrNull()?.takeIf { rawArgs.size > 1 }
            val argumentExpression = call.arguments.getOrNull(index) ?: sharedExpression
            val resultIndex = if (sharedExpression != null) index else 0
            val declaredType = when {
                !call.expandLastArgument && variadicParameterIndex != null && index >= variadicParameterIndex ->
                    variadicElementType
                else -> parameterTypes.getOrNull(index)
            }
            when {
                declaredType != null && underlying(declaredType) is InterfaceGoType ->
                    boxInterfaceAssignment(value, declaredType, argumentExpression, env, resultIndex)
                target == BuiltinValue("panic") && index == 0 ->
                    defaultRuneValue(value, call.arguments.getOrNull(index), env)
                index > 0 && appendElementType?.let { underlying(it) is InterfaceGoType } == true ->
                    defaultRuneValue(value, call.arguments.getOrNull(index), env)
                index == 1 && deleteKeyType?.let { underlying(it) is InterfaceGoType } == true ->
                    defaultRuneValue(value, call.arguments.getOrNull(index), env)
                else -> value
            }
        }
    }

    private suspend fun evaluateCallArguments(call: CallExpression, env: Environment): List<Any?> {
        if (!call.expandLastArgument && call.arguments.size == 1) {
            val value = evaluate(call.arguments.single(), env)
            if (value is GoMultiValue) return value.values.map(::copyValue)
            return listOf(copyValue(value))
        }
        return call.arguments.map { copyValue(evaluate(it, env)) }
    }

    private fun runtimeTypeConversion(call: CallExpression, env: Environment): GoTypeSyntax? = when (val target = call.function.unparenthesized()) {
        is TypeExpression -> resolveRuntimeType(target.type, env)
        is NameExpression -> {
            val binding = env.binding(target.name)
            when {
                binding?.value is TypeValue -> binding.value.type
                binding == null -> env.imports.dotPackages.firstOrNull { path ->
                    target.name in importedRuntimePackages[path]?.exportedTypeNames.orEmpty() ||
                        path == "unsafe" && target.name in GoUnsafePackage.exportedTypes
                }?.let { path -> QualifiedGoType(path, target.name) }
                    ?: target.name.takeIf { it in builtinTypes }?.let(::NamedGoType)
                else -> null
            }
        }
        is SelectorExpression -> {
            val alias = (target.receiver as? NameExpression)?.name
            val path = alias?.takeIf { !env.contains(it) && env.typeBinding(it) == null }?.let(env.imports.packages::get)
            if (path == "unsafe" && target.field in GoUnsafePackage.exportedTypes)
                QualifiedGoType(path, target.field)
            else if (path != null && target.field in importedRuntimePackages[path]?.exportedTypeNames.orEmpty())
                QualifiedGoType(path, target.field) else null
        }
        else -> null
    }

    private fun containsCallOrReceive(expression: Expression, env: Environment): Boolean = when (expression) {
        is CallExpression -> runtimeTypeConversion(expression, env)?.let {
            expression.arguments.any { argument -> containsCallOrReceive(argument, env) }
        } ?: true
        is UnaryExpression -> expression.operator == TokenKind.ARROW || containsCallOrReceive(expression.operand, env)
        is BinaryExpression -> containsCallOrReceive(expression.left, env) || containsCallOrReceive(expression.right, env)
        is SelectorExpression -> containsCallOrReceive(expression.receiver, env)
        is IndexExpression -> containsCallOrReceive(expression.receiver, env) || containsCallOrReceive(expression.index, env)
        is SliceExpression -> containsCallOrReceive(expression.receiver, env) ||
            listOfNotNull(expression.low, expression.high).any { containsCallOrReceive(it, env) }
        is TypeAssertionExpression -> containsCallOrReceive(expression.receiver, env)
        is ParenthesizedExpression -> containsCallOrReceive(expression.expression, env)
        is CompositeLiteral -> expression.elements.any { (it.key?.let { key -> containsCallOrReceive(key, env) } ?: false) ||
            containsCallOrReceive(it.value, env) }
        is ElidedCompositeLiteral -> expression.elements.any { (it.key?.let { key -> containsCallOrReceive(key, env) } ?: false) ||
            containsCallOrReceive(it.value, env) }
        is FunctionLiteralExpression -> false
        else -> false
    }

    private suspend fun call(
        target: Any?,
        args: List<Any?>,
        expandLastArgument: Boolean = false,
        panicState: PanicState = PanicState(),
        deferredCall: Boolean = false,
        environment: Environment? = null
    ): Any? {
        val effectiveArgs = if (expandLastArgument && !(target == BuiltinValue("append") && args.lastOrNull() is GoString)) {
            val last = args.lastOrNull()
            args.dropLast(1).map(::copyValue) + when (last) {
                is GoSlice -> last.toList().map(::copyValue)
                is GoNilValue -> if (underlying(last.type) is SliceGoType) emptyList() else
                    throw RuntimeGoError("... argument must be a slice")
                null -> emptyList()
                else -> throw RuntimeGoError("... argument must be a slice")
            }
        } else args.map(::copyValue)
        when (target) {
            is FunctionValue -> {
                val values = target.owner.invoke(target.function, args, parent = target.closure, expandedVariadic = expandLastArgument,
                    panicState = panicState, deferredCall = deferredCall)
                val resultTypes = (target.type as? FunctionGoType)?.results
                val exportedValues = if (target.owner !== this && resultTypes != null &&
                    resultTypes.size == values.size) values.mapIndexed { index, value ->
                    externalizeImportedResult(value, resultTypes[index], target.owner)
                } else values
                return if (exportedValues.isEmpty()) null else if (exportedValues.size == 1) exportedValues.single() else GoMultiValue(exportedValues)
            }
            is MethodValue -> {
                val values = target.owner.invoke(target.function, args, target.receiver, expandedVariadic = expandLastArgument,
                    panicState = panicState, deferredCall = deferredCall)
                val importPath = target.owner.packageIdentity
                val exportedValues = if (target.owner !== this && importPath != null &&
                    target.owner.checkedFunctionType(target.function).results.size == values.size) values.mapIndexed { index, value ->
                    val resultType = target.owner.externalizeRuntimeType(
                        target.owner.checkedFunctionType(target.function).results[index], importPath
                    )
                    externalizeImportedResult(value, resultType, target.owner)
                } else values
                return if (exportedValues.isEmpty()) null else if (exportedValues.size == 1) exportedValues.single() else GoMultiValue(exportedValues)
            }
            is RuntimeErrorMethodValue -> {
                if (args.isNotEmpty()) throw RuntimeGoError("Error expects no arguments")
                return GoString(target.receiver.message.toByteArray(Charsets.UTF_8), NamedGoType("string"))
            }
            is MethodExpressionValue -> {
                val receiver = args.firstOrNull() ?: throw RuntimeGoError("method expression requires a receiver")
                val scope = environment ?: globals
                val method = selectStructMember(receiver, target.name, NameExpression("<method-expression receiver>"), scope)
                    as? MethodValue ?: throw RuntimeGoError("${target.name} is not a method")
                return call(method, args.drop(1), expandLastArgument, panicState, deferredCall, environment)
            }
            is GoNilValue -> if (underlying(target.type) is FunctionGoType)
                throw RuntimeGoError("call of nil function")
            is BuiltinValue -> when (target.name) {
                "print", "println" -> {
                    emitOutput(formatBuiltinPrint(effectiveArgs, target.name == "println"))
                    return null
                }
                "panic" -> args.singleOrNull().let { throw PanicSignal(it, stringify(it)) }
                "recover" -> {
                    if (!panicState.recoverAllowed) return null
                    val activePanic = panicState.activePanic ?: return null
                    activePanic.recovered = true
                    panicState.activePanic = null
                    return when (val value = activePanic.value) {
                        null, is GoInterfaceValue -> value
                        else -> runtimeType(value)?.let { GoInterfaceValue(canonicalAliasType(it), value, this) } ?: value
                    }
                }
                "complex" -> {
                    if (args.size != 2) throw RuntimeGoError("complex expects two arguments")
                    if (args.all { it is BigInteger || it is GoRational })
                        return GoExactComplex(exactRational(args[0]), exactRational(args[1]))
                    val type = if (args.filterIsInstance<GoFloat>().any { underlying(it.type) == NamedGoType("float32") })
                        NamedGoType("complex64") else NamedGoType("complex128")
                    val real = real(args[0])
                    val imaginary = real(args[1])
                    return if (type == NamedGoType("complex64"))
                        GoComplex(real.toFloat().toDouble(), imaginary.toFloat().toDouble(), type)
                    else GoComplex(real, imaginary, type)
                }
                "real" -> return when (val value = args.singleOrNull()) {
                    is GoExactComplex -> value.real
                    is GoRational -> value
                    is BigInteger -> GoRational.of(value)
                    is GoComplex -> floatResult(value.real, value.type)
                    is GoFloat -> value.value
                    is GoInteger -> integerAsDouble(value)
                    is Double -> value
                    is Long -> value.toDouble()
                    else -> throw RuntimeGoError("real requires a numeric argument")
                }
                "imag" -> return when (val value = args.singleOrNull()) {
                    is GoExactComplex -> value.imaginary
                    is GoRational, is BigInteger -> GoRational.ZERO
                    is GoComplex -> floatResult(value.imaginary, value.type)
                    is GoFloat, is GoInteger, is Double, is Long -> 0.0
                    else -> throw RuntimeGoError("imag requires a numeric argument")
                }
                "make" -> return make(args)
                "new" -> {
                    val type = (args.singleOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("new requires a type")
                    return addressableCell(zeroValue(type), type)
                }
                "close" -> {
                    when (val channel = args.singleOrNull()) {
                        is GoChannel -> channel.close()
                        is GoNilValue -> if (underlying(channel.type) is ChannelGoType) throw RuntimeGoError("close of nil channel") else throw RuntimeGoError("close of non-channel")
                        else -> throw RuntimeGoError("close of non-channel")
                    }
                    return null
                }
                "len" -> return when (val value = args.singleOrNull()) {
                    is GoString -> value.bytes.size.toLong()
                    is GoSlice -> value.length.toLong()
                    is GoArray -> value.values.size.toLong()
                    is GoPointer -> pointerArrayLength(value, environment)
                    is GoMap -> value.values.size.toLong()
                    is GoChannel -> value.len()
                    is GoNilValue -> when (underlying(value.type)) {
                        is SliceGoType, is MapGoType, is ChannelGoType -> 0L
                        else -> throw RuntimeGoError("len is not defined for this value")
                    }
                    else -> throw RuntimeGoError("len is not defined for this value")
                }
                "cap" -> return when (val value = args.singleOrNull()) {
                    is GoChannel -> value.capacity.toLong()
                    is GoSlice -> value.capacity.toLong()
                    is GoArray -> value.values.size.toLong()
                    is GoPointer -> pointerArrayLength(value, environment)
                    is GoNilValue -> when (underlying(value.type)) {
                        is SliceGoType, is ChannelGoType -> 0L
                        else -> throw RuntimeGoError("cap is not defined for this value")
                    }
                    else -> throw RuntimeGoError("cap is not defined for this value")
                }
                "append" -> return append(effectiveArgs, expandString = expandLastArgument)
                "copy" -> return copy(args)
                "delete" -> { delete(args); return null }
                "Print", "Fprint" -> {
                    val values = effectiveArgs.drop(if (target.name == "Fprint") 1 else 0)
                    val rendered = formatPrintArguments(values, alwaysSpace = false, newline = false)
                    return if (target.name == "Fprint") {
                        writeFmtOutput(effectiveArgs.firstOrNull()
                            ?: throw RuntimeGoError("Fprint requires an io.Writer"), rendered, environment)
                    } else {
                        emitOutput(rendered)
                        fmtWriteResult(rendered.size, null)
                    }
                }
                "Println", "Fprintln" -> {
                    val values = effectiveArgs.drop(if (target.name == "Fprintln") 1 else 0)
                    val rendered = formatPrintArguments(values, alwaysSpace = true, newline = true)
                    return if (target.name == "Fprintln") {
                        writeFmtOutput(effectiveArgs.firstOrNull()
                            ?: throw RuntimeGoError("Fprintln requires an io.Writer"), rendered, environment)
                    } else {
                        emitOutput(rendered)
                        fmtWriteResult(rendered.size, null)
                    }
                }
                else -> if (target.name.startsWith("math.")) return mathCall(target.name.removePrefix("math."), args)
            }
            is TypeValue -> return convert(target.type, args.singleOrNull() ?: throw RuntimeGoError("conversion requires one argument"))
        }
        throw RuntimeGoError("cannot call value")
    }

    private fun formatPrintArguments(values: List<Any?>, alwaysSpace: Boolean, newline: Boolean): ByteArray {
        val bytes = mutableListOf<Byte>()
        values.forEachIndexed { index, value ->
            if (index > 0 && (alwaysSpace || (!isStringOperand(values[index - 1]) && !isStringOperand(value))))
                bytes += 0x20.toByte()
            bytes += formatValueBytes(value).toList()
        }
        if (newline) bytes += 0x0a.toByte()
        return bytes.toByteArray()
    }

    private fun formatBuiltinPrint(values: List<Any?>, newline: Boolean): ByteArray {
        val bytes = mutableListOf<Byte>()
        values.forEachIndexed { index, value ->
            if (newline && index > 0) bytes += 0x20.toByte()
            bytes += formatValueBytes(value).toList()
        }
        if (newline) bytes += 0x0a.toByte()
        return bytes.toByteArray()
    }

    private fun emitOutput(bytes: ByteArray) {
        val byteOutput = outputBytes
        if (byteOutput != null) byteOutput(bytes) else output(decodeGoUtf8Text(bytes))
    }

    private fun formatValueBytes(value: Any?): ByteArray = when (value) {
        is GoString -> value.bytes.copyOf()
        is GoInterfaceValue -> formatValueBytes(value.value)
        is GoPointer -> if (value.isNil) encodeGoUtf8Text("<nil>")
            else concatenateFormatted(encodeGoUtf8Text("&"), formatValueBytes(value.get()))
        is GoSlice -> joinFormatted(value.toList().map(::formatValueBytes), "[", " ", "]")
        is GoArray -> joinFormatted(value.values.map(::formatValueBytes), "[", " ", "]")
        is GoMap -> joinFormatted(value.values.entries.map { (key, item) ->
            concatenateFormatted(formatValueBytes(key.value), encodeGoUtf8Text(":"), formatValueBytes(item))
        }, "map[", " ", "]")
        is GoStruct -> joinFormatted(value.fields.values.map(::formatValueBytes), "{", " ", "}")
        else -> encodeGoUtf8Text(stringify(value))
    }

    private fun joinFormatted(values: List<ByteArray>, prefix: String, separator: String, suffix: String): ByteArray {
        val bytes = mutableListOf<Byte>()
        bytes += encodeGoUtf8Text(prefix).toList()
        values.forEachIndexed { index, value ->
            if (index > 0) bytes += encodeGoUtf8Text(separator).toList()
            bytes += value.toList()
        }
        bytes += encodeGoUtf8Text(suffix).toList()
        return bytes.toByteArray()
    }

    private fun concatenateFormatted(vararg values: ByteArray): ByteArray =
        values.flatMap(ByteArray::asIterable).toByteArray()

    private fun isStringOperand(value: Any?): Boolean {
        val actual = if (value is GoInterfaceValue) value.value else value
        val type = runtimeType(actual) ?: return actual is GoString
        return underlying(type) == NamedGoType("string")
    }

    private suspend fun writeFmtOutput(writer: Any?, bytes: ByteArray, environment: Environment?): Any {
        val scope = environment ?: globals
        val method = selectStructMember(writer, "Write", NameExpression("<fmt writer>"), scope)
        val byteType = predeclaredUInt8RuntimeType
        val slice = GoSlice(
            byteType,
            bytes.mapTo(mutableListOf()) { GoInteger((it.toInt() and 0xff).toLong(), byteType) },
            0,
            bytes.size,
            bytes.size,
            type = SliceGoType(byteType)
        )
        val result = call(method, listOf(slice), environment = scope)
        val values = when (result) {
            is GoMultiValue -> result.values
            null -> emptyList()
            else -> listOf(result)
        }
        val written = values.firstOrNull() ?: GoInteger(0, predeclaredIntRuntimeType)
        val failure = values.getOrNull(1)
        return fmtWriteResult(written, failure)
    }

    private fun fmtWriteResult(written: Any?, failure: Any?): GoMultiValue = GoMultiValue(listOf(
        when (written) {
            is GoInteger -> written
            is Number -> GoInteger(written.toLong(), predeclaredIntRuntimeType)
            else -> GoInteger(0, predeclaredIntRuntimeType)
        },
        failure
    ))

    private suspend fun composite(literal: CompositeLiteral, env: Environment): Any? {
        val type = underlying(literal.type)
        return when (type) {
            is SliceGoType -> {
                val backing = mutableListOf<Any?>()
                var nextIndex = 0
                val usedIndices = mutableSetOf<Int>()
                literal.elements.forEach { element ->
                    val at = element.key?.let { compositeIndex(it, "slice literal index", env) } ?: nextIndex
                    if (at < 0 || at == Int.MAX_VALUE) throw RuntimeGoError("slice literal index out of range")
                    if (!usedIndices.add(at)) throw RuntimeGoError("duplicate slice literal index")
                    while (backing.size <= at) backing += zeroValue(type.element)
                    backing[at] = copyForType(evaluateCompositeValue(element.value, type.element, env), type.element)
                    nextIndex = at + 1
                }
                GoSlice(type.element, backing, 0, backing.size, backing.size, namedTypeName(literal.type), literal.type,
                    namedTypePackage(literal.type))
            }
            is ArrayGoType -> {
                val indices = mutableListOf<Int>()
                var nextIndex = 0
                literal.elements.forEach { element ->
                    val at = element.key?.let { compositeIndex(it, "array literal index", env) } ?: nextIndex
                    indices += at
                    nextIndex = at + 1
                }
                val size = type.length?.let {
                    val length = number(evaluate(it, env), "array length")
                    if (length < 0 || length > Int.MAX_VALUE) throw RuntimeGoError("array length out of range")
                    length.toInt()
                }
                    ?: (indices.maxOrNull()?.plus(1) ?: 0)
                if (size < 0) throw RuntimeGoError("negative array length")
                val values = MutableList(size) { zeroValue(type.element) }
                val usedIndices = mutableSetOf<Int>()
                literal.elements.forEachIndexed { index, element ->
                    val at = indices[index]
                    if (at !in values.indices) throw RuntimeGoError("array literal index out of range")
                    if (!usedIndices.add(at)) throw RuntimeGoError("duplicate array literal index")
                    values[at] = copyForType(evaluateCompositeValue(element.value, type.element, env), type.element)
                }
                GoArray(type.element, values, namedTypeName(literal.type), literal.type, namedTypePackage(literal.type))
            }
            is MapGoType -> {
                val values = linkedMapOf<GoMapKey, Any?>()
                literal.elements.forEach { element ->
                    val keyExpression = element.key ?: throw RuntimeGoError("map literal element requires a key")
                    val key = evaluateCompositeValue(keyExpression, type.key, env)
                    values[mapKey(key, type.key)] = copyForType(evaluateCompositeValue(element.value, type.value, env), type.value)
                }
                GoMap(type.key, type.value, zeroValue(type.value), values,
                    namedTypeName(literal.type), literal.type, namedTypePackage(literal.type))
            }
            is StructGoType -> {
                val fields = linkedMapOf<String, Any?>()
                val fieldList = structFieldSlots(type)
                fieldList.forEach { field ->
                    if (field.name.isNotEmpty()) fields[field.storageKey] = zeroValue(field.type)
                }
                val keyed = literal.elements.map { it.key != null }.toSet()
                if (keyed.size > 1) throw RuntimeGoError("mixture of keyed and unkeyed struct literal elements")
                if (literal.elements.isNotEmpty() && keyed.singleOrNull() != true && literal.elements.size != fieldList.size)
                    throw RuntimeGoError("struct literal has ${literal.elements.size} values for ${fieldList.size} fields")
                val usedFields = mutableSetOf<String>()
                literal.elements.forEachIndexed { i, element ->
                    val field = if (element.key == null) fieldList.getOrNull(i) else {
                        val name = (element.key as? NameExpression)?.name
                        if (name == null || name == "_") throw RuntimeGoError("invalid struct literal field")
                        fieldList.firstOrNull { it.name == name }
                    }
                    if (field == null || field.name.isEmpty()) throw RuntimeGoError("unknown struct literal field")
                    if (!usedFields.add(field.storageKey)) throw RuntimeGoError("duplicate field ${field.name} in struct literal")
                    val value = evaluateCompositeValue(element.value, field.type, env)
                    fields[field.storageKey] = copyForType(value, field.type)
                }
                val fieldTypes = fieldList.filter { it.name.isNotEmpty() }.associate { it.storageKey to it.type }
                val runtimeStructType = resolveRuntimeType(literal.type, env)
                GoStruct(fields, namedTypeName(runtimeStructType), fieldTypes,
                    fieldList.filter { it.embedded }.mapTo(linkedSetOf()) { it.storageKey }, runtimeStructType,
                    namedTypePackage(runtimeStructType))
            }
            else -> throw RuntimeGoError("composite literal for this type is not implemented")
        }
    }

    private suspend fun compositeIndex(expression: Expression, context: String, env: Environment): Int {
        val index = number(evaluate(expression, env), context)
        if (index < 0 || index >= Int.MAX_VALUE) throw RuntimeGoError("$context out of range")
        return index.toInt()
    }

    private suspend fun evaluateCompositeValue(expression: Expression, type: GoTypeSyntax, env: Environment): Any? = when {
        expression !is ElidedCompositeLiteral -> {
            val value = evaluate(expression, env)
            if (underlying(type) is InterfaceGoType) defaultRuneValue(value, expression, env) else value
        }
        underlying(type) is PointerGoType -> {
            val pointerType = underlying(type) as PointerGoType
            addressableCell(composite(CompositeLiteral(pointerType.element, expression.elements), env), pointerType.element)
        }
        else -> composite(CompositeLiteral(type, expression.elements), env)
    }

    private fun underlying(type: GoTypeSyntax): GoTypeSyntax = when (type) {
        is NamedGoType -> typeDefinitions[type.name]?.let(::underlying) ?: when (type.name) {
            "byte" -> predeclaredUInt8RuntimeType
            "rune" -> predeclaredIntRuntimeType
            "error" -> errorInterfaceType
            else -> type
        }
        is QualifiedGoType -> importedRuntimePackages[type.packageName]?.let { imported ->
            imported.typeDefinitions[type.name]?.let { definition ->
                imported.externalizeRuntimeType(imported.underlying(definition), type.packageName)
            }
        } ?: if (type.packageName == "unsafe" && type.name == "Pointer")
            PointerGoType(InterfaceGoType(emptyList())) else type
        else -> type
    }

    private fun externalizeRuntimeType(type: GoTypeSyntax, importPath: String): GoTypeSyntax = when (type) {
        is NamedGoType -> if (typeDefinitions.containsKey(type.name)) QualifiedGoType(importPath, type.name) else type
        is PointerGoType -> PointerGoType(externalizeRuntimeType(type.element, importPath))
        is SliceGoType -> SliceGoType(externalizeRuntimeType(type.element, importPath))
        is ArrayGoType -> ArrayGoType(type.length?.let(::externalizeRuntimeArrayLength),
            externalizeRuntimeType(type.element, importPath))
        is MapGoType -> MapGoType(externalizeRuntimeType(type.key, importPath), externalizeRuntimeType(type.value, importPath))
        is ChannelGoType -> ChannelGoType(externalizeRuntimeType(type.element, importPath), type.direction)
        is StructGoType -> StructGoType(type.fields.map { field ->
            field.copy(
                type = externalizeRuntimeType(field.type, importPath),
                declaringPackagePath = field.declaringPackagePath ?: importPath,
                packagePath = field.packagePath ?: importPath.takeIf { path ->
                    field.names.any(GoUnicode6::isUnexportedIdentifier) ||
                        field.names.isEmpty() && GoUnicode6.isUnexportedIdentifier(embeddedFieldName(field.type))
                }
            )
        })
        is InterfaceGoType -> InterfaceGoType(type.methods.map { method -> method.copy(
            parameters = method.parameters.map { it.copy(type = externalizeRuntimeType(it.type, importPath)) },
            results = method.results.map { externalizeRuntimeType(it, importPath) },
            packagePath = method.packagePath ?: importPath.takeIf { GoUnicode6.isUnexportedIdentifier(method.name) }
        ) }, type.embeddedTypes.map { externalizeRuntimeType(it, importPath) })
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = externalizeRuntimeType(it.type, importPath)) },
            type.results.map { externalizeRuntimeType(it, importPath) }
        )
        is QualifiedGoType -> type
    }

    private fun externalizeRuntimeArrayLength(expression: Expression): Expression =
        runCatching { integerLiteral(expression) }.getOrNull()?.let { value ->
            LiteralExpression(Token(TokenKind.INT, value.toString(), Position(0, 1, 1)))
        } ?: expression

    private fun externalizeImportedResult(value: Any?, type: GoTypeSyntax, owner: Interpreter): Any? {
        val importPath = owner.packageIdentity ?: return copyForType(value, type)
        if (value is GoInterfaceValue) {
            val dynamicType = owner.externalizeRuntimeType(value.dynamicType, importPath)
            return GoInterfaceValue(dynamicType, copyForType(value.value, dynamicType), value.implementationOwner)
        }
        return copyForType(value, type)
    }

    private fun resolveRuntimeType(type: GoTypeSyntax, env: Environment): GoTypeSyntax = when (type) {
        is NamedGoType -> env.typeBinding(type.name) ?: env.imports.dotPackages.firstOrNull { path ->
            type.name in importedRuntimePackages[path]?.exportedTypeNames.orEmpty()
        }?.let { path -> QualifiedGoType(path, type.name) } ?: type
        is QualifiedGoType -> {
            val path = env.imports.packages[type.packageName] ?: type.packageName
            QualifiedGoType(path, type.name)
        }
        is PointerGoType -> PointerGoType(resolveRuntimeType(type.element, env))
        is SliceGoType -> SliceGoType(resolveRuntimeType(type.element, env))
        is ArrayGoType -> {
            val length = type.length?.let { expression ->
                val value = integerLiteral(expression, env)
                if (value.signum() < 0) throw RuntimeGoError("negative array length")
                LiteralExpression(Token(TokenKind.INT, value.toString(), Position(0, 1, 1)))
            }
            ArrayGoType(length, resolveRuntimeType(type.element, env))
        }
        is MapGoType -> MapGoType(resolveRuntimeType(type.key, env), resolveRuntimeType(type.value, env))
        is ChannelGoType -> ChannelGoType(resolveRuntimeType(type.element, env), type.direction)
        is StructGoType -> StructGoType(type.fields.map { field ->
            field.copy(
                type = resolveRuntimeType(field.type, env),
                declaringPackagePath = field.declaringPackagePath ?: packageIdentity,
                packagePath = field.packagePath ?: packageIdentity.takeIf { path ->
                    field.names.any(GoUnicode6::isUnexportedIdentifier) ||
                        field.names.isEmpty() && GoUnicode6.isUnexportedIdentifier(embeddedFieldName(field.type))
                }
            )
        })
        is InterfaceGoType -> InterfaceGoType(
            type.methods.map { method ->
                method.copy(
                    parameters = method.parameters.map { it.copy(type = resolveRuntimeType(it.type, env)) },
                    results = method.results.map { resolveRuntimeType(it, env) }
                )
            },
            type.embeddedTypes.map { resolveRuntimeType(it, env) }
        )
        is FunctionGoType -> FunctionGoType(
            type.parameters.map { it.copy(type = resolveRuntimeType(it.type, env)) },
            type.results.map { resolveRuntimeType(it, env) }
        )
    }

    private fun defineLocalType(declaration: TypeDeclaration, env: Environment, resolveDefinition: Boolean = true) {
        val identity = synchronized(localTypeIdentities) {
            localTypeIdentities[declaration] ?: "<local:${nextLocalTypeIdentity.incrementAndGet()}:${declaration.name}>".also {
                localTypeIdentities[declaration] = it
            }
        }
        val namedType = NamedGoType(identity)
        if (declaration.name != "_") env.defineType(declaration.name, namedType)
        if (resolveDefinition) typeDefinitions[identity] = resolveRuntimeType(declaration.type, env)
    }

    private fun boxInterface(value: Any?, targetType: GoTypeSyntax): Any? {
        if ((underlying(targetType) as? InterfaceGoType) == null || value == null || value is GoInterfaceValue) return value
        val dynamicType = canonicalAliasType(runtimeType(value) ?: return value)
        return boxInterfaceValue(value, dynamicType)
    }

    private fun boxInterfaceValue(value: Any?, dynamicType: GoTypeSyntax): GoInterfaceValue =
        GoInterfaceValue(canonicalAliasType(dynamicType), copyForType(value, dynamicType), this)

    private fun runtimeType(value: Any?): GoTypeSyntax? = when (value) {
        is GoRuntimeErrorValue -> runtimeErrorValueType
        is GoInterfaceValue -> value.dynamicType
        is GoStruct -> value.namedType?.let { name ->
            value.packagePath?.takeIf { it != packageIdentity }?.let { QualifiedGoType(it, name) } ?: NamedGoType(name)
        } ?: value.staticType
        is GoArray -> value.namedType?.let { runtimeNamedType(it, value.packagePath) } ?: value.type
        is GoSlice -> value.namedType?.let { runtimeNamedType(it, value.packagePath) } ?: value.type ?: SliceGoType(value.elementType)
        is GoChannel -> value.namedType?.let { runtimeNamedType(it, value.packagePath) } ?: value.type ?: ChannelGoType(value.elementType, value.direction)
        is GoPointer -> {
            val pointedType = if (value.isNil || value.rawAddress != null && value.locationIdentity == null) null else runtimeType(value.get())
            val qualifiedPointedType = pointedType as? QualifiedGoType
            val elementType = if (qualifiedPointedType != null &&
                (value.pointeeType == null || namedTypeName(value.pointeeType) == qualifiedPointedType.name))
                qualifiedPointedType else value.pointeeType ?: pointedType
            value.valueType ?: elementType?.let(::PointerGoType)
        }
        is GoNilValue -> value.type
        is GoComplex -> value.type
        is GoFloat -> value.type
        is GoBoolean -> value.type
        is GoInteger -> when {
            value.type == NamedGoType("byte") && !typeDefinitions.containsKey("byte") -> predeclaredUInt8RuntimeType
            value.type == NamedGoType("rune") && !typeDefinitions.containsKey("rune") -> predeclaredIntRuntimeType
            else -> value.type
        }
        is GoRational -> NamedGoType("float64")
        is GoExactComplex -> NamedGoType("complex128")
        is BigInteger -> NamedGoType("int")
        is GoMap -> value.namedType?.let { runtimeNamedType(it, value.packagePath) } ?: value.type ?: MapGoType(value.keyType, value.valueType)
        is FunctionValue -> value.type ?: value.owner.checkedFunctionType(value.function)
        is MethodValue -> value.type ?: value.owner.checkedFunctionType(value.function).let { signature ->
            if (value.owner !== this) value.owner.packageIdentity?.let {
                value.owner.externalizeRuntimeType(signature, it) as FunctionGoType
            } ?: signature else signature
        }
        is RuntimeErrorMethodValue -> value.type ?: FunctionGoType(emptyList(), listOf(NamedGoType("string")))
        is BuiltinValue -> value.type
        is MethodExpressionValue -> value.type
        is Long -> NamedGoType("int")
        is Double -> NamedGoType("float64")
        is GoString -> value.type
        is Boolean -> NamedGoType("bool")
        else -> null
    }

    private fun evaluateMathPackageMember(name: String): Any? = when {
        GoMathPackage.constant(name) != null -> GoRational.decimal(GoMathPackage.constant(name)!!)
        GoMathPackage.functionType(name) != null -> BuiltinValue("math.$name", GoMathPackage.functionType(name))
        else -> throw RuntimeGoError("undefined math identifier $name")
    }

    private fun evaluateUnsafePackageMember(name: String): Any? = when {
        GoUnsafePackage.functionType(name) != null -> BuiltinValue("unsafe.$name", GoUnsafePackage.functionType(name))
        name == "Pointer" -> TypeValue(QualifiedGoType("unsafe", name))
        GoUnsafePackage.constant(name) != null -> GoInteger(GoUnsafePackage.constant(name)!!.toLong(), NamedGoType("int"))
        else -> throw RuntimeGoError("undefined unsafe identifier $name")
    }

    private fun mathCall(name: String, args: List<Any?>): Any? {
        fun count(expected: Int) {
            if (args.size != expected) throw RuntimeGoError("math.$name expects $expected argument(s)")
        }
        fun x() = real(args[0])
        fun y() = real(args[1])
        fun unary(operation: (Double) -> Double): Any { count(1); return operation(x()) }
        fun binary(operation: (Double, Double) -> Double): Any { count(2); return operation(x(), y()) }
        return when (name) {
            "Abs" -> unary(Math::abs)
            "Acos" -> unary(Math::acos)
            "Acosh" -> unary { value ->
                when {
                    value < 1.0 -> Double.NaN
                    value < 2.0 -> {
                        val offset = value - 1.0
                        Math.log1p(offset + Math.sqrt(offset * (offset + 2.0)))
                    }
                    else -> Math.log(value) + Math.log1p(Math.sqrt(1.0 - 1.0 / (value * value)))
                }
            }
            "Asin" -> unary(Math::asin)
            "Asinh" -> unary { value ->
                val magnitude = abs(value)
                val result = if (magnitude < 1.0) Math.log(magnitude + Math.hypot(magnitude, 1.0))
                    else Math.log(magnitude) + Math.log1p(Math.sqrt(1.0 + 1.0 / (magnitude * magnitude)))
                Math.copySign(result, value)
            }
            "Atan" -> unary(Math::atan)
            "Atanh" -> unary { 0.5 * (Math.log1p(it) - Math.log1p(-it)) }
            "Cbrt" -> unary(Math::cbrt)
            "Ceil" -> unary(Math::ceil)
            "Cos" -> unary(Math::cos)
            "Cosh" -> unary(Math::cosh)
            "Exp" -> unary(Math::exp)
            "Exp2" -> unary { 2.0.pow(it) }
            "Expm1" -> unary(Math::expm1)
            "Erf" -> unary(Erf::erf)
            "Erfc" -> unary(Erf::erfc)
            "Floor" -> unary(Math::floor)
            "Gamma" -> unary(Gamma::gamma)
            "Log" -> unary(Math::log)
            "Log10" -> unary(Math::log10)
            "Log1p" -> unary(Math::log1p)
            "Log2" -> unary { Math.log(it) / Math.log(2.0) }
            "Logb" -> unary { value ->
                when {
                    value == 0.0 -> Double.NEGATIVE_INFINITY
                    value.isInfinite() -> Double.POSITIVE_INFINITY
                    value.isNaN() -> value
                    else -> (mathCall("Ilogb", listOf(value)) as Long).toDouble()
                }
            }
            "Sin" -> unary(Math::sin)
            "Sinh" -> unary(Math::sinh)
            "Sqrt" -> unary(Math::sqrt)
            "Tan" -> unary(Math::tan)
            "Tanh" -> unary(Math::tanh)
            "Trunc" -> unary { if (it < 0.0) ceil(it) else floor(it) }
            "Atan2" -> binary(Math::atan2)
            "Copysign" -> binary(Math::copySign)
            "Dim" -> binary { a, b -> Math.max(a - b, 0.0) }
            "Hypot" -> binary(Math::hypot)
            "J0" -> unary { besselJ(0L, it) }
            "J1" -> unary { besselJ(1L, it) }
            "Y0" -> unary { besselY(0, it) }
            "Y1" -> unary { besselY(1, it) }
            "Jn" -> { count(2); besselJ(number(args[0], "math.Jn order"), x()) }
            "Yn" -> { count(2); besselY(number(args[0], "math.Yn order"), x()) }
            "Max" -> binary(Math::max)
            "Min" -> binary(Math::min)
            "Mod" -> binary { a, b -> a % b }
            "Pow" -> binary(Math::pow)
            "Remainder" -> binary(Math::IEEEremainder)
            "IsNaN" -> { count(1); java.lang.Double.isNaN(x()) }
            "IsInf" -> {
                count(2)
                val value = x()
                val sign = number(args[1], "math.IsInf sign")
                java.lang.Double.isInfinite(value) && (sign == 0L || sign < 0L && value < 0.0 || sign > 0L && value > 0.0)
            }
            "Signbit" -> { count(1); java.lang.Double.doubleToRawLongBits(x()) < 0L }
            "Inf" -> { count(1); if (number(args[0], "math.Inf sign") < 0L) Double.NEGATIVE_INFINITY else Double.POSITIVE_INFINITY }
            "NaN" -> { count(0); Double.NaN }
            "Sincos" -> {
                count(1)
                val value = x()
                GoMultiValue(listOf(Math.sin(value), Math.cos(value)))
            }
            "Modf" -> {
                count(1)
                val value = x()
                val integral = if (value < 0.0) ceil(value) else floor(value)
                GoMultiValue(listOf(integral, value - integral))
            }
            "Frexp" -> {
                count(1)
                val value = x()
                when {
                    value == 0.0 || !value.isFinite() -> GoMultiValue(listOf(value, 0L))
                    else -> {
                        val scaled = if (abs(value) < java.lang.Double.MIN_NORMAL) value * 18014398509481984.0 else value
                        val exponent = Math.getExponent(scaled) + 1 - if (scaled != value) 54 else 0
                        GoMultiValue(listOf(Math.scalb(value, -exponent), exponent.toLong()))
                    }
                }
            }
            "Ldexp" -> { count(2); Math.scalb(x(), number(args[1], "math.Ldexp exponent").coerceIn(Int.MIN_VALUE.toLong(), Int.MAX_VALUE.toLong()).toInt()) }
            "Pow10" -> { count(1); 10.0.pow(number(args[0], "math.Pow10 exponent").toDouble()) }
            "Ilogb" -> {
                count(1)
                val value = x()
                when {
                    value == 0.0 -> Int.MIN_VALUE.toLong()
                    value.isInfinite() || value.isNaN() -> Int.MAX_VALUE.toLong()
                    abs(value) < java.lang.Double.MIN_NORMAL -> {
                        val significand = java.lang.Double.doubleToRawLongBits(abs(value)) and 0x000fffffffffffffL
                        (63 - java.lang.Long.numberOfLeadingZeros(significand) - 1074).toLong()
                    }
                    else -> Math.getExponent(value).toLong()
                }
            }
            "Nextafter" -> binary(Math::nextAfter)
            "Lgamma" -> {
                count(1)
                val value = x()
                val (logAbsGamma, sign) = when {
                    value.isNaN() || value.isInfinite() -> value to 1L
                    value == 0.0 -> Double.POSITIVE_INFINITY to 1L
                    value > 0.0 -> Gamma.logGamma(value) to 1L
                    value == floor(value) -> Double.POSITIVE_INFINITY to 1L
                    else -> {
                        val sine = sinPi(value)
                        (Math.log(Math.PI) - Math.log(abs(sine)) - Gamma.logGamma(1.0 - value)) to
                            if (sine < 0.0) -1L else 1L
                    }
                }
                GoMultiValue(listOf(logAbsGamma, sign))
            }
            "Float32bits" -> {
                count(1)
                GoInteger(java.lang.Float.floatToRawIntBits(x().toFloat()).toLong() and 0xffffffffL, NamedGoType("uint32"))
            }
            "Float32frombits" -> {
                count(1)
                GoFloat(java.lang.Float.intBitsToFloat(number(args[0], "math.Float32frombits").toInt()).toDouble(), NamedGoType("float32"))
            }
            "Float64bits" -> { count(1); GoInteger(java.lang.Double.doubleToRawLongBits(x()), NamedGoType("uint64")) }
            "Float64frombits" -> {
                count(1)
                val bits = when (val value = args[0]) {
                    is GoInteger -> value.value
                    is Long -> value
                    is BigInteger -> value.toLong()
                    else -> throw RuntimeGoError("math.Float64frombits requires uint64")
                }
                java.lang.Double.longBitsToDouble(bits)
            }
            else -> throw RuntimeGoError("undefined math function $name")
        }
    }

    private fun besselJ(order: Long, x: Double): Double {
        if (x.isNaN() || x.isInfinite()) return if (x.isNaN()) x else 0.0
        if (order == Long.MIN_VALUE) return 0.0
        val absoluteOrder = abs(order)
        val value = BesselJ.value(absoluteOrder.toDouble(), abs(x))
        val odd = (absoluteOrder and 1L) != 0L
        val negativeSign = (order < 0L && odd) xor (x < 0.0 && odd)
        return if (negativeSign) -value else value
    }

    private fun sinPi(value: Double): Double {
        if (!value.isFinite() || value == 0.0 || abs(value) >= 9_007_199_254_740_992.0) return 0.0
        val integerPart = floor(value)
        val fraction = value - integerPart
        if (fraction == 0.0) return 0.0
        val reducedFraction = if (fraction > 0.5) 1.0 - fraction else fraction
        val positiveSine = sin(Math.PI * reducedFraction)
        val parity = integerPart.toLong() and 1L
        return if (parity == 0L) positiveSine else -positiveSine
    }

    private fun besselY(order: Long, x: Double): Double {
        if (x.isNaN()) return x
        if (x < 0.0) return Double.NaN
        if (x == 0.0) return Double.NEGATIVE_INFINITY
        if (x.isInfinite()) return 0.0
        if (order == Long.MIN_VALUE) return Double.NaN
        var n = abs(order)
        var previous = besselYBase(0, x)
        if (n == 0L) return previous
        var current = besselYBase(1, x)
        var i = 1L
        while (i < n) {
            val next = 2.0 * i / x * current - previous
            previous = current
            current = next
            i++
        }
        return if (order < 0L && (n and 1L) != 0L) -current else current
    }

    private fun besselYBase(order: Int, x: Double): Double {
        if (x > 12.0) {
            val mu = 4.0 * order * order
            val coefficients = DoubleArray(13)
            coefficients[0] = 1.0
            for (k in 1 until coefficients.size) {
                val odd = 2.0 * k - 1.0
                coefficients[k] = coefficients[k - 1] * (mu - odd * odd) / (k * 8.0 * x)
            }
            var p = 0.0
            var q = 0.0
            for (k in coefficients.indices.reversed()) {
                if (k % 2 == 0) p += (if ((k / 2) % 2 == 0) 1.0 else -1.0) * coefficients[k]
                else q += (if (((k - 1) / 2) % 2 == 0) 1.0 else -1.0) * coefficients[k]
            }
            val phase = x - order * Math.PI / 2.0 - Math.PI / 4.0
            return sqrt(2.0 / (Math.PI * x)) * (sin(phase) * p + cos(phase) * q)
        }
        val z = x * x / 4.0
        var term = 1.0
        var harmonic = 0.0
        var sum = 0.0
        var derivativeSum = 0.0
        for (k in 1..160) {
            term *= -z / (k.toDouble() * k)
            harmonic += 1.0 / k
            val harmonicTerm = -harmonic * term
            sum += harmonicTerm
            derivativeSum += (2.0 * k / x) * harmonicTerm
            if (abs(term) < 1e-18 && abs(harmonicTerm) < 1e-18) break
        }
        val j0 = BesselJ.value(0.0, x)
        val j1 = BesselJ.value(1.0, x)
        val logTerm = ln(x / 2.0) + 0.5772156649015328606
        val y0 = 2.0 / Math.PI * (logTerm * j0 + sum)
        if (order == 0) return y0
        return 2.0 / Math.PI * (logTerm * j1 - j0 / x - derivativeSum)
    }

    private fun assertType(value: Any?, target: GoTypeSyntax): GoAssertionResult {
        if (value == null) return GoAssertionResult(zeroValue(target), false, NamedGoType("<nil>"))
        val iface = value as? GoInterfaceValue ?: throw RuntimeGoError("type assertion on non-interface value")
        val targetInterface = underlying(target) as? InterfaceGoType
        val matches = when {
            targetInterface != null -> implementsInterface(iface.dynamicType, targetInterface)
            else -> sameRuntimeType(iface.dynamicType, target)
        }
        val assertedValue = if (!matches) zeroValue(target) else if (targetInterface != null)
            GoInterfaceValue(iface.dynamicType, copyForType(iface.value, iface.dynamicType), iface.implementationOwner)
        else iface.value
        return GoAssertionResult(assertedValue, matches, iface.dynamicType)
    }

    private fun implementsInterface(type: GoTypeSyntax, target: InterfaceGoType): Boolean {
        val required = interfaceMethodsRuntime(target)
        val actual = runtimeMethodSet(type)
        return required.all { (name, signature) -> actual[name]?.let { sameFunctionType(it, signature) } == true }
    }

    private fun interfaceMethodsRuntime(type: GoTypeSyntax, seen: Set<String> = emptySet()): Map<String, FunctionGoType> {
        val iface = underlying(type) as? InterfaceGoType ?: return emptyMap()
        val result = linkedMapOf<String, FunctionGoType>()
        iface.embeddedTypes.forEach { embedded ->
            val key = embedded.toString()
            if (key !in seen) interfaceMethodsRuntime(embedded, seen + key).forEach { (name, signature) ->
                if (result.putIfAbsent(name, signature) != null) throw RuntimeGoError("duplicate interface method $name")
            }
        }
        iface.methods.forEach { method ->
            val key = runtimeInterfaceMethodKey(method)
            if (result.putIfAbsent(key, FunctionGoType(method.parameters, method.results)) != null)
                throw RuntimeGoError("duplicate interface method ${method.name}")
        }
        return result
    }

    private fun runtimeMethodSet(type: GoTypeSyntax): Map<String, FunctionGoType> {
        // A pointer to an interface does not inherit the interface's method set.
        if (type is PointerGoType && underlying(type.element) is InterfaceGoType) return emptyMap()
        val qualified = (type as? PointerGoType)?.element as? QualifiedGoType ?: type as? QualifiedGoType
        if (qualified != null) {
            val owner = importedRuntimePackages[qualified.packageName]
            val foreignType = if (type is PointerGoType) PointerGoType(NamedGoType(qualified.name))
                else NamedGoType(qualified.name)
            if (owner != null) return owner.runtimeMethodSet(foreignType).mapValues { (_, signature) ->
                owner.externalizeRuntimeType(signature, qualified.packageName) as FunctionGoType
            }
        }
        val actual = underlying(type)
        if (actual is InterfaceGoType) return interfaceMethodsRuntime(actual)
        if (type == runtimeErrorValueType) return mapOf(
            "Error" to FunctionGoType(emptyList(), listOf(NamedGoType("string")))
        )
        val result = linkedMapOf<String, FunctionGoType>()
        data class SearchNode(val type: GoTypeSyntax, val pointer: Boolean, val ancestors: Set<String>)
        fun baseType(nodeType: GoTypeSyntax): GoTypeSyntax = underlying((nodeType as? PointerGoType)?.element ?: nodeType)
        fun baseName(nodeType: GoTypeSyntax): String? = when (val base = if (nodeType is PointerGoType) nodeType.element else nodeType) {
            is NamedGoType -> base.name
            else -> null
        }
        var level = listOf(SearchNode(type, type is PointerGoType, emptySet()))
        val blocked = mutableSetOf<String>()
        while (level.isNotEmpty()) {
            val candidates = linkedMapOf<String, MutableList<FunctionGoType>>()
            val next = mutableListOf<SearchNode>()
            level.forEach { node ->
                val nodeUnderlying = baseType(node.type)
                val namedType = (node.type as? PointerGoType)?.element as? QualifiedGoType
                    ?: node.type as? QualifiedGoType
                if (namedType != null && nodeUnderlying !is InterfaceGoType) {
                    val owner = importedRuntimePackages[namedType.packageName]
                    val foreignType = if (node.pointer) PointerGoType(NamedGoType(namedType.name))
                        else NamedGoType(namedType.name)
                    owner?.runtimeMethodSet(foreignType)?.forEach { (name, signature) ->
                        candidates.getOrPut(name) { mutableListOf() } +=
                            owner.externalizeRuntimeType(signature, namedType.packageName) as FunctionGoType
                    }
                }
                when (nodeUnderlying) {
                    is InterfaceGoType -> interfaceMethodsRuntime(nodeUnderlying).forEach { (name, signature) ->
                        candidates.getOrPut(name) { mutableListOf() } += signature
                    }
                    is StructGoType -> {
                        val named = baseName(node.type)
                        if (named != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            val receiverBase = if (receiverType is PointerGoType) receiverType.element else receiverType
                            if (receiverBase != NamedGoType(named) || receiverType is PointerGoType && !node.pointer) return@methodLoop
                            candidates.getOrPut(runtimePackageMethodKey(method.name)) { mutableListOf() } += checkedFunctionType(method)
                        }
                        nodeUnderlying.fields.filter { it.names.isEmpty() }.forEach { field ->
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
                        val named = baseName(node.type)
                        if (named != null) methods.values.forEach methodLoop@{ method ->
                            val receiverType = method.receiver?.type ?: return@methodLoop
                            val receiverBase = if (receiverType is PointerGoType) receiverType.element else receiverType
                            if (receiverBase != NamedGoType(named) || receiverType is PointerGoType && !node.pointer) return@methodLoop
                            candidates.getOrPut(runtimePackageMethodKey(method.name)) { mutableListOf() } += checkedFunctionType(method)
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

    private fun sameFunctionType(left: FunctionGoType, right: FunctionGoType): Boolean =
        left.parameters.size == right.parameters.size && left.results.size == right.results.size &&
            left.parameters.zip(right.parameters).all { (a, b) -> sameRuntimeType(a.type, b.type) && a.variadic == b.variadic } &&
            left.results.zip(right.results).all { (a, b) -> sameRuntimeType(a, b) }

    private fun methodKey(type: GoTypeSyntax, name: String): String {
        val base = if (type is PointerGoType) type.element else type
        return "${(base as? NamedGoType)?.name ?: base}.$name"
    }

    private fun runtimePackageMethodKey(name: String): String = if (GoUnicode6.isExportedIdentifier(name)) name
        else "${packageIdentity ?: "<package>"}:$name"

    private fun runtimeInterfaceMethodKey(method: InterfaceMethodSyntax): String =
        if (GoUnicode6.isExportedIdentifier(method.name)) method.name
        else "${method.packagePath ?: packageIdentity ?: "<package>"}:${method.name}"

    private fun dereference(value: Any?): Any? = if (value is GoPointer) value.get() else value

    private fun copyValue(value: Any?): Any? = when (value) {
        is GoStruct -> GoStruct(
            value.fields.mapValuesTo(linkedMapOf()) { copyValue(it.value) },
            value.namedType, value.fieldTypes, value.embeddedFields, value.staticType, value.packagePath
        )
        is GoArray -> GoArray(value.elementType, value.values.mapTo(mutableListOf(), ::copyValue), value.namedType, value.type, value.packagePath)
        is GoInterfaceValue -> GoInterfaceValue(value.dynamicType, copyValue(value.value), value.implementationOwner)
        else -> value
    }

    private fun copyForType(value: Any?, type: GoTypeSyntax): Any? {
        val actual = underlying(type)
        val copied = if (value == null) when (actual) {
            is PointerGoType -> GoPointer.nil(actual.element, type)
            is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType -> GoNilValue(type)
            else -> null
        } else if (value is GoBoolean && actual == NamedGoType("bool")) GoBoolean(value.value, type)
        else if (value is Boolean && actual == NamedGoType("bool")) GoBoolean(value, type)
        else if (value is GoString && actual == NamedGoType("string")) GoString(value.bytes.copyOf(), type)
        else if (value is GoPointer && actual is PointerGoType) value.retype(actual.element, type)
        else if (value is GoArray && actual is ArrayGoType)
            GoArray(actual.element, value.values.mapTo(mutableListOf()) { copyForType(it, actual.element) },
                namedTypeName(type), type, namedTypePackage(type))
        else if (value is GoSlice && actual is SliceGoType) value.retype(actual.element, namedTypeName(type), type, namedTypePackage(type))
        else if (value is GoMap && actual is MapGoType) value.retype(actual.key, actual.value, namedTypeName(type), type, namedTypePackage(type))
        else if (value is GoChannel && actual is ChannelGoType)
            value.retype(actual.element, actual.direction, namedTypeName(type), type, namedTypePackage(type))
        else if (value is FunctionValue && actual is FunctionGoType) value.copy(type = type)
        else if (value is MethodValue && actual is FunctionGoType) value.copy(type = type)
        else if (value is RuntimeErrorMethodValue && actual is FunctionGoType) value.copy(type = type)
        else if (value is MethodExpressionValue && actual is FunctionGoType) value.copy(type = type)
        else if (value is GoStruct && actual is StructGoType) {
            val fields = linkedMapOf<String, Any?>()
            val fieldTypes = linkedMapOf<String, GoTypeSyntax>()
            val embeddedFields = linkedSetOf<String>()
            structFieldSlots(actual).forEach { field ->
                if (field.name.isEmpty()) return@forEach
                fields[field.storageKey] = copyForType(value.fields[field.storageKey], field.type)
                fieldTypes[field.storageKey] = field.type
                if (field.embedded) embeddedFields += field.storageKey
            }
            GoStruct(fields, namedTypeName(type), fieldTypes, embeddedFields, type, namedTypePackage(type))
        }
        else if ((value is BigInteger || value is GoRational || value is GoExactComplex) && actual is InterfaceGoType) defaultConstantValue(value)
        else if (actual is NamedGoType && (actual.name in integerTypeNames || actual.name in setOf("complex64", "complex128", "float32", "float64"))) convert(type, value)
        else copyValue(value)
        return boxInterface(copied, type)
    }

    private fun index(
        receiver: Any?,
        rawIndex: Any?,
        indexExpression: Expression? = null,
        env: Environment? = null
    ): Any? {
        return when (receiver) {
            is GoSlice -> receiver.get(collectionIndex(rawIndex, "index"))
            is GoArray -> arrayElement(receiver, rawIndex)
            is GoPointer -> {
                val array = receiver.get() as? GoArray ?: throw RuntimeGoError("index requires pointer to array")
                arrayElement(array, rawIndex)
            }
            is GoMap -> {
                val key = if (underlying(receiver.keyType) is InterfaceGoType && indexExpression != null && env != null)
                    defaultRuneValue(rawIndex, indexExpression, env) else rawIndex
                mapValue(receiver, mapKey(key, receiver.keyType))
            }
            is GoNilValue -> (underlying(receiver.type) as? MapGoType)?.let { mapType ->
                val key = if (underlying(mapType.key) is InterfaceGoType && indexExpression != null && env != null)
                    defaultRuneValue(rawIndex, indexExpression, env) else rawIndex
                mapKey(key, mapType.key)
                zeroValue(mapType.value)
            } ?: throw RuntimeGoError("cannot index this value")
            is GoStruct -> {
                val field = rawIndex as? String ?: throw RuntimeGoError("struct field must be a name")
                if (receiver.fields.containsKey(field)) receiver.fields[field] else throw RuntimeGoError("unknown struct field: $field")
            }
            is GoString -> {
                val i = collectionIndex(rawIndex, "index")
                if (i !in receiver.bytes.indices) throw RuntimeGoError("string index out of range")
                GoInteger((receiver.bytes[i].toInt() and 0xff).toLong(), NamedGoType("byte"))
            }
            else -> throw RuntimeGoError("cannot index this value")
        }
    }

    private fun arrayElement(array: GoArray, rawIndex: Any?): Any? {
        val index = collectionIndex(rawIndex, "index")
        if (index !in array.values.indices) throw RuntimeGoError("array index out of range")
        return array.values[index]
    }

    private fun setArrayElement(array: GoArray, rawIndex: Any?, value: Any?) {
        val index = collectionIndex(rawIndex, "index")
        if (index !in array.values.indices) throw RuntimeGoError("array index out of range")
        val assigned = copyForType(value, array.elementType)
        array.values[index] = preserveAggregateStorage(array.values[index], assigned, array.elementType)
    }

    private fun addressableCell(value: Any?, type: GoTypeSyntax): GoPointer = GoPointer.cell(value, type) { previous, assigned ->
        preserveAggregateStorage(previous, copyForType(assigned, type), type)
    }

    private fun sliceArray(array: GoArray, low: Int, high: Int, max: Int): GoSlice {
        if (low < 0 || high < low || max < high || max > array.values.size)
            throw RuntimeGoError("slice bounds out of range")
        return GoSlice(array.elementType, array.values, low, high - low, max - low,
            type = SliceGoType(array.elementType))
    }

    private fun slice(receiver: Any?, lowValue: Any?, highValue: Any?): Any? {
        val low = lowValue?.let { collectionIndex(it, "slice index") } ?: 0
        return when (receiver) {
            is GoSlice -> {
                val high = highValue?.let { collectionIndex(it, "slice index") } ?: receiver.length
                receiver.subSlice(low, high, receiver.capacity)
            }
            is GoArray -> {
                val high = highValue?.let { collectionIndex(it, "slice index") } ?: receiver.values.size
                sliceArray(receiver, low, high, receiver.values.size)
            }
            is GoPointer -> {
                val array = receiver.get() as? GoArray ?: throw RuntimeGoError("slice requires pointer to array")
                val high = highValue?.let { collectionIndex(it, "slice index") } ?: array.values.size
                sliceArray(array, low, high, array.values.size)
            }
            is GoString -> {
                val bytes = receiver.bytes
                val high = highValue?.let { collectionIndex(it, "slice index") } ?: bytes.size
                if (low < 0 || high < low || high > bytes.size) throw RuntimeGoError("string slice bounds out of range")
                GoString(bytes.copyOfRange(low, high), receiver.type)
            }
            is GoNilValue -> if (underlying(receiver.type) is SliceGoType) {
                val high = highValue?.let { collectionIndex(it, "slice index") } ?: 0
                if (low != 0 || high != 0) throw RuntimeGoError("slice bounds out of range")
                receiver
            } else throw RuntimeGoError("cannot slice this value")
            else -> throw RuntimeGoError("cannot slice this value")
        }
    }

    private fun convert(type: GoTypeSyntax, value: Any?): Any? = when (val target = underlying(type)) {
        is PointerGoType -> when (value) {
            is GoPointer -> value.retype(target.element, type)
            is GoInteger -> if (isUnsafePointerType(type)) unsafePointer(value.value, target.element, type)
                else throw RuntimeGoError("cannot convert value to $type")
            is Long -> if (isUnsafePointerType(type)) unsafePointer(value, target.element, type)
                else throw RuntimeGoError("cannot convert value to $type")
            null, is GoNilValue -> GoPointer.nil(target.element, type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is ArrayGoType -> {
            if (value !is GoArray) throw RuntimeGoError("cannot convert value to $type")
            GoArray(target.element, value.values.mapTo(mutableListOf()) { copyForType(it, target.element) },
                namedTypeName(type), type, namedTypePackage(type))
        }
        is SliceGoType -> {
            if (value is GoString && (isByteElementType(target.element) || isRuneElementType(target.element))) {
                if (value.bytes.isEmpty()) GoNilValue(type)
                else {
                    val converted = if (isByteElementType(target.element))
                        value.bytes.map { (it.toInt() and 0xff).toLong() }
                    else decodeUtf8Runes(value.bytes).map(Int::toLong)
                    val backing = converted.mapTo(mutableListOf()) { copyForType(it, target.element) }
                    GoSlice(target.element, backing, 0, backing.size, backing.size, namedTypeName(type), type,
                        namedTypePackage(type))
                }
            } else if (value is GoSlice) value.retype(target.element, namedTypeName(type), type, namedTypePackage(type))
            else if (value == null || value is GoNilValue && underlying(value.type) is SliceGoType) GoNilValue(type)
            else throw RuntimeGoError("cannot convert value to $type")
        }
        is MapGoType -> when (value) {
            is GoMap -> value.retype(target.key, target.value, namedTypeName(type), type, namedTypePackage(type))
            null, is GoNilValue -> GoNilValue(type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is ChannelGoType -> when (value) {
            is GoChannel -> value.retype(target.element, target.direction, namedTypeName(type), type, namedTypePackage(type))
            null, is GoNilValue -> GoNilValue(type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is FunctionGoType -> when (value) {
            is FunctionValue -> value.copy(type = type)
            is MethodValue -> value.copy(type = type)
            is RuntimeErrorMethodValue -> value.copy(type = type)
            is MethodExpressionValue -> value.copy(type = type)
            is BuiltinValue -> value.copy(type = type)
            null, is GoNilValue -> GoNilValue(type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is InterfaceGoType -> boxInterface(value, type)
        is StructGoType -> when (value) {
            is GoStruct -> copyForType(value, type)
            else -> throw RuntimeGoError("cannot convert value to $type")
        }
        is NamedGoType -> when (target.name) {
            "string" -> when (value) {
                is GoString -> GoString(value.bytes.copyOf(), type)
                is Long -> GoString(encodeGoCodePoint(value), type)
                is BigInteger -> GoString(encodeGoCodePoint(value), type)
                is GoInteger -> GoString(encodeGoCodePoint(integerValue(value, "string conversion")), type)
                is GoSlice -> when {
                    isByteElementType(value.elementType) -> GoString(value.toList().map { number(it, "string conversion").toInt().toByte() }.toByteArray(), type)
                    isRuneElementType(value.elementType) -> GoString(value.toList().flatMap {
                        encodeGoCodePoint(number(it, "string conversion")).toList()
                    }.toByteArray(), type)
                    else -> throw RuntimeGoError("cannot convert slice to string")
                }
                is GoNilValue -> if (isByteOrRuneSlice(value.type)) GoString(byteArrayOf(), type) else throw RuntimeGoError("cannot convert to string")
                else -> throw RuntimeGoError("cannot convert to string")
            }
            "bool" -> GoBoolean(booleanValue(value, "bool conversion"), type)
            "float32", "float64" -> when (value) {
                is Long -> GoFloat(if (target.name == "float32") GoRational.of(BigInteger.valueOf(value)).toFloat().toDouble() else value.toDouble(), type)
                is BigInteger -> GoFloat(if (target.name == "float32") GoRational.of(value).toFloat().toDouble() else value.toDouble(), type)
                is GoRational -> GoFloat(if (target.name == "float32") value.toFloat().toDouble() else value.toDouble(), type)
                is GoExactComplex -> {
                    if (value.imaginary.numerator.signum() != 0) throw RuntimeGoError("cannot convert complex value to float")
                    GoFloat(if (target.name == "float32") value.real.toFloat().toDouble() else value.real.toDouble(), type)
                }
                is GoComplex -> {
                    if (value.imaginary != 0.0) throw RuntimeGoError("cannot convert complex value to float")
                    GoFloat(if (target.name == "float32") value.real.toFloat().toDouble() else value.real, type)
                }
                is GoInteger -> GoFloat(if (target.name == "float32") GoRational.of(integerValue(value, "float conversion")).toFloat().toDouble() else integerAsDouble(value), type)
                is Double -> GoFloat(if (target.name == "float32") value.toFloat().toDouble() else value, type)
                is GoFloat -> GoFloat(if (target.name == "float32") value.value.toFloat().toDouble() else value.value, type)
                else -> throw RuntimeGoError("cannot convert to float")
            }
            "complex64", "complex128" -> {
                val narrow = target.name == "complex64"
                fun exactFloat(integer: BigInteger) = if (narrow) GoRational.of(integer).toFloat().toDouble() else integer.toDouble()
                val real = when (value) {
                    is Long -> exactFloat(BigInteger.valueOf(value))
                    is BigInteger -> exactFloat(value)
                    is GoRational -> if (narrow) value.toFloat().toDouble() else value.toDouble()
                    is GoExactComplex -> if (narrow) value.real.toFloat().toDouble() else value.real.toDouble()
                    is GoInteger -> exactFloat(integerValue(value, "complex conversion"))
                    is Double -> value
                    is GoFloat -> value.value
                    is GoComplex -> value.real
                    else -> throw RuntimeGoError("cannot convert to complex")
                }
                val imaginary = when (value) {
                    is GoComplex -> value.imaginary
                    is GoExactComplex -> if (target.name == "complex64") value.imaginary.toFloat().toDouble() else value.imaginary.toDouble()
                    else -> 0.0
                }
                val convertedType = type
                if (narrow) GoComplex(real.toFloat().toDouble(), imaginary.toFloat().toDouble(), convertedType)
                else GoComplex(real, imaginary, convertedType)
            }
            in integerTypeNames -> {
                val converted = when (value) {
                    is GoPointer -> if (underlying(type) == NamedGoType("uintptr")) unsafeAddress(value)
                        else throw RuntimeGoError("cannot convert pointer to $type")
                    is Long -> value
                    is GoInteger -> value.value
                    is BigInteger -> value.toLong()
                    is GoRational -> value.integerValue("integer conversion").toLong()
                    is GoExactComplex -> {
                        if (value.imaginary.numerator.signum() != 0) throw RuntimeGoError("cannot convert complex value to integer")
                        value.real.integerValue("integer conversion").toLong()
                    }
                    is GoComplex -> {
                        if (value.imaginary != 0.0 || !value.real.isFinite() || value.real % 1.0 != 0.0)
                            throw RuntimeGoError("cannot convert complex value to integer")
                        value.real.toLong()
                    }
                    is Double -> value.toLong()
                    is GoFloat -> value.value.toLong()
                    else -> throw RuntimeGoError("cannot convert to integer")
                }
                GoInteger(wrapInteger(converted, type), type)
            }
            else -> value
        }
        else -> value
    }

    private fun isByteElementType(type: GoTypeSyntax): Boolean =
        canonicalAliasType(type) == predeclaredUInt8RuntimeType
    private fun isByteOrRuneSlice(type: GoTypeSyntax): Boolean =
        (underlying(type) as? SliceGoType)?.element?.let { isByteElementType(it) || isRuneElementType(it) } == true

    private fun isPredeclaredRuneType(type: GoTypeSyntax): Boolean =
        canonicalAliasType(type) == predeclaredIntRuntimeType
    private fun isRuneElementType(type: GoTypeSyntax): Boolean =
        canonicalAliasType(type) == predeclaredIntRuntimeType

    private fun isUnsignedInteger(type: GoTypeSyntax): Boolean = (underlying(type) as? NamedGoType)?.name in
        setOf("#predeclared-uint8", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte")

    private fun isUnsafePointerType(type: GoTypeSyntax) = type == QualifiedGoType("unsafe", "Pointer")

    private fun unsafeAddress(pointer: GoPointer): Long {
        if (pointer.isNil) return 0L
        pointer.rawAddress?.let { return it }
        val identity = pointer.locationIdentity ?: throw RuntimeGoError("pointer has no address")
        synchronized(unsafeAddressByLocation) {
            return unsafeAddressByLocation.getOrPut(identity) {
                val address = nextUnsafeAddress
                nextUnsafeAddress = Math.addExact(nextUnsafeAddress, 8L)
                unsafePointerByAddress[address] = pointer
                registerUnsafeSubaddresses(pointer, address, mutableSetOf())
                address
            }
        }
    }

    private fun registerUnsafeSubaddresses(pointer: GoPointer, base: Long, ancestors: MutableSet<String>) {
        val identity = pointer.locationIdentity ?: return
        unsafeAddressByLocation.putIfAbsent(identity, base)
        unsafePointerByAddress.putIfAbsent(base, pointer)
        val type = pointer.pointeeType?.let(::underlying) ?: return
        val addressable = runCatching { pointer.get() }.getOrNull()
        val arrayLength: (Expression) -> BigInteger = { integerLiteral(it, globals) }
        when {
            type is StructGoType && addressable is GoStruct -> {
                val key = type.toString()
                if (!ancestors.add(key)) return
                type.fields.forEach { field ->
                    val names = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
                    names.filter { it.isNotEmpty() && it != "_" }.forEach { name ->
                        val offset = GoUnsafePackage.fieldOffset(type, name, ::underlying, arrayLength)?.first ?: return@forEach
                        val child = addressable.pointer(name)
                        val childAddress = Math.addExact(base, offset)
                        if (child.locationIdentity != null) unsafeAddressByLocation.putIfAbsent(child.locationIdentity!!, childAddress)
                        unsafePointerByAddress.putIfAbsent(childAddress, child)
                        registerUnsafeSubaddresses(child, childAddress, ancestors)
                    }
                }
                ancestors.remove(key)
            }
            type is ArrayGoType && addressable is GoArray -> {
                val count = type.length?.let(arrayLength)?.intValueExact() ?: return
                val elementLayout = GoUnsafePackage.layout(type.element, ::underlying, arrayLength)
                repeat(minOf(count, addressable.values.size)) { index ->
                    val child = addressable.pointerAt(index)
                    val childAddress = Math.addExact(base, Math.multiplyExact(index.toLong(), elementLayout.size))
                    if (child.locationIdentity != null) unsafeAddressByLocation.putIfAbsent(child.locationIdentity!!, childAddress)
                    unsafePointerByAddress.putIfAbsent(childAddress, child)
                    registerUnsafeSubaddresses(child, childAddress, ancestors)
                }
            }
        }
    }

    private fun unsafePointer(address: Long, elementType: GoTypeSyntax, pointerType: GoTypeSyntax): GoPointer {
        if (address == 0L) return GoPointer.nil(elementType, pointerType)
        synchronized(unsafeAddressByLocation) {
            return unsafePointerByAddress[address]?.retype(elementType, pointerType)
                ?: GoPointer.address(address, elementType, pointerType)
        }
    }

    private fun integerBitWidth(type: GoTypeSyntax): Int = when ((underlying(type) as? NamedGoType)?.name) {
        "#predeclared-uint8", "int8", "uint8", "byte" -> 8
        "int16", "uint16" -> 16
        "int32", "uint32" -> 32
        else -> 64
    }

    private fun wrapInteger(value: Long, type: GoTypeSyntax): Long {
        val bits = integerBitWidth(type)
        if (bits == Long.SIZE_BITS) return value
        val mask = (1L shl bits) - 1
        val narrowed = value and mask
        return if (!isUnsignedInteger(type) && narrowed.and(1L shl (bits - 1)) != 0L) narrowed or mask.inv() else narrowed
    }

    private fun integerAsDouble(value: GoInteger): Double = integerValue(value, "float conversion").toDouble()

    private fun append(args: List<Any?>, expandString: Boolean = false): Any? {
        val first = args.firstOrNull()
        val values = args.drop(1)
        val expandsEmptyString = expandString && values.singleOrNull() is GoString &&
            (values.single() as GoString).bytes.isEmpty()
        if (first is GoNilValue && (values.isEmpty() || expandsEmptyString)) return first
        val slice = when (first) {
            is GoSlice -> first
            is GoNilValue -> (underlying(first.type) as? SliceGoType)?.let {
                GoSlice(it.element, mutableListOf(), 0, 0, 0,
                    namedTypeName(first.type), first.type, namedTypePackage(first.type))
            } ?: throw RuntimeGoError("append requires a slice")
            else -> throw RuntimeGoError("append requires a slice")
        }
        if (expandString && values.singleOrNull() is GoString) {
            if (!isByteElementType(slice.elementType)) throw RuntimeGoError("append string expansion requires a byte slice")
            return slice.append((values.single() as GoString).bytes.map { (it.toInt() and 0xff).toLong() })
        }
        return slice.append(values)
    }

    private fun copy(args: List<Any?>): Long {
        val destinationValue = args.getOrNull(0)
        val destination = destinationValue as? GoSlice
        val sourceValue = args.getOrNull(1)
        val inferredDestinationType = when (sourceValue) {
            is GoSlice -> SliceGoType(sourceValue.elementType)
            is GoNilValue -> underlying(sourceValue.type).takeIf { it is SliceGoType }
            is GoString -> SliceGoType(NamedGoType("byte"))
            else -> null
        }
        val destinationType = when (destinationValue) {
            is GoSlice -> SliceGoType(destinationValue.elementType)
            is GoNilValue -> underlying(destinationValue.type).takeIf { it is SliceGoType }
            null -> inferredDestinationType
            else -> throw RuntimeGoError("copy destination must be a slice")
        } as? SliceGoType ?: throw RuntimeGoError("copy destination must be a slice")
        val values = when (val source = sourceValue) {
            is GoSlice -> {
                if (!sameRuntimeType(destinationType.element, source.elementType)) throw RuntimeGoError("copy slice element types do not match")
                source.toList()
            }
            is GoNilValue -> {
                val sourceType = underlying(source.type) as? SliceGoType
                    ?: throw RuntimeGoError("copy source must be a slice or string")
                if (!sameRuntimeType(destinationType.element, sourceType.element)) throw RuntimeGoError("copy slice element types do not match")
                emptyList()
            }
            null -> emptyList()
            is GoString -> {
                if (!isByteElementType(destinationType.element)) throw RuntimeGoError("copy from string requires a byte slice")
                source.bytes.map { (it.toInt() and 0xff).toLong() }
            }
            else -> throw RuntimeGoError("copy source must be a slice or string")
        }
        if (destination == null) return 0L
        val count = minOf(destination.length, values.size)
        repeat(count) { destination.set(it, values[it]) }
        return count.toLong()
    }

    private fun delete(args: List<Any?>) {
        val map = args.getOrNull(0) as? GoMap ?: when (val nilMap = args.getOrNull(0)) {
            // Go 1.0 specifies a run-time panic here; later Go versions made this a no-op.
            is GoNilValue -> if (underlying(nilMap.type) is MapGoType)
                throw RuntimeGoError("delete from nil map") else throw RuntimeGoError("delete requires a map")
            else -> throw RuntimeGoError("delete requires a map")
        }
        map.values.remove(mapKey(args.getOrNull(1), map.keyType))
    }

    private fun mapKey(value: Any?, keyType: GoTypeSyntax? = null): GoMapKey {
        val typedValue = keyType?.let { copyForType(value, it) } ?: value
        if (!runtimeComparable(typedValue)) throw RuntimeGoError("hash of unhashable type")
        return GoMapKey(copyValue(typedValue))
    }

    private fun mapValue(map: GoMap, key: GoMapKey): Any? =
        copyForType(if (map.values.containsKey(key)) map.values[key] else map.elementZero, map.valueType)

    private fun literal(token: Token): Any = when (token.kind) {
        TokenKind.INT -> integer(token.lexeme)
        TokenKind.FLOAT -> runCatching { GoRational.decimal(token.lexeme) }.getOrElse { throw RuntimeGoError("invalid float ${token.lexeme}") }
        TokenKind.IMAG -> GoExactComplex(GoRational.ZERO, imaginaryPart(token.lexeme.removeSuffix("i")))
        TokenKind.CHAR -> BigInteger.valueOf(decodeGoCharacterLiteral(token.lexeme).toLong())
        TokenKind.STRING -> decodeString(token.lexeme)
        else -> throw RuntimeGoError("invalid literal")
    }

    private fun integer(text: String): BigInteger = try {
        when {
            text.startsWith("0x", true) -> BigInteger(text.substring(2), 16)
            text.length > 1 && text.startsWith("0") -> BigInteger(text.substring(1), 8)
            else -> BigInteger(text, 10)
        }
    } catch (_: Exception) { throw RuntimeGoError("invalid integer literal: $text") }

    private suspend fun unary(operator: TokenKind, value: Any?): Any? = when (operator) {
        TokenKind.ADD -> value
        TokenKind.SUB -> when (value) {
            is GoRational -> value.negate()
            is GoExactComplex -> GoExactComplex(value.real.negate(), value.imaginary.negate())
            is BigInteger -> value.negate()
            is Long -> -value
            is GoInteger -> value.copy(value = wrapInteger(-value.value, value.type))
            is Double -> -value
            is GoFloat -> value.copy(value = -value.value)
            is GoComplex -> value.copy(real = -value.real, imaginary = -value.imaginary)
            else -> typeError("unary -", value)
        }
        TokenKind.NOT -> {
            val result = !booleanValue(value, "!")
            if (value is GoBoolean) GoBoolean(result, value.type) else result
        }
        TokenKind.XOR -> when (value) {
            is BigInteger -> value.not()
            is GoInteger -> value.copy(value = wrapInteger(value.value.inv(), value.type))
            else -> number(value, "^").inv()
        }
        TokenKind.AND -> throw RuntimeGoError("pointers are not implemented")
        TokenKind.MUL -> throw RuntimeGoError("pointer dereference is not implemented")
        TokenKind.ARROW -> when (value) {
            is GoChannel -> value.receive()
            is GoNilValue -> if (underlying(value.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("receive from non-channel")
            else -> throw RuntimeGoError("receive from non-channel")
        }
        else -> value
    }

    private suspend fun receiveResult(value: Any?): GoReceiveResult = when (value) {
        is GoChannel -> value.receive()
        is GoNilValue -> if (underlying(value.type) is ChannelGoType) awaitCancellation() else throw RuntimeGoError("receive from non-channel")
        else -> throw RuntimeGoError("receive from non-channel")
    }

    private fun make(args: List<Any?>): Any? {
        val type = underlying((args.firstOrNull() as? TypeValue)?.type ?: throw RuntimeGoError("make requires a type"))
        return when (type) {
            is ChannelGoType -> {
                if (args.size !in 1..2) throw RuntimeGoError("make channel accepts one or two arguments")
                val capacity = args.getOrNull(1)?.let { makeSize(it, "channel capacity") } ?: 0
                if (capacity < 0) throw RuntimeGoError("negative channel capacity")
                val requestedType = (args.first() as TypeValue).type
                GoChannel(type.element, capacity, namedTypeName(requestedType), requestedType, type.direction,
                    packagePath = namedTypePackage(requestedType))
            }
            is SliceGoType -> {
                if (args.size !in 2..3) throw RuntimeGoError("make slice requires length and optional capacity")
                val length = args.getOrNull(1)?.let { makeSize(it, "slice length") }
                    ?: throw RuntimeGoError("make slice requires a length")
                val capacity = args.getOrNull(2)?.let { makeSize(it, "slice capacity") } ?: length
                if (length < 0 || capacity < length) throw RuntimeGoError("invalid slice length or capacity")
                val requestedType = (args.first() as TypeValue).type
                GoSlice(type.element, zeroedSliceBacking(capacity, type.element), 0, length, capacity,
                    namedTypeName(requestedType), requestedType, namedTypePackage(requestedType))
            }
            is MapGoType -> {
                if (args.size !in 1..2) throw RuntimeGoError("make map accepts one or two arguments")
                val size = args.getOrNull(1)?.let { makeSize(it, "map size hint") } ?: 0
                if (size < 0) throw RuntimeGoError("negative map size hint")
                val requestedType = (args.first() as TypeValue).type
                GoMap(type.key, type.value, zeroValue(type.value), linkedMapOf(),
                    namedTypeName(requestedType), requestedType, namedTypePackage(requestedType))
            }
            else -> throw RuntimeGoError("make for this type is not implemented")
        }
    }

    private fun makeSize(value: Any?, operation: String): Int {
        val size = number(value, operation)
        if (size < Int.MIN_VALUE || size > Int.MAX_VALUE) throw RuntimeGoError("$operation out of range")
        return size.toInt()
    }

    private fun zeroedSliceBacking(capacity: Int, elementType: GoTypeSyntax): MutableList<Any?> = try {
        MutableList(capacity) { zeroValue(elementType) }
    } catch (_: OutOfMemoryError) {
        throw RuntimeGoError("slice allocation failed")
    }

    private fun expandValues(values: List<Any?>, targets: Int): List<Any?> {
        if (values.size == 1) {
            val only = values.single()
            if (only is GoAssertionResult && targets == 2) return listOf(only.value, only.ok)
            if (only is GoAssertionResult) return listOf(only.value)
            if (only is GoReceiveResult && targets == 2) return listOf(only.value, only.ok)
            if (only is GoReceiveResult) return listOf(only.value)
            if (only is MapLookupResult && targets == 2) return listOf(only.value, only.ok)
            if (only is MapLookupResult) return listOf(only.value)
            if (only is GoMultiValue) return only.values
            return listOf(only)
        }
        return values.map { when (it) { is GoReceiveResult -> it.value; is MapLookupResult -> it.value; else -> it } }
    }

    private fun zeroValue(type: GoTypeSyntax): Any? = when (val actual = underlying(type)) {
        is NamedGoType -> when (actual.name) {
            "bool" -> GoBoolean(false, type)
            "string" -> GoString(byteArrayOf(), type)
            in integerTypeNames -> GoInteger(0L, type)
            "float32", "float64" -> GoFloat(0.0, type)
            "complex64", "complex128" -> GoComplex(0.0, 0.0, type)
            else -> null
        }
        is ArrayGoType -> {
            val length = actual.length?.let {
                val value = try { integerLiteral(it).intValueExact() }
                catch (_: ArithmeticException) { throw RuntimeGoError("array length out of range") }
                if (value < 0) throw RuntimeGoError("negative array length")
                value
            } ?: 0
            GoArray(actual.element, MutableList(length) { zeroValue(actual.element) }, namedTypeName(type), type,
                namedTypePackage(type))
        }
        is StructGoType -> {
            val fields = linkedMapOf<String, Any?>()
            val fieldTypes = linkedMapOf<String, GoTypeSyntax>()
            structFieldSlots(actual).forEach { field ->
                if (field.name.isNotEmpty()) {
                    fields[field.storageKey] = zeroValue(field.type)
                    fieldTypes[field.storageKey] = field.type
                }
            }
            GoStruct(fields, namedTypeName(type), fieldTypes,
                structFieldSlots(actual).filter { it.embedded }.mapTo(linkedSetOf()) { it.storageKey }, type,
                namedTypePackage(type))
        }
        is SliceGoType, is MapGoType, is ChannelGoType, is FunctionGoType -> GoNilValue(type)
        is PointerGoType -> GoPointer.nil(actual.element, type)
        else -> null
    }

    private fun embeddedFieldName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> type.name
        is PointerGoType -> embeddedFieldName(type.element)
        else -> ""
    }

    private fun namedTypeName(type: GoTypeSyntax): String? = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> type.name
        else -> null
    }

    private fun namedTypePackage(type: GoTypeSyntax): String? = when (type) {
        is QualifiedGoType -> type.packageName
        is NamedGoType -> packageIdentity
        else -> packageIdentity
    }

    private fun unexportedFieldPackagePath(field: StructFieldSyntax, name: String): String? {
        if (!GoUnicode6.isUnexportedIdentifier(name)) return null
        val embeddedType = if (field.names.isEmpty()) field.type.let {
            if (it is PointerGoType) it.element else it
        } else null
        return field.packagePath ?: (embeddedType as? QualifiedGoType)?.packageName ?: packageIdentity
    }

    private fun structFieldSlots(type: StructGoType): List<RuntimeStructField> =
        type.fields.flatMap { field ->
            val embedded = field.names.isEmpty()
            val names = field.names.ifEmpty { listOf(embeddedFieldName(field.type)) }
            names.map { Triple(it, field.type, embedded) }
        }.mapIndexed { index, (name, fieldType, embedded) ->
            RuntimeStructField(name, if (name == "_") "\u0000blank:$index" else name, fieldType, embedded)
        }

    private fun integerLiteral(expression: Expression, env: Environment? = null): BigInteger = when (expression) {
        is LiteralExpression -> integer(expression.token.lexeme)
        is NameExpression -> when (val value = env?.getOrNull(expression.name) ?: globals.getOrNull(expression.name)) {
            is BigInteger -> value
            is Long -> BigInteger.valueOf(value)
            is GoInteger -> integerValue(value, "array length")
            else -> throw RuntimeGoError("array length is not a constant integer expression")
        }
        is ParenthesizedExpression -> integerLiteral(expression.expression, env)
        is UnaryExpression -> when (expression.operator) {
            TokenKind.ADD -> integerLiteral(expression.operand, env)
            TokenKind.SUB -> integerLiteral(expression.operand, env).negate()
            TokenKind.XOR -> {
                val value = integerLiteral(expression.operand, env).not()
                val scope = env ?: globals
                val operandType = staticExpressionType(expression.operand, scope)?.let { resolveRuntimeType(it, scope) }
                val underlyingType = operandType?.let(::underlying) as? NamedGoType
                if (underlyingType?.name in setOf("uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte")) {
                    val width = integerBitWidth(operandType!!)
                    value.and(BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE))
                } else value
            }
            else -> throw RuntimeGoError("invalid integer constant expression")
        }
        is BinaryExpression -> {
            val left = integerLiteral(expression.left, env)
            val right = integerLiteral(expression.right, env)
            when (expression.operator) {
                TokenKind.ADD -> left + right
                TokenKind.SUB -> left - right
                TokenKind.MUL -> left * right
                TokenKind.QUO -> if (right.signum() == 0) throw RuntimeGoError("division by zero in array length") else left / right
                TokenKind.REM -> if (right.signum() == 0) throw RuntimeGoError("division by zero in array length") else left % right
                TokenKind.AND -> left.and(right)
                TokenKind.OR -> left.or(right)
                TokenKind.XOR -> left.xor(right)
                TokenKind.AND_NOT -> left.and(right.not())
                TokenKind.SHL -> left.shiftLeft(right.intValueExact())
                TokenKind.SHR -> left.shiftRight(right.intValueExact())
                else -> throw RuntimeGoError("invalid integer constant expression")
            }
        }
        is CallExpression -> {
            if (expression.arguments.size != 1 || expression.expandLastArgument)
                throw RuntimeGoError("array length is not a constant integer expression")
            val name = (expression.function as? NameExpression)?.name
            if (name == "len" || name == "cap") {
                if (env?.contains(name) == true || globals.contains(name))
                    throw RuntimeGoError("array length is not a constant integer expression")
                val operand = expression.arguments.single()
                if (name == "len") constantStringByteLength(operand, env)?.let { return it }
                if (containsCallOrReceive(operand, env ?: globals))
                    throw RuntimeGoError("array length is not a constant integer expression")
                constantArrayLength(operand, env ?: globals)
                    ?: throw RuntimeGoError("array length is not a constant integer expression")
            } else {
                val scope = env ?: globals
                val target = when (val function = expression.function) {
                    is TypeExpression -> function.type
                    is NameExpression -> {
                        if (!scope.contains(function.name) && !globals.contains(function.name))
                            scope.typeBinding(function.name) ?: if (function.name in builtinTypes || typeDefinitions.containsKey(function.name))
                                NamedGoType(function.name) else null
                        else null
                    }
                    else -> null
                }?.let { resolveRuntimeType(it, scope) }
                if ((target?.let(::underlying) as? NamedGoType)?.name !in integerTypeNames)
                    throw RuntimeGoError("array length is not a constant integer expression")
                integerLiteral(expression.arguments.single(), env)
            }
        }
        else -> throw RuntimeGoError("array length is not a constant integer expression")
    }

    private fun constantArrayLength(expression: Expression, env: Environment): BigInteger? {
        arrayCompositeLiteral(expression, env)?.let { return BigInteger.valueOf(inferredArrayLiteralLength(it, env).toLong()) }
        val operandType = staticExpressionType(expression, env)?.let { resolveRuntimeType(it, env) }
        val arrayType = when (val actual = operandType?.let(::underlying)) {
            is ArrayGoType -> actual
            is PointerGoType -> underlying(actual.element) as? ArrayGoType
            else -> null
        } ?: return null
        return arrayType.length?.let { integerLiteral(it, env) }
    }

    private fun constantStringByteLength(expression: Expression, env: Environment?): BigInteger? = when (expression) {
        is LiteralExpression -> if (expression.token.kind == TokenKind.STRING)
            BigInteger.valueOf(decodeGoStringLiteralBytes(expression.token.lexeme).size.toLong()) else null
        is NameExpression -> (env?.getOrNull(expression.name) ?: globals.getOrNull(expression.name))
            ?.let { (it as? GoString)?.bytes?.size?.let { size -> BigInteger.valueOf(size.toLong()) } }
        is ParenthesizedExpression -> constantStringByteLength(expression.expression, env)
        is BinaryExpression -> if (expression.operator == TokenKind.ADD) {
            val left = constantStringByteLength(expression.left, env)
            val right = constantStringByteLength(expression.right, env)
            if (left != null && right != null) left + right else null
        } else null
        is CallExpression -> if (expression.arguments.size == 1 && !expression.expandLastArgument &&
            expression.function == NameExpression("string")) {
            constantStringByteLength(expression.arguments.single(), env) ?: runCatching {
                val value = integerLiteral(expression.arguments.single(), env)
                val codePoint = runCatching { value.intValueExact() }.getOrNull() ?: -1
                BigInteger.valueOf(encodeGoCodePoint(codePoint).size.toLong())
            }.getOrNull()
        } else null
        else -> null
    }

    private fun materializeExactConstant(value: Any?, typedOperand: Any?): Any? = when (value) {
        is GoRational -> when (typedOperand) {
            is GoInteger -> value.integerValue("integer operation")
            is Long -> value.integerValue("integer operation")
            is GoFloat, is Double -> value.toDouble()
            is GoComplex -> GoComplex(value.toDouble(), 0.0, typedOperand.type)
            else -> value
        }
        is GoExactComplex -> when (typedOperand) {
            is GoComplex -> GoComplex(value.real.toDouble(), value.imaginary.toDouble(), typedOperand.type)
            else -> throw RuntimeGoError("complex constant cannot be used with this operand")
        }
        else -> value
    }

    private fun GoRational.integerValue(context: String): BigInteger = if (isInteger()) numerator
        else throw RuntimeGoError("non-integer constant in $context")

    private fun exactRational(value: Any?): GoRational = when (value) {
        is GoRational -> value
        is BigInteger -> GoRational.of(value)
        is GoInteger -> GoRational.of(integerValue(value, "constant arithmetic"))
        is Long -> GoRational.of(BigInteger.valueOf(value))
        else -> typeError("constant arithmetic", value)
    }

    private fun exactComplex(value: Any?): GoExactComplex = when (value) {
        is GoExactComplex -> value
        else -> GoExactComplex(exactRational(value), GoRational.ZERO)
    }

    private fun exactConstantBinary(left: Any?, op: TokenKind, right: Any?): Any? {
        if (op == TokenKind.SHL || op == TokenKind.SHR) {
            val leftInteger = exactRational(left).integerValue("shift")
            val count = exactRational(right).integerValue("shift count")
            if (count.signum() < 0) throw RuntimeGoError("negative shift count")
            if (count > BigInteger.valueOf(Int.MAX_VALUE.toLong()))
                throw RuntimeGoError("untyped shift result exceeds implementation limits")
            return if (op == TokenKind.SHL) leftInteger.shiftLeft(count.toInt()) else leftInteger.shiftRight(count.toInt())
        }
        if (left is GoExactComplex || right is GoExactComplex) {
            if (left is GoComplex || right is GoComplex || left is GoFloat || right is GoFloat || left is Double || right is Double) {
                val a = complexValue(left)
                val b = complexValue(right)
                return a.real == b.real && a.imaginary == b.imaginary
            }
            val a = exactComplex(left)
            val b = exactComplex(right)
            return when (op) {
                TokenKind.ADD -> GoExactComplex(a.real + b.real, a.imaginary + b.imaginary)
                TokenKind.SUB -> GoExactComplex(a.real - b.real, a.imaginary - b.imaginary)
                TokenKind.MUL -> GoExactComplex(a.real * b.real - a.imaginary * b.imaginary,
                    a.real * b.imaginary + a.imaginary * b.real)
                TokenKind.QUO -> {
                    val denominator = b.real * b.real + b.imaginary * b.imaginary
                    GoExactComplex((a.real * b.real + a.imaginary * b.imaginary) / denominator,
                        (a.imaginary * b.real - a.real * b.imaginary) / denominator)
                }
                else -> throw RuntimeGoError("invalid complex constant operator $op")
            }
        }
        val a = exactRational(left)
        val b = exactRational(right)
        return when (op) {
            TokenKind.ADD -> a + b
            TokenKind.SUB -> a - b
            TokenKind.MUL -> a * b
            TokenKind.QUO -> a / b
            TokenKind.LSS -> a < b
            TokenKind.LEQ -> a <= b
            TokenKind.GTR -> a > b
            TokenKind.GEQ -> a >= b
            else -> throw RuntimeGoError("invalid real constant operator $op")
        }
    }

    private fun binary(left: Any?, op: TokenKind, right: Any?): Any? {
        if (op == TokenKind.EQL || op == TokenKind.NEQ) {
            val equal = goEqual(left, right)
            return if (op == TokenKind.EQL) equal else !equal
        }
        if (op == TokenKind.LAND || op == TokenKind.LOR) {
            val a = booleanValue(left, "logical operator")
            val b = booleanValue(right, "logical operator")
            return if (op == TokenKind.LAND) a && b else a || b
        }
        if (left is GoString && right is GoString) {
            if (op == TokenKind.ADD) {
                val resultType = when {
                    left.type != NamedGoType("string") -> left.type
                    right.type != NamedGoType("string") -> right.type
                    else -> left.type
                }
                return GoString(left.bytes + right.bytes, resultType)
            }
            val comparison = compareGoStrings(left, right)
            return when (op) {
                TokenKind.LSS -> comparison < 0
                TokenKind.LEQ -> comparison <= 0
                TokenKind.GTR -> comparison > 0
                TokenKind.GEQ -> comparison >= 0
                else -> throw RuntimeGoError("invalid string operator $op")
            }
        }
        if (left is GoRational || right is GoRational || left is GoExactComplex || right is GoExactComplex) {
            val typedOperand = listOf(left, right).firstOrNull {
                it is GoInteger || it is GoFloat || it is GoComplex || it is Long || it is Double
            }
            if (typedOperand != null) {
                return binary(materializeExactConstant(left, typedOperand), op, materializeExactConstant(right, typedOperand))
            }
            return exactConstantBinary(left, op, right)
        }
        if (left is GoComplex || right is GoComplex) {
            val a = complexValue(left)
            val b = complexValue(right)
            val resultType = (left as? GoComplex)?.type ?: (right as? GoComplex)?.type ?: NamedGoType("complex128")
            fun result(real: Double, imaginary: Double): GoComplex = if (underlying(resultType) == NamedGoType("complex64"))
                GoComplex(real.toFloat().toDouble(), imaginary.toFloat().toDouble(), resultType)
            else GoComplex(real, imaginary, resultType)
            return when (op) {
                TokenKind.ADD -> result(a.real + b.real, a.imaginary + b.imaginary)
                TokenKind.SUB -> result(a.real - b.real, a.imaginary - b.imaginary)
                TokenKind.MUL -> result(a.real * b.real - a.imaginary * b.imaginary,
                    a.real * b.imaginary + a.imaginary * b.real)
                TokenKind.QUO -> {
                    val (real, imaginary) = divideComplex(a, b)
                    result(real, imaginary)
                }
                else -> throw RuntimeGoError("invalid complex operator $op")
            }
        }
        if (left is Double || right is Double || left is GoFloat || right is GoFloat) {
            val a = real(left); val b = real(right)
            val resultType = (left as? GoFloat)?.type ?: (right as? GoFloat)?.type
            fun result(value: Double): Any = if (resultType == null) value else GoFloat(
                if (underlying(resultType) == NamedGoType("float32")) value.toFloat().toDouble() else value,
                resultType
            )
            return when (op) {
                TokenKind.ADD -> result(a + b); TokenKind.SUB -> result(a - b); TokenKind.MUL -> result(a * b); TokenKind.QUO -> result(a / b)
                TokenKind.LSS -> a < b; TokenKind.LEQ -> a <= b; TokenKind.GTR -> a > b; TokenKind.GEQ -> a >= b
                else -> throw RuntimeGoError("invalid floating-point operator $op")
            }
        }
        val leftType = (left as? GoInteger)?.type ?: if (left is Long) NamedGoType("int") else null
        val rightType = (right as? GoInteger)?.type ?: if (right is Long) NamedGoType("int") else null
        val integerType = if (op == TokenKind.SHL || op == TokenKind.SHR)
            leftType ?: NamedGoType("int") else leftType ?: rightType
        val a = integerValue(left, op.name)
        val b = integerValue(right, op.name)
        val compare = a.compareTo(b)
        when (op) {
            TokenKind.LSS -> return compare < 0
            TokenKind.LEQ -> return compare <= 0
            TokenKind.GTR -> return compare > 0
            TokenKind.GEQ -> return compare >= 0
            else -> Unit
        }
        val shift = if (op == TokenKind.SHL || op == TokenKind.SHR) b else BigInteger.ZERO
        if (shift.signum() < 0) throw RuntimeGoError("negative shift count")
        if (integerType != null && shift >= BigInteger.valueOf(integerBitWidth(integerType).toLong())) {
            val saturated = when {
                op == TokenKind.SHL -> BigInteger.ZERO
                isUnsignedInteger(integerType) || a.signum() >= 0 -> BigInteger.ZERO
                else -> BigInteger.ONE.negate()
            }
            return GoInteger(wrapInteger(saturated.toLong(), integerType), integerType)
        }
        if (shift > BigInteger.valueOf(Int.MAX_VALUE.toLong()))
            throw RuntimeGoError("untyped shift result exceeds implementation limits")
        val result = when (op) {
            TokenKind.ADD -> a + b
            TokenKind.SUB -> a - b
            TokenKind.MUL -> a * b
            TokenKind.QUO -> when {
                b.signum() == 0 -> throw RuntimeGoError("integer divide by zero")
                else -> a / b
            }
            TokenKind.REM -> when {
                b.signum() == 0 -> throw RuntimeGoError("integer divide by zero")
                else -> a % b
            }
            TokenKind.AND -> a.and(b)
            TokenKind.OR -> a.or(b)
            TokenKind.XOR -> a.xor(b)
            TokenKind.AND_NOT -> a.and(b.not())
            TokenKind.SHL -> a.shiftLeft(shift.toInt())
            TokenKind.SHR -> a.shiftRight(shift.toInt())
            else -> throw RuntimeGoError("invalid operator $op")
        }
        return integerType?.let { GoInteger(wrapInteger(result.toLong(), it), it) } ?: result
    }

    private fun divideComplex(numerator: GoComplex, denominator: GoComplex): Pair<Double, Double> {
        val a = numerator.real
        val b = numerator.imaginary
        val c = denominator.real
        val d = denominator.imaginary
        var real: Double
        var imaginary: Double

        // Smith's algorithm avoids squaring the denominator components, which can overflow
        // or underflow even when the quotient is representable.
        if (abs(c) >= abs(d)) {
            val ratio = d / c
            val divisor = c + ratio * d
            real = (a + b * ratio) / divisor
            imaginary = (b - a * ratio) / divisor
        } else {
            val ratio = c / d
            val divisor = d + ratio * c
            real = (a * ratio + b) / divisor
            imaginary = (b * ratio - a) / divisor
        }

        if (real.isNaN() && imaginary.isNaN()) {
            when {
                c == 0.0 && d == 0.0 && (!a.isNaN() || !b.isNaN()) -> {
                    val signedInfinity = Math.copySign(Double.POSITIVE_INFINITY, c)
                    real = signedInfinity * a
                    imaginary = signedInfinity * b
                }
                (a.isInfinite() || b.isInfinite()) && c.isFinite() && d.isFinite() -> {
                    val scaledReal = infToSignedOne(a)
                    val scaledImaginary = infToSignedOne(b)
                    real = Double.POSITIVE_INFINITY * (scaledReal * c + scaledImaginary * d)
                    imaginary = Double.POSITIVE_INFINITY * (scaledImaginary * c - scaledReal * d)
                }
                (c.isInfinite() || d.isInfinite()) && a.isFinite() && b.isFinite() -> {
                    val scaledReal = infToSignedOne(c)
                    val scaledImaginary = infToSignedOne(d)
                    real = 0.0 * (a * scaledReal + b * scaledImaginary)
                    imaginary = 0.0 * (b * scaledReal - a * scaledImaginary)
                }
            }
        }
        return real to imaginary
    }

    private fun infToSignedOne(value: Double): Double =
        Math.copySign(if (value.isInfinite()) 1.0 else 0.0, value)

    private fun goEqual(left: Any?, right: Any?): Boolean {
        if (left is GoBoolean || right is GoBoolean)
            return runCatching { booleanValue(left, "comparison") == booleanValue(right, "comparison") }.getOrDefault(false)
        if (left is GoPointer && right == null) return left.isNil
        if (right is GoPointer && left == null) return right.isNil
        if (left is GoNilValue && right == null || right is GoNilValue && left == null) return true
        if (left is GoNilValue && right is GoNilValue) {
            if (sameRuntimeType(left.type, right.type)) return true
            val leftType = underlying(left.type)
            val rightType = underlying(right.type)
            if (leftType is PointerGoType && rightType is PointerGoType)
                return sameRuntimeType(leftType.element, rightType.element)
            if (leftType is ChannelGoType && rightType is ChannelGoType) {
                val sameElement = sameRuntimeType(leftType.element, rightType.element)
                val compatibleDirection = leftType.direction == rightType.direction ||
                    leftType.direction == ChannelDirection.SEND_RECEIVE ||
                    rightType.direction == ChannelDirection.SEND_RECEIVE
                return sameElement && compatibleDirection
            }
            return false
        }
        if (left is GoInterfaceValue || right is GoInterfaceValue) {
            if (left == null || right == null) return left == null && right == null
            val leftType = ((left as? GoInterfaceValue)?.dynamicType ?: runtimeType(left))?.let(::canonicalAliasType)
            val rightType = ((right as? GoInterfaceValue)?.dynamicType ?: runtimeType(right))?.let(::canonicalAliasType)
            if (leftType != rightType && (leftType == null || rightType == null ||
                    !sameRuntimeType(leftType, rightType))) return false
            val leftInterface = left as? GoInterfaceValue
            val rightInterface = right as? GoInterfaceValue
            val leftValue = if (leftInterface != null) leftInterface.value else left
            val rightValue = if (rightInterface != null) rightInterface.value else right
            if (!runtimeComparable(leftValue) || !runtimeComparable(rightValue))
                throw RuntimeGoError("comparing uncomparable type ${leftType ?: "interface value"}")
            return goEqual(leftValue, rightValue)
        }
        if (left is GoExactComplex || right is GoExactComplex) {
            val a = exactComplex(left)
            val b = exactComplex(right)
            return a.real == b.real && a.imaginary == b.imaginary
        }
        if (left is GoRational || right is GoRational) {
            if (left is GoComplex || left is GoFloat || left is Double || right is GoComplex || right is GoFloat || right is Double) {
                val a = complexValue(left)
                val b = complexValue(right)
                return a.real == b.real && a.imaginary == b.imaginary
            }
            return runCatching { exactRational(left) == exactRational(right) }.getOrDefault(false)
        }
        if (left is GoComplex && right is GoComplex) return left.real == right.real && left.imaginary == right.imaginary
        if (left is GoComplex || right is GoComplex) {
            val a = complexValue(left)
            val b = complexValue(right)
            return a.real == b.real && a.imaginary == b.imaginary
        }
        if (left is GoInteger || right is GoInteger) {
            val a = runCatching { integerValue(left, "comparison") }.getOrNull() ?: return false
            val b = runCatching { integerValue(right, "comparison") }.getOrNull() ?: return false
            return a == b
        }
        if (left is BigInteger || right is BigInteger) {
            val a = runCatching { integerValue(left, "comparison") }.getOrNull() ?: return false
            val b = runCatching { integerValue(right, "comparison") }.getOrNull() ?: return false
            return a == b
        }
        if (left is GoFloat || right is GoFloat) return real(left) == real(right)
        if (left is Double && right is Double) return left == right
        if (left is GoArray && right is GoArray)
            return left.values.size == right.values.size &&
                left.values.indices.all { goEqual(left.values[it], right.values[it]) }
        if (left is GoStruct && right is GoStruct) return left == right
        return left == right
    }

    private fun compareGoStrings(left: GoString, right: GoString): Int {
        val leftBytes = left.bytes
        val rightBytes = right.bytes
        for (i in 0 until minOf(leftBytes.size, rightBytes.size)) {
            val difference = (leftBytes[i].toInt() and 0xff) - (rightBytes[i].toInt() and 0xff)
            if (difference != 0) return difference
        }
        return leftBytes.size.compareTo(rightBytes.size)
    }

    private fun runtimeComparable(value: Any?): Boolean = when (value) {
        is GoSlice, is GoMap, is FunctionValue, is MethodValue, is MethodExpressionValue,
        is RuntimeErrorMethodValue, is BuiltinValue -> false
        is GoNilValue -> when (underlying(value.type)) {
            is SliceGoType, is MapGoType, is FunctionGoType -> false
            else -> true
        }
        is GoArray -> value.values.all(::runtimeComparable)
        is GoStruct -> value.fields.values.all(::runtimeComparable)
        is GoInterfaceValue -> runtimeComparable(value.value)
        else -> true
    }

    private fun goHash(value: Any?): Int = when (value) {
        null -> 0
        is GoNilValue -> 0
        is GoRational -> value.hashCode()
        is GoExactComplex -> 31 * value.real.hashCode() + value.imaginary.hashCode()
        is GoBoolean -> value.value.hashCode()
        is GoInteger -> integerValue(value, "hash").hashCode()
        is Double -> if (value == 0.0) 0 else value.hashCode()
        is GoFloat -> if (value.value == 0.0) 0 else value.value.hashCode()
        is GoComplex -> 31 * (if (value.real == 0.0) 0 else value.real.hashCode()) + (if (value.imaginary == 0.0) 0 else value.imaginary.hashCode())
        is GoArray -> value.values.fold(1) { hash, element -> 31 * hash + goHash(element) }
        is GoStruct -> value.fields.entries.filterNot { isBlankStorageKey(it.key) }
            .fold(0) { hash, (name, element) ->
                31 * (31 * hash + name.hashCode()) + goHash(element)
            }
        is GoInterfaceValue -> goHash(value.value)
        else -> value.hashCode()
    }

    private fun number(value: Any?, op: String): Long = when (value) {
        is Long -> value
        is GoInteger -> try { integerValue(value, op).longValueExact() }
            catch (_: ArithmeticException) { throw RuntimeGoError("integer out of range for $op") }
        is BigInteger -> try { value.longValueExact() }
            catch (_: ArithmeticException) { throw RuntimeGoError("integer out of range for $op") }
        else -> typeError(op, value)
    }
    private fun collectionIndex(value: Any?, op: String): Int {
        val index = number(value, op)
        if (index < Int.MIN_VALUE || index > Int.MAX_VALUE) throw RuntimeGoError("$op out of range")
        return index.toInt()
    }
    private fun integerValue(value: Any?, op: String): BigInteger = when (value) {
        is BigInteger -> value
        is Long -> BigInteger.valueOf(value)
        is GoInteger -> {
            val integer = BigInteger.valueOf(value.value)
            if (isUnsignedInteger(value.type) && value.value < 0L)
                integer.add(BigInteger.ONE.shiftLeft(Long.SIZE_BITS)) else integer
        }
        else -> typeError(op, value)
    }
    private fun defaultIntegerValue(value: Any?): Any = if (value is BigInteger) {
        try { GoInteger(value.longValueExact(), NamedGoType("int")) } catch (_: ArithmeticException) {
            throw RuntimeGoError("constant overflows default int")
        }
    } else value ?: throw RuntimeGoError("invalid integer value")
    private fun defaultConstantValue(value: Any?, expression: Expression? = null, env: Environment? = null): Any? = when {
        value == null -> null
        value is BigInteger && expression != null && env != null && isRuneConstantExpression(expression, env) ->
            GoInteger(value.longValueExact(), predeclaredIntRuntimeType)
        value is GoRational -> value.toDouble()
        value is GoExactComplex -> GoComplex(value.real.toDouble(), value.imaginary.toDouble(), NamedGoType("complex128"))
        else -> defaultIntegerValue(value)
    }

    private fun defaultRuneValue(value: Any?, expression: Expression?, env: Environment): Any? =
        if (value is BigInteger && expression != null && isRuneConstantExpression(expression, env))
            GoInteger(value.longValueExact(), predeclaredIntRuntimeType) else value

    private fun asRuneValue(value: Any?): Any? = if (value is BigInteger)
        GoInteger(value.longValueExact(), predeclaredIntRuntimeType) else value

    private fun isRuneConstantExpression(expression: Expression, env: Environment): Boolean =
        integerConstantKind(expression, env) == 2

    /** 1 denotes an untyped integer constant; 2 denotes an untyped character constant. */
    private fun integerConstantKind(expression: Expression, env: Environment): Int? = when (expression) {
        is LiteralExpression -> when (expression.token.kind) {
            TokenKind.INT -> 1
            TokenKind.CHAR -> 2
            else -> null
        }
        is NameExpression -> when (env.typeOf(expression.name)) {
            untypedRuneRuntimeType -> 2
            null -> if (env.getOrNull(expression.name) is BigInteger) 1 else null
            else -> null
        }
        is ParenthesizedExpression -> integerConstantKind(expression.expression, env)
        is UnaryExpression -> if (expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.XOR))
            integerConstantKind(expression.operand, env) else null
        is BinaryExpression -> {
            val left = integerConstantKind(expression.left, env)
            val right = integerConstantKind(expression.right, env)
            when {
                expression.operator in setOf(TokenKind.SHL, TokenKind.SHR) -> if (left != null && right != null) 1 else null
                expression.operator in setOf(TokenKind.ADD, TokenKind.SUB, TokenKind.MUL, TokenKind.QUO, TokenKind.REM,
                    TokenKind.AND, TokenKind.OR, TokenKind.XOR, TokenKind.AND_NOT) && left != null && right != null -> maxOf(left, right)
                else -> null
            }
        }
        else -> null
    }

    private fun complexValue(value: Any?): GoComplex = when (value) {
        is GoComplex -> value
        is GoExactComplex -> GoComplex(value.real.toDouble(), value.imaginary.toDouble(), NamedGoType("complex128"))
        is GoRational -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is GoInteger -> GoComplex(integerAsDouble(value), 0.0, NamedGoType("complex128"))
        is GoFloat -> GoComplex(value.value, 0.0, NamedGoType("complex128"))
        is BigInteger -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is Long -> GoComplex(value.toDouble(), 0.0, NamedGoType("complex128"))
        is Double -> GoComplex(value, 0.0, NamedGoType("complex128"))
        else -> typeError("complex arithmetic", value)
    }
    private fun imaginaryPart(text: String): GoRational = runCatching { GoRational.decimal(text) }
        .getOrElse { throw RuntimeGoError("invalid imaginary literal") }
    private fun real(value: Any?): Double = when (value) {
        is Long -> value.toDouble()
        is BigInteger -> value.toDouble()
        is GoRational -> value.toDouble()
        is GoInteger -> integerAsDouble(value)
        is Double -> value
        is GoFloat -> value.value
        is GoComplex -> value.real
        else -> typeError("arithmetic", value)
    }
    private fun floatResult(value: Double, complexType: GoTypeSyntax): Any =
        if (underlying(complexType) == NamedGoType("complex64")) GoFloat(value.toFloat().toDouble(), NamedGoType("float32")) else value
    private fun booleanValue(value: Any?, operation: String): Boolean = when (value) {
        is Boolean -> value
        is GoBoolean -> value.value
        else -> typeError(operation, value)
    }
    private fun truth(value: Any?) = booleanValue(value, "condition")
    private fun stringify(value: Any?): String = when (value) {
        null -> "<nil>"
        is GoNilValue -> "<nil>"
        is GoRuntimeErrorValue -> value.message
        is GoInterfaceValue -> stringify(value.value)
        is GoComplex -> "(${value.real}${if (value.imaginary < 0) "" else "+"}${value.imaginary}i)"
        is GoFloat -> value.value.toString()
        is GoRational -> value.toString()
        is GoExactComplex -> "(${value.real}+${value.imaginary}i)"
        is BigInteger -> value.toString()
        is GoInteger -> if (isUnsignedInteger(value.type)) java.lang.Long.toUnsignedString(value.value) else value.value.toString()
        is GoBoolean -> value.value.toString()
        is GoPointer -> if (value.isNil) "<nil>" else "&${stringify(value.get())}"
        is GoString -> value.toString()
        is FunctionValue -> "<function ${value.function.name}>"
        is GoSlice -> value.toList().joinToString(prefix = "[", postfix = "]") { stringify(it) }
        is GoArray -> value.values.joinToString(prefix = "[", postfix = "]") { stringify(it) }
        is GoMap -> value.values.entries.joinToString(prefix = "map[", postfix = "]") { "${stringify(it.key.value)}:${stringify(it.value)}" }
        is GoStruct -> value.fields.values.joinToString(prefix = "{", postfix = "}") { stringify(it) }
        else -> value.toString()
    }
    private fun <T> typeError(op: String, value: Any?): T = throw RuntimeGoError("invalid operand for $op: ${value?.javaClass?.simpleName ?: "nil"}")

    private fun compoundOperator(op: TokenKind) = when (op) {
        TokenKind.ADD_ASSIGN -> TokenKind.ADD; TokenKind.SUB_ASSIGN -> TokenKind.SUB; TokenKind.MUL_ASSIGN -> TokenKind.MUL
        TokenKind.QUO_ASSIGN -> TokenKind.QUO; TokenKind.REM_ASSIGN -> TokenKind.REM; TokenKind.AND_ASSIGN -> TokenKind.AND
        TokenKind.OR_ASSIGN -> TokenKind.OR; TokenKind.XOR_ASSIGN -> TokenKind.XOR; TokenKind.SHL_ASSIGN -> TokenKind.SHL
        TokenKind.SHR_ASSIGN -> TokenKind.SHR; TokenKind.AND_NOT_ASSIGN -> TokenKind.AND_NOT
        else -> throw RuntimeGoError("invalid compound assignment")
    }

    private fun decodeString(text: String): GoString = GoString(decodeGoStringLiteralBytes(text))

    private fun decodeUtf8Runes(bytes: ByteArray): List<Int> {
        val runes = mutableListOf<Int>()
        var offset = 0
        while (offset < bytes.size) {
            val (rune, width) = decodeUtf8Rune(bytes, offset)
            runes += rune
            offset += width
        }
        return runes
    }

    private fun decodeUtf8Rune(bytes: ByteArray, offset: Int): Pair<Int, Int> {
        return decodeGoUtf8Rune(bytes, offset)
    }

    private inner class Environment(
        private val parent: Environment? = null,
        private val deferredCalls: MutableList<suspend () -> Unit> = mutableListOf(),
        val panicState: PanicState = parent?.panicState ?: PanicState(),
        var imports: RuntimeImports = parent?.imports ?: RuntimeImports()
    ) {
        private val values = mutableMapOf<String, Any?>()
        private val types = mutableMapOf<String, GoTypeSyntax>()
        private val namedTypes = mutableMapOf<String, NamedGoType>()
        private val addresses = mutableMapOf<String, GoPointer>()
        fun child() = Environment(this, deferredCalls, panicState, imports)
        fun containsLocal(name: String) = values.containsKey(name)
        fun define(name: String, value: Any?, type: GoTypeSyntax? = null) {
            values[name] = type?.let { copyForType(value, it) } ?: copyValue(value)
            if (type != null) types[name] = type
        }
        fun get(name: String): Any? = lookup(name)?.value ?: if (contains(name)) null else throw RuntimeGoError("undefined: $name")
        fun lookup(name: String): Lookup? = if (values.containsKey(name)) Lookup(values[name]) else parent?.lookup(name)
        fun binding(name: String): Lookup? = when {
            values.containsKey(name) -> Lookup(values[name])
            name in namedTypes -> Lookup(TypeValue(namedTypes.getValue(name)))
            else -> parent?.binding(name)
        }
        fun getOrNull(name: String): Any? = lookup(name)?.value
        fun contains(name: String): Boolean = values.containsKey(name) || parent?.contains(name) == true
        fun typeOf(name: String): GoTypeSyntax? = types[name] ?: parent?.typeOf(name)
        fun defineType(name: String, type: NamedGoType) { namedTypes[name] = type }
        fun clearLocalTypes() { namedTypes.clear() }
        fun typeBinding(name: String): NamedGoType? = namedTypes[name] ?: parent?.typeBinding(name)
        fun containsLocalType(name: String) = name in namedTypes
        fun pointer(name: String): GoPointer {
            val owner = owner(name) ?: throw RuntimeGoError("undefined: $name")
            return owner.addresses.getOrPut(name) {
                GoPointer.reference({ owner.get(name) }, { owner.set(name, it) }, owner.types[name] ?: runtimeType(owner.get(name)))
            }
        }
        private fun owner(name: String): Environment? = if (values.containsKey(name)) this else parent?.owner(name)
        fun defer(action: suspend () -> Unit) { deferredCalls += action }
        suspend fun runDefers(allowRecover: Boolean = false) {
            val panicAtStart = panicState.activePanic
            val actions = deferredCalls.asReversed().toList()
            deferredCalls.clear()
            var panicFromDefer: PanicSignal? = null
            for (action in actions) {
                val previousPermission = panicState.recoverAllowed
                panicState.recoverAllowed = panicState.activePanic != null &&
                    (allowRecover || panicFromDefer != null)
                try {
                    action()
                } catch (panic: PanicSignal) {
                    panicFromDefer = panic
                    panicState.activePanic = panic
                } catch (failure: RuntimeGoError) {
                    val message = failure.message ?: "runtime panic"
                    val panic = PanicSignal(GoRuntimeErrorValue(message), message)
                    panicFromDefer = panic
                    panicState.activePanic = panic
                } finally {
                    panicState.recoverAllowed = previousPermission
                }
                if (panicState.activePanic == null && panicFromDefer?.recovered == true) {
                    panicFromDefer = null
                    if (allowRecover && panicAtStart != null && !panicAtStart.recovered)
                        panicState.activePanic = panicAtStart
                }
            }
            if (panicState.activePanic == null && panicAtStart != null && !panicAtStart.recovered)
                panicState.activePanic = panicAtStart
            panicFromDefer?.takeUnless { it.recovered }?.let { throw it }
        }
        fun set(name: String, value: Any?) {
            if (values.containsKey(name)) {
                val type = types[name]
                val assigned = type?.let { copyForType(value, it) } ?: copyValue(value)
                values[name] = if (type != null) preserveAggregateStorage(values[name], assigned, type) else assigned
            }
            else if (parent != null && parent.contains(name)) parent.set(name, value)
            else throw RuntimeGoError("undefined: $name")
        }
    }

    private fun preserveAggregateStorage(previous: Any?, assigned: Any?, type: GoTypeSyntax): Any? = when (val actual = underlying(type)) {
        is ArrayGoType -> {
            val oldArray = previous as? GoArray
            val newArray = assigned as? GoArray
            if (oldArray == null || newArray == null || oldArray.values.size != newArray.values.size) assigned
            else {
                oldArray.values.indices.forEach { index ->
                    oldArray.values[index] = preserveAggregateStorage(oldArray.values[index], newArray.values[index], actual.element)
                }
                oldArray
            }
        }
        is StructGoType -> {
            val oldStruct = previous as? GoStruct
            val newStruct = assigned as? GoStruct
            if (oldStruct == null || newStruct == null) assigned
            else {
                structFieldSlots(actual).forEach { field ->
                    if (field.name.isNotEmpty() && oldStruct.fields.containsKey(field.storageKey) && newStruct.fields.containsKey(field.storageKey))
                        oldStruct.fields[field.storageKey] = preserveAggregateStorage(
                            oldStruct.fields[field.storageKey], newStruct.fields[field.storageKey], field.type
                        )
                }
                oldStruct
            }
        }
        else -> assigned
    }

    private fun elementPointer(values: MutableList<Any?>, index: Int, elementType: GoTypeSyntax): GoPointer =
        synchronized(elementPointers) {
            elementPointers.getOrPut(values) { mutableMapOf() }.getOrPut(index) {
                GoPointer.reference({ values[index] }, { value ->
                    val assigned = copyForType(value, elementType)
                    values[index] = preserveAggregateStorage(values[index], assigned, elementType)
                }, elementType)
            }
        }

    private data class Lookup(val value: Any?)
    private data class FunctionValue(
        val function: FunctionDeclaration,
        val closure: Environment,
        val type: GoTypeSyntax? = null,
        val owner: Interpreter
    )
    private data class BuiltinValue(val name: String, val type: GoTypeSyntax? = null)
    private data class TypeValue(val type: GoTypeSyntax)
    private data class MethodValue(
        val function: FunctionDeclaration,
        val receiver: Any?,
        val owner: Interpreter,
        val type: GoTypeSyntax? = null
    )
    private data class MethodExpressionValue(val receiverType: GoTypeSyntax, val name: String, val type: GoTypeSyntax)
    private data class GoMultiValue(val values: List<Any?>)
    private data class GoReceiveResult(val value: Any?, val ok: Boolean)
    private data class MapLookupResult(val value: Any?, val ok: Boolean)
    private data class GoAssertionResult(val value: Any?, val ok: Boolean, val dynamicType: GoTypeSyntax)
    private data class GoInterfaceValue(
        val dynamicType: GoTypeSyntax,
        val value: Any?,
        val implementationOwner: Interpreter? = null
    )
    private data class GoNilValue(val type: GoTypeSyntax)
    private data class GoComplex(val real: Double, val imaginary: Double, val type: GoTypeSyntax)
    private data class GoFloat(val value: Double, val type: GoTypeSyntax)
    private data class GoBoolean(val value: Boolean, val type: GoTypeSyntax)
    private data class GoInteger(val value: Long, val type: GoTypeSyntax)
    private data class RuntimeTarget(val get: () -> Any?, val set: (Any?) -> Unit, val type: GoTypeSyntax? = null)
    private data class RuntimeStructField(
        val name: String,
        val storageKey: String,
        val type: GoTypeSyntax,
        val embedded: Boolean
    )
    private class PanicState(var activePanic: PanicSignal? = null, var recoverAllowed: Boolean = false)
    private data class GoRuntimeErrorValue(val message: String)
    private data class RuntimeErrorMethodValue(val receiver: GoRuntimeErrorValue, val type: GoTypeSyntax? = null)
    private class PanicSignal(val value: Any?, message: String) : RuntimeGoError(message) {
        var recovered: Boolean = false
    }
    private data class SelectSelection(
        val caseIndex: Int,
        val received: GoReceiveResult?,
        val failure: RuntimeGoError? = null
    )
    private sealed interface SelectOperation { val caseIndex: Int; val channel: GoChannel }
    private data class SelectSend(override val caseIndex: Int, override val channel: GoChannel, val value: Any?) : SelectOperation
    private data class SelectReceive(override val caseIndex: Int, override val channel: GoChannel, val assignment: AssignmentStatement?) : SelectOperation
    private inner class ChannelDecision(private val complete: (SelectSelection) -> Unit) {
        var selected = false
            private set
        val waiters = mutableListOf<ChannelWaiter>()

        fun claim(
            caseIndex: Int,
            received: GoReceiveResult?,
            failure: RuntimeGoError?,
            completions: MutableList<() -> Unit>
        ): Boolean {
            if (selected) return false
            selected = true
            waiters.toList().forEach { it.channel.removeWaiter(it) }
            waiters.clear()
            val selection = SelectSelection(caseIndex, received, failure)
            completions += { complete(selection) }
            return true
        }

        fun cancel() {
            synchronized(goChannelCoordinator) {
                if (selected) return
                selected = true
                waiters.toList().forEach { it.channel.removeWaiter(it) }
                waiters.clear()
            }
        }
    }
    private inner class ChannelWaiter(
        val channel: GoChannel,
        val decision: ChannelDecision,
        val caseIndex: Int,
        val sendElement: GoChannelElement?
    )
    private inner class GoArray(
        val elementType: GoTypeSyntax,
        val values: MutableList<Any?>,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null,
        val packagePath: String? = packageIdentity
    ) {
        fun pointerAt(index: Int): GoPointer {
            if (index !in values.indices) throw RuntimeGoError("array index out of range")
            return elementPointer(values, index, elementType)
        }
        override fun equals(other: Any?) = other is GoArray &&
            (namedType == null || other.namedType == null ||
                namedType == other.namedType && packagePath == other.packagePath) && values.size == other.values.size &&
            values.indices.all { goEqual(values[it], other.values[it]) }
        override fun hashCode() = values.hashCode()
    }
    private inner class GoSlice(
        val elementType: GoTypeSyntax,
        private val backing: MutableList<Any?>,
        private val start: Int,
        val length: Int,
        val capacity: Int,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null,
        val packagePath: String? = packageIdentity
    ) {
        fun get(index: Int): Any? {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            return backing[start + index]
        }
        fun set(index: Int, value: Any?) {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            val absolute = start + index
            val assigned = copyForType(value, elementType)
            backing[absolute] = preserveAggregateStorage(backing[absolute], assigned, elementType)
        }
        fun pointerAt(index: Int): GoPointer {
            if (index !in 0 until length) throw RuntimeGoError("slice index out of range")
            val absolute = start + index
            return elementPointer(backing, absolute, elementType)
        }
        fun subSlice(low: Int, high: Int, max: Int): GoSlice {
            if (low < 0 || high < low || max < high || max > capacity) throw RuntimeGoError("slice bounds out of range")
            return GoSlice(elementType, backing, start + low, high - low, max - low, namedType, type, packagePath)
        }
        fun retype(element: GoTypeSyntax, name: String?, type: GoTypeSyntax, packagePath: String? = packageIdentity) =
            GoSlice(element, backing, start, length, capacity, name, type, packagePath)
        fun append(values: List<Any?>): GoSlice {
            val required = length.toLong() + values.size
            if (required > Int.MAX_VALUE) throw RuntimeGoError("slice length out of range")
            if (required <= capacity) {
                values.forEachIndexed { i, value ->
                    val index = start + length + i
                    val assigned = copyForType(value, elementType)
                    backing[index] = preserveAggregateStorage(backing[index], assigned, elementType)
                }
                return GoSlice(elementType, backing, start, length + values.size, capacity, namedType, type, packagePath)
            }
            val grownCapacity = minOf(capacity.toLong() * 2, Int.MAX_VALUE.toLong())
            val newCapacity = maxOf(required, maxOf(1L, grownCapacity)).toInt()
            val newBacking = zeroedSliceBacking(newCapacity, elementType)
            repeat(length) { newBacking[it] = get(it) }
            values.forEachIndexed { i, value -> newBacking[length + i] = copyForType(value, elementType) }
            return GoSlice(elementType, newBacking, 0, length + values.size, newCapacity, namedType, type, packagePath)
        }
        fun toList(): List<Any?> = (0 until length).map(::get)
    }
    private inner class GoMap(
        val keyType: GoTypeSyntax,
        val valueType: GoTypeSyntax,
        val elementZero: Any?,
        val values: MutableMap<GoMapKey, Any?>,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null,
        val packagePath: String? = packageIdentity
    ) {
        fun retype(key: GoTypeSyntax, value: GoTypeSyntax, name: String?, type: GoTypeSyntax,
                   packagePath: String? = packageIdentity) =
            GoMap(key, value, zeroValue(value), values, name, type, packagePath)
    }
    private inner class GoMapKey(val value: Any?) {
        override fun equals(other: Any?) = other is GoMapKey && goEqual(value, other.value)
        override fun hashCode() = goHash(value)
    }
    private inner class GoStruct(
        val fields: MutableMap<String, Any?>,
        val namedType: String? = null,
        val fieldTypes: Map<String, GoTypeSyntax> = emptyMap(),
        val embeddedFields: Set<String> = emptySet(),
        val staticType: GoTypeSyntax? = null,
        val packagePath: String? = packageIdentity
    ) {
        private val addresses = mutableMapOf<String, GoPointer>()
        fun pointer(field: String): GoPointer = addresses.getOrPut(field) {
            val fieldType = fieldTypes[field] ?: NamedGoType("<unknown>")
            GoPointer.reference({ fields[field] }, { value ->
                val assigned = copyForType(value, fieldType)
                fields[field] = preserveAggregateStorage(fields[field], assigned, fieldType)
            }, fieldTypes[field])
        }
        override fun equals(other: Any?): Boolean {
            if (other !is GoStruct || (namedType != null && other.namedType != null &&
                    (namedType != other.namedType || packagePath != other.packagePath))) return false
            val comparableFields = fields.keys.filterNot(::isBlankStorageKey)
            if (comparableFields.toSet() != other.fields.keys.filterNot(::isBlankStorageKey).toSet()) return false
            return comparableFields.all { goEqual(fields[it], other.fields[it]) }
        }
        override fun hashCode(): Int = fields.filterKeys { !isBlankStorageKey(it) }.hashCode()
    }

    private fun isBlankStorageKey(key: String) = key.startsWith("\u0000blank:")
    private class GoPointer(
        private val location: GoLocation?,
        val pointeeType: GoTypeSyntax? = null,
        val rawAddress: Long? = null,
        val valueType: GoTypeSyntax? = null
    ) {
        val isNil: Boolean get() = location == null && (rawAddress == null || rawAddress == 0L)
        val locationIdentity: Any? get() = location
        fun get(): Any? = location?.get() ?: if (location == null)
            throw RuntimeGoError("invalid memory address or nil pointer dereference") else null
        fun retype(type: GoTypeSyntax, pointerType: GoTypeSyntax? = valueType) = GoPointer(location, type, rawAddress, pointerType)
        fun set(value: Any?) {
            val target = location ?: throw RuntimeGoError("invalid memory address or nil pointer dereference")
            target.set(value)
        }
        override fun equals(other: Any?) = other is GoPointer && when {
            isNil || other.isNil -> isNil && other.isNil
            location != null && other.location != null -> location === other.location
            rawAddress != null || other.rawAddress != null -> rawAddress != null && rawAddress == other.rawAddress
            else -> location === other.location
        }
        override fun hashCode() = if (isNil) 0 else rawAddress?.hashCode() ?: System.identityHashCode(location)

        companion object {
            fun reference(get: () -> Any?, set: (Any?) -> Unit, pointeeType: GoTypeSyntax? = null) =
                GoPointer(GoLocation(get, set), pointeeType, valueType = pointeeType?.let(::PointerGoType))
            fun cell(
                value: Any?,
                pointeeType: GoTypeSyntax? = null,
                assign: (previous: Any?, assigned: Any?) -> Any? = { _, assigned -> assigned }
            ) = GoCell(value).let { cell ->
                reference({ cell.value }, { cell.value = assign(cell.value, it) }, pointeeType)
            }
            fun nil(pointeeType: GoTypeSyntax, pointerType: GoTypeSyntax? = null) =
                GoPointer(null, pointeeType, valueType = pointerType ?: PointerGoType(pointeeType))
            fun address(address: Long, pointeeType: GoTypeSyntax, pointerType: GoTypeSyntax? = null) =
                GoPointer(null, pointeeType, address, pointerType ?: PointerGoType(pointeeType))
        }
    }
    private class GoLocation(val get: () -> Any?, val set: (Any?) -> Unit)
    private class GoCell(var value: Any?)
    private inner class GoChannelState {
        val buffer = mutableListOf<GoChannelElement>()
        val senders = mutableListOf<ChannelWaiter>()
        val receivers = mutableListOf<ChannelWaiter>()
        var closed = false
    }
    private inner class GoChannel(
        val elementType: GoTypeSyntax,
        val capacity: Int,
        val namedType: String? = null,
        val type: GoTypeSyntax? = null,
        val direction: ChannelDirection = ChannelDirection.SEND_RECEIVE,
        private val state: GoChannelState = GoChannelState(),
        private val identity: Any = Any(),
        val packagePath: String? = packageIdentity
    ) {
        fun retype(element: GoTypeSyntax, direction: ChannelDirection, name: String?, type: GoTypeSyntax,
                   packagePath: String? = packageIdentity) =
            GoChannel(element, capacity, name, type, direction, state, identity, packagePath)

        override fun equals(other: Any?) = other is GoChannel && identity === other.identity
        override fun hashCode() = System.identityHashCode(identity)

        suspend fun send(value: Any?) {
            suspendCancellableCoroutine { continuation ->
                val decision = ChannelDecision { selection ->
                    continuation.resumeWith(selection.failure?.let { Result.failure(it) } ?: Result.success(Unit))
                }
                continuation.invokeOnCancellation { decision.cancel() }
                val completions = mutableListOf<() -> Unit>()
                synchronized(goChannelCoordinator) {
                    if (continuation.isActive) register(
                        ChannelWaiter(this, decision, 0, GoChannelElement(copyForType(value, elementType))),
                        enqueue = true,
                        completions
                    )
                }
                completions.forEach { it() }
            }
        }

        suspend fun receive(): GoReceiveResult = suspendCancellableCoroutine { continuation ->
            val decision = ChannelDecision { continuation.resumeWith(Result.success(it.received!!)) }
            continuation.invokeOnCancellation { decision.cancel() }
            val completions = mutableListOf<() -> Unit>()
            synchronized(goChannelCoordinator) {
                if (continuation.isActive) register(ChannelWaiter(this, decision, 0, null), enqueue = true, completions)
            }
            completions.forEach { it() }
        }

        fun register(waiter: ChannelWaiter, enqueue: Boolean, completions: MutableList<() -> Unit>) {
            if (waiter.sendElement == null) registerReceive(waiter, enqueue, completions)
            else registerSend(waiter, enqueue, completions)
        }

        private fun registerSend(waiter: ChannelWaiter, enqueue: Boolean, completions: MutableList<() -> Unit>) {
            if (waiter.decision.selected) return
            if (state.closed) {
                waiter.decision.claim(waiter.caseIndex, null, RuntimeGoError("send on closed channel"), completions)
                return
            }
            val receiver = takeEligible(state.receivers, waiter.decision)
            if (receiver != null) {
                waiter.decision.claim(waiter.caseIndex, null, null, completions)
                receiver.decision.claim(receiver.caseIndex,
                    GoReceiveResult(copyForType(waiter.sendElement!!.value, receiver.channel.elementType), true), null, completions)
            } else if (capacity > state.buffer.size) {
                state.buffer += waiter.sendElement!!
                waiter.decision.claim(waiter.caseIndex, null, null, completions)
            } else if (enqueue) addWaiter(state.senders, waiter)
        }

        private fun registerReceive(waiter: ChannelWaiter, enqueue: Boolean, completions: MutableList<() -> Unit>) {
            if (waiter.decision.selected) return
            if (state.buffer.isNotEmpty()) {
                val element = state.buffer.removeAt(0)
                waiter.decision.claim(waiter.caseIndex,
                    GoReceiveResult(copyForType(element.value, elementType), true), null, completions)
                refillBuffer(completions)
                return
            }
            val sender = takeEligible(state.senders, waiter.decision)
            if (sender != null) {
                waiter.decision.claim(waiter.caseIndex,
                    GoReceiveResult(copyForType(sender.sendElement!!.value, elementType), true), null, completions)
                sender.decision.claim(sender.caseIndex, null, null, completions)
            } else if (state.closed) {
                waiter.decision.claim(waiter.caseIndex, GoReceiveResult(zeroValue(elementType), false), null, completions)
            } else if (enqueue) addWaiter(state.receivers, waiter)
        }

        private fun refillBuffer(completions: MutableList<() -> Unit>) {
            while (!state.closed && state.buffer.size < capacity) {
                val sender = takeEligible(state.senders, null) ?: break
                state.buffer += sender.sendElement!!
                sender.decision.claim(sender.caseIndex, null, null, completions)
            }
        }

        private fun addWaiter(queue: MutableList<ChannelWaiter>, waiter: ChannelWaiter) {
            queue += waiter
            waiter.decision.waiters += waiter
        }

        private fun takeEligible(queue: MutableList<ChannelWaiter>, excluded: ChannelDecision?): ChannelWaiter? {
            var index = 0
            while (index < queue.size) {
                val waiter = queue[index]
                if (waiter.decision.selected) {
                    queue.removeAt(index)
                    waiter.decision.waiters.remove(waiter)
                } else if (waiter.decision !== excluded) {
                    queue.removeAt(index)
                    waiter.decision.waiters.remove(waiter)
                    return waiter
                } else index++
            }
            return null
        }

        fun removeWaiter(waiter: ChannelWaiter) {
            state.senders.remove(waiter)
            state.receivers.remove(waiter)
            waiter.decision.waiters.remove(waiter)
        }

        fun close() {
            val completions = mutableListOf<() -> Unit>()
            synchronized(goChannelCoordinator) {
                if (state.closed) throw RuntimeGoError("close of closed channel")
                state.closed = true
                while (state.buffer.isNotEmpty()) {
                    val receiver = takeEligible(state.receivers, null) ?: break
                    val element = state.buffer.removeAt(0)
                    receiver.decision.claim(receiver.caseIndex,
                        GoReceiveResult(copyForType(element.value, receiver.channel.elementType), true), null, completions)
                }
                (state.senders + state.receivers).shuffled().forEach { waiter ->
                    if (waiter.decision.selected) return@forEach
                    if (waiter.sendElement != null)
                        waiter.decision.claim(waiter.caseIndex, null, RuntimeGoError("send on closed channel"), completions)
                    else waiter.decision.claim(waiter.caseIndex, GoReceiveResult(zeroValue(elementType), false), null, completions)
                }
            }
            completions.forEach { it() }
        }

        fun len(): Long = synchronized(goChannelCoordinator) { state.buffer.size.toLong() }
    }
    private class GoChannelElement(val value: Any?)
    private class ReturnSignal(val values: List<Any?>, val runeConstants: List<Boolean> = emptyList()) : RuntimeException(null, null, false, false)
    private class BreakSignal(val label: String?) : RuntimeException(null, null, false, false)
    private class ContinueSignal(val label: String?) : RuntimeException(null, null, false, false)
    private class GotoSignal(val label: String) : RuntimeException(null, null, false, false)
    private class FallthroughSignal : RuntimeException(null, null, false, false)

    companion object {
        private val predeclaredIntRuntimeType = NamedGoType("#predeclared-int")
        private val predeclaredUInt8RuntimeType = NamedGoType("#predeclared-uint8")
        private val integerTypeNames = setOf("#predeclared-int", "#predeclared-uint8", "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune")
        private val errorInterfaceType = InterfaceGoType(listOf(InterfaceMethodSyntax("Error", emptyList(), listOf(NamedGoType("string")))))
        private val runtimeErrorValueType = NamedGoType("#runtime.Error")
        private val builtinTypes = setOf("bool", "byte", "complex64", "complex128", "error", "float32", "float64", "int", "int8", "int16", "int32", "int64", "rune", "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr")
    }
}
