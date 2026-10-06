package kgo

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
    private var functionLabels: Map<String, Statement> = emptyMap()

    fun check(file: GoFile) {
        for (declaration in file.declarations) when (declaration) {
            is TypeDeclaration -> {
                if (typeDeclarations.putIfAbsent(declaration.name, declaration.type) != null) error("type ${declaration.name} redeclared")
            }
            is FunctionDeclaration -> {
                val receiver = declaration.receiver
                if (receiver == null) {
                    if (declaration.name == "init") initFunctions += declaration
                    else if (functions.putIfAbsent(declaration.name, declaration) != null) error("function ${declaration.name} redeclared")
                } else {
                    methods[methodKey(receiver.type, declaration.name)] = declaration
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
            receiver.name?.let { scope.define(it, receiver.type) }
        }
        function.parameters.forEachIndexed { i, name ->
            val type = function.parameterTypes.getOrNull(i) ?: error("missing type for parameter ${name ?: i}")
            validateType(type)
            if (name != null && name != "_") scope.define(name, type)
        }
        function.resultTypes.forEach(::validateType)
        val previousResults = resultTypes
        val previousLabels = functionLabels
        resultTypes = function.resultTypes
        functionLabels = collectLabels(function.body)
        try { checkBlock(function.body, scope) } finally {
            resultTypes = previousResults
            functionLabels = previousLabels
        }
    }

    private fun checkBlock(block: BlockStatement, parent: Scope) {
        val scope = parent.child()
        block.statements.forEach { checkStatement(it, scope) }
    }

    private fun collectLabels(body: BlockStatement): Map<String, Statement> {
        val labels = linkedMapOf<String, Statement>()
        fun visit(statement: Statement) {
            when (statement) {
                is LabeledStatement -> {
                    if (labels.putIfAbsent(statement.label, statement.statement) != null) error("label ${statement.label} redeclared")
                    visit(statement.statement)
                }
                is BlockStatement -> statement.statements.forEach(::visit)
                is IfStatement -> {
                    statement.init?.let(::visit); visit(statement.thenBranch); statement.elseBranch?.let(::visit)
                }
                is ForStatement -> {
                    statement.init?.let(::visit); statement.post?.let(::visit); visit(statement.body)
                }
                is SwitchStatement -> {
                    statement.init?.let(::visit)
                    statement.clauses.flatMap { it.statements }.forEach(::visit)
                }
                is SelectStatement -> statement.cases.forEach { clause ->
                    clause.communication?.let(::visit); clause.statements.forEach(::visit)
                }
                else -> Unit
            }
        }
        body.statements.forEach(::visit)
        return labels
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
            is BranchStatement -> if (statement.label != null) {
                val target = functionLabels[statement.label] ?: error("undefined label ${statement.label}")
                val destination = unwrapLabels(target)
                when (statement.kind) {
                    TokenKind.BREAK -> if (destination !is ForStatement && destination !is SwitchStatement && destination !is SelectStatement)
                        error("invalid break label ${statement.label}")
                    TokenKind.CONTINUE -> if (destination !is ForStatement) error("invalid continue label ${statement.label}")
                    else -> error("label is not valid on ${statement.kind}")
                }
            }
            is SelectStatement -> checkSelect(statement, scope)
            is SwitchStatement -> checkSwitch(statement, scope)
        }
    }

    private fun checkAssignment(statement: AssignmentStatement, scope: Scope) {
        if (statement.operator == TokenKind.DEFINE) {
            val names = statement.targets.map { (it as? NameExpression)?.name ?: error("short declaration target must be an identifier") }
            val valueTypes = expressionTypes(statement.values, names.size, scope)
            if (valueTypes.size != names.size) error("assignment count mismatch")
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
            clause.statements.forEach { checkStatement(it, caseScope) }
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
            clause.statements.forEach { checkStatement(it, caseScope) }
        }
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
            resultTypes = expression.results
            functionLabels = collectLabels(expression.body)
            try { checkBlock(expression.body, literalScope) } finally {
                resultTypes = previousResults
                functionLabels = previousLabels
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
                is NamedGoType -> if (receiver.name == "string") receiver else error("cannot slice ${receiver.name}")
                else -> error("cannot slice this value")
            }
        }
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
        val receiver = underlying(expressionType(expression.receiver, scope))
        val struct = when (receiver) {
            is StructGoType -> receiver
            is PointerGoType -> underlying(receiver.element) as? StructGoType
            else -> null
        } ?: error("selector requires struct or package")
        struct.fields.firstOrNull { expression.field in it.names }?.let { return it.type }
        val named = namedType(expressionType(expression.receiver, scope)) ?: error("selector receiver has no method set")
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
            "complex" -> { requireCount(name, args, 2); listOf(NamedGoType("complex128")) }
            "real", "imag" -> { requireCount(name, args, 1); listOf(NamedGoType("float64")) }
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
            return boolType
        }
        if (operator in setOf(TokenKind.LSS, TokenKind.LEQ, TokenKind.GTR, TokenKind.GEQ)) {
            if (!((isNumeric(left) && isNumeric(right)) || (isString(left) && isString(right)))) error("invalid ordered comparison")
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
        return underlying(from) == underlying(to) && (!isNamed(from) || !isNamed(to))
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
                type.embeddedTypes.forEach { validateType(it, active) }
                type.methods.forEach { method -> method.parameters.forEach { validateType(it.type, active) }; method.results.forEach { validateType(it, active) } }
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
    private fun underlying(type: GoTypeSyntax, seen: Set<String> = emptySet()): GoTypeSyntax = when (type) {
        is NamedGoType -> typeDeclarations[type.name]?.let { if (type.name in seen) type else underlying(it, seen + type.name) } ?: type
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
        private val integerNames = setOf("int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr", "byte", "rune")
        private val floatNames = setOf("float32", "float64")
        private val complexNames = setOf("complex64", "complex128")
        private val builtinTypes = integerNames + floatNames + complexNames + setOf("bool", "string")
    }
}
