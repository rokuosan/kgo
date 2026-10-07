package kgo

data class GoFile(val packageName: String, val declarations: List<Declaration>)

sealed interface Declaration
data class FunctionDeclaration(
    val name: String,
    val parameters: List<String?>,
    val body: BlockStatement?,
    val parameterTypes: List<GoTypeSyntax> = emptyList(),
    val resultTypes: List<GoTypeSyntax> = emptyList(),
    val receiver: ParameterSyntax? = null,
    val variadic: Boolean = false,
    val resultNames: List<String?> = emptyList()
) : Declaration
data class VariableDeclaration(val names: List<String>, val values: List<Expression>, val type: GoTypeSyntax? = null) : Declaration
data class ConstantDeclaration(
    val names: List<String>,
    val values: List<Expression>,
    val type: GoTypeSyntax? = null,
    val iotaIndex: Int = 0
) : Declaration
data class TypeDeclaration(val name: String, val type: GoTypeSyntax) : Declaration
data class ImportSpecSyntax(val alias: String?, val path: String)
data class ImportDeclaration(val imports: List<ImportSpecSyntax>) : Declaration {
    val paths: List<String> get() = imports.map { it.path }
}

sealed interface Statement
data class DeclarationStatement(val declarations: List<Declaration>) : Statement
data class LabeledStatement(val label: String, val statement: Statement) : Statement
data class BlockStatement(val statements: List<Statement>) : Statement
data class VariableStatement(val names: List<String>, val values: List<Expression>, val type: GoTypeSyntax? = null) : Statement
data class ReturnStatement(val values: List<Expression>) : Statement
data class ExpressionStatement(val expression: Expression) : Statement
data class SendStatement(val channel: Expression, val value: Expression) : Statement
data class GoStatement(val call: Expression) : Statement
data class DeferStatement(val call: Expression) : Statement
data class BranchStatement(val kind: TokenKind, val label: String?) : Statement
data class SelectStatement(val cases: List<SelectCase>) : Statement
data class SelectCase(val communication: Statement?, val statements: List<Statement>)
data class SwitchStatement(val init: Statement?, val tag: Expression?, val clauses: List<SwitchClause>) : Statement
data class SwitchClause(val expressions: List<Expression>?, val statements: List<Statement>)
data class TypeSwitchStatement(val init: Statement?, val guard: TypeSwitchGuard, val clauses: List<TypeSwitchClause>) : Statement
data class TypeSwitchGuard(val name: String?, val expression: Expression)
data class TypeSwitchClause(val types: List<GoTypeSyntax>?, val statements: List<Statement>)
data class AssignmentStatement(
    val targets: List<Expression>,
    val operator: TokenKind,
    val values: List<Expression>
) : Statement
data class IncrementStatement(val target: Expression, val delta: Int) : Statement
data class IfStatement(
    val init: Statement?,
    val condition: Expression,
    val thenBranch: BlockStatement,
    val elseBranch: Statement?
) : Statement
data class ForStatement(
    val init: Statement?,
    val condition: Expression?,
    val post: Statement?,
    val body: BlockStatement,
    val rangeClause: RangeClause? = null
) : Statement
data class RangeClause(val targets: List<Expression>, val operator: TokenKind?, val expression: Expression)
data object EmptyStatement : Statement

sealed interface Expression
fun Expression.unparenthesized(): Expression = when (this) {
    is ParenthesizedExpression -> expression.unparenthesized()
    else -> this
}

data class NameExpression(val name: String) : Expression
data class LiteralExpression(val token: Token) : Expression
data class UnaryExpression(val operator: TokenKind, val operand: Expression) : Expression
data class BinaryExpression(val left: Expression, val operator: TokenKind, val right: Expression) : Expression
data class CallExpression(val function: Expression, val arguments: List<Expression>, val expandLastArgument: Boolean = false) : Expression
data class SelectorExpression(val receiver: Expression, val field: String) : Expression
data class IndexExpression(val receiver: Expression, val index: Expression) : Expression
data class SliceExpression(val receiver: Expression, val low: Expression?, val high: Expression?) : Expression
data class TypeAssertionExpression(val receiver: Expression, val type: GoTypeSyntax) : Expression
data class TypeSwitchGuardExpression(val receiver: Expression) : Expression
data class ParenthesizedExpression(val expression: Expression) : Expression
data class TypeExpression(val type: GoTypeSyntax) : Expression
data class CompositeLiteral(val type: GoTypeSyntax, val elements: List<CompositeElement>) : Expression
data class ElidedCompositeLiteral(val elements: List<CompositeElement>) : Expression
data class FunctionLiteralExpression(
    val parameters: List<ParameterSyntax>,
    val results: List<GoTypeSyntax>,
    val body: BlockStatement,
    val variadic: Boolean = false,
    val resultNames: List<String?> = emptyList()
) : Expression
data class CompositeElement(val key: Expression?, val value: Expression)

sealed interface GoTypeSyntax
data class ParameterSyntax(val name: String?, val type: GoTypeSyntax, val variadic: Boolean = false)
data class StructFieldSyntax(
    val names: List<String>,
    val type: GoTypeSyntax,
    val tag: String? = null,
    val packagePath: String? = null,
    val declaringPackagePath: String? = null
)
data class InterfaceMethodSyntax(
    val name: String,
    val parameters: List<ParameterSyntax>,
    val results: List<GoTypeSyntax>,
    val packagePath: String? = null
)
data class NamedGoType(val name: String) : GoTypeSyntax
data class QualifiedGoType(val packageName: String, val name: String) : GoTypeSyntax
data class PointerGoType(val element: GoTypeSyntax) : GoTypeSyntax
data class SliceGoType(val element: GoTypeSyntax) : GoTypeSyntax
data class ArrayGoType(val length: Expression?, val element: GoTypeSyntax) : GoTypeSyntax
data class MapGoType(val key: GoTypeSyntax, val value: GoTypeSyntax) : GoTypeSyntax
data class ChannelGoType(val element: GoTypeSyntax, val direction: ChannelDirection) : GoTypeSyntax
data class StructGoType(val fields: List<StructFieldSyntax>) : GoTypeSyntax
data class InterfaceGoType(val methods: List<InterfaceMethodSyntax>, val embeddedTypes: List<GoTypeSyntax> = emptyList()) : GoTypeSyntax
data class FunctionGoType(val parameters: List<ParameterSyntax>, val results: List<GoTypeSyntax>) : GoTypeSyntax
enum class ChannelDirection { SEND_RECEIVE, SEND_ONLY, RECEIVE_ONLY }
