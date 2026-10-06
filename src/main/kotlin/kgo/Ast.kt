package kgo

data class GoFile(val packageName: String, val declarations: List<Declaration>)

sealed interface Declaration
data class FunctionDeclaration(
    val name: String,
    val parameters: List<String>,
    val body: BlockStatement
) : Declaration
data class VariableDeclaration(val names: List<String>, val values: List<Expression>) : Declaration
data class ImportDeclaration(val paths: List<String>) : Declaration

sealed interface Statement
data class BlockStatement(val statements: List<Statement>) : Statement
data class VariableStatement(val names: List<String>, val values: List<Expression>) : Statement
data class ReturnStatement(val values: List<Expression>) : Statement
data class ExpressionStatement(val expression: Expression) : Statement
data class SendStatement(val channel: Expression, val value: Expression) : Statement
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
    val body: BlockStatement
) : Statement
data object EmptyStatement : Statement

sealed interface Expression
data class NameExpression(val name: String) : Expression
data class LiteralExpression(val token: Token) : Expression
data class UnaryExpression(val operator: TokenKind, val operand: Expression) : Expression
data class BinaryExpression(val left: Expression, val operator: TokenKind, val right: Expression) : Expression
data class CallExpression(val function: Expression, val arguments: List<Expression>) : Expression
data class SelectorExpression(val receiver: Expression, val field: String) : Expression
data class IndexExpression(val receiver: Expression, val index: Expression) : Expression
data class ParenthesizedExpression(val expression: Expression) : Expression
