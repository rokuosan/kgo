package kgo

enum class TokenKind {
    IDENT, INT, FLOAT, IMAG, CHAR, STRING,
    BREAK, CASE, CHAN, CONST, CONTINUE, DEFAULT, DEFER, ELSE, FALLTHROUGH,
    FOR, FUNC, GO, GOTO, IF, IMPORT, INTERFACE, MAP, PACKAGE, RANGE, RETURN,
    SELECT, STRUCT, SWITCH, TYPE, VAR,
    ADD, SUB, MUL, QUO, REM, AND, OR, XOR, SHL, SHR, AND_NOT,
    ADD_ASSIGN, SUB_ASSIGN, MUL_ASSIGN, QUO_ASSIGN, REM_ASSIGN,
    AND_ASSIGN, OR_ASSIGN, XOR_ASSIGN, SHL_ASSIGN, SHR_ASSIGN, AND_NOT_ASSIGN,
    LAND, LOR, ARROW, INC, DEC, EQL, LSS, GTR, ASSIGN, NOT,
    NEQ, LEQ, GEQ, DEFINE, ELLIPSIS,
    LPAREN, LBRACK, LBRACE, COMMA, PERIOD, RPAREN, RBRACK, RBRACE,
    SEMICOLON, COLON, EOF
}

/** Source offset and column use UTF-8 byte counts, matching Go source positions. */
data class Position(val offset: Int, val line: Int, val column: Int)

data class Token(val kind: TokenKind, val lexeme: String, val position: Position)

class ScanError(message: String, val position: Position) : RuntimeException(
    "${position.line}:${position.column}: $message"
)
