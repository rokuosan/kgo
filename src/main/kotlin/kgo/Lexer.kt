package kgo

/** Scanner for the Go 1.0 lexical grammar, including automatic semicolon insertion. */
class Lexer(private val source: String) {
    private var offset = 0
    private var line = 1
    private var column = 1
    private var insertSemi = false

    fun scan(): List<Token> {
        val tokens = mutableListOf<Token>()
        while (true) {
            skipSpaceAndComments(tokens)
            if (offset >= source.length) {
                if (insertSemi) tokens += Token(TokenKind.SEMICOLON, "\n", position())
                tokens += Token(TokenKind.EOF, "", position())
                return tokens
            }
            val start = position()
            val c = peek()
            val token = when {
                isIdentifierStart(c) -> identifier(start)
                c.isDigit() -> number(start)
                c == '"' || c == '`' -> string(start, c)
                c == '\'' -> rune(start)
                else -> operator(start)
            }
            tokens += token
            insertSemi = token.kind in semicolonEnders
        }
    }

    private fun skipSpaceAndComments(tokens: MutableList<Token>) {
        while (offset < source.length) {
            when {
                peek() == ' ' || peek() == '\t' || peek() == '\r' -> advance()
                peek() == '\n' -> {
                    val p = position(); advance()
                    if (insertSemi) { tokens += Token(TokenKind.SEMICOLON, "\n", p); insertSemi = false }
                }
                startsWith("//") -> {
                    while (offset < source.length && peek() != '\n') advance()
                }
                startsWith("/*") -> {
                    val start = position(); advance(); advance()
                    var newline: Position? = null
                    while (offset < source.length && !startsWith("*/")) {
                        if (peek() == '\n' && newline == null) newline = position()
                        advance()
                    }
                    if (offset >= source.length) throw ScanError("unterminated block comment", start)
                    advance(); advance()
                    if (newline != null && insertSemi) {
                        tokens += Token(TokenKind.SEMICOLON, "\n", newline)
                        insertSemi = false
                    }
                }
                else -> return
            }
        }
    }

    private fun identifier(start: Position): Token {
        val begin = offset
        advance()
        while (offset < source.length && isIdentifierContinue(peek())) advance()
        val text = source.substring(begin, offset)
        return Token(keywords[text] ?: TokenKind.IDENT, text, start)
    }

    private fun number(start: Position): Token {
        val begin = offset
        var kind = TokenKind.INT
        if (peek() == '0' && (peek(1) == 'x' || peek(1) == 'X')) {
            advance(); advance()
            val digits = offset
            while (offset < source.length && peek().digitToIntOrNull(16) != null) advance()
            if (offset == digits) throw ScanError("hexadecimal literal has no digits", start)
        } else {
            while (offset < source.length && peek().isDigit()) advance()
            if (source[begin] == '0' && offset - begin > 1 && source.substring(begin, offset).any { it in '8'..'9' }) {
                throw ScanError("invalid digit in octal literal", start)
            }
        }
        if (peekOrNull() == '.' && peek(1).isDigit()) {
            kind = TokenKind.FLOAT; advance()
            while (offset < source.length && peek().isDigit()) advance()
        }
        if (peekOrNull() == 'e' || peekOrNull() == 'E') {
            kind = TokenKind.FLOAT; advance()
            if (peekOrNull() == '+' || peekOrNull() == '-') advance()
            val exp = offset
            while (offset < source.length && peek().isDigit()) advance()
            if (exp == offset) throw ScanError("malformed exponent", start)
        }
        if (peekOrNull() == 'i') { advance(); kind = TokenKind.IMAG }
        return Token(kind, source.substring(begin, offset), start)
    }

    private fun string(start: Position, quote: Char): Token {
        val begin = offset
        advance()
        while (offset < source.length) {
            val c = peek()
            if (c == quote) { advance(); return Token(TokenKind.STRING, source.substring(begin, offset), start) }
            if (quote == '`') {
                if (c == '\r') { advance(); continue }
                advance()
            } else {
                if (c == '\n') throw ScanError("newline in interpreted string", start)
                if (c == '\\') { advance(); if (offset < source.length) advance() } else advance()
            }
        }
        throw ScanError("unterminated string literal", start)
    }

    private fun rune(start: Position): Token {
        val begin = offset
        advance()
        if (offset >= source.length || peek() == '\n' || peek() == '\'') throw ScanError("empty or unterminated rune literal", start)
        if (peek() == '\\') { advance(); if (offset < source.length) advance() } else advance()
        if (peekOrNull() != '\'') throw ScanError("rune literal must contain one character", start)
        advance()
        return Token(TokenKind.CHAR, source.substring(begin, offset), start)
    }

    private fun operator(start: Position): Token {
        val begin = offset
        val candidates = operators.keys.sortedByDescending { it.length }
        val op = candidates.firstOrNull { startsWith(it) } ?: throw ScanError("unexpected character '${peek()}'", start)
        repeat(op.length) { advance() }
        return Token(operators.getValue(op), source.substring(begin, offset), start)
    }

    private fun position() = Position(offset, line, column)
    private fun startsWith(s: String) = source.startsWith(s, offset)
    private fun peek(ahead: Int = 0): Char = source.getOrElse(offset + ahead) { '\u0000' }
    private fun peekOrNull(): Char? = source.getOrNull(offset)
    private fun advance() {
        if (offset >= source.length) return
        if (source[offset++] == '\n') { line++; column = 1 } else column++
    }

    private fun isIdentifierStart(c: Char) = c == '_' || c.isLetter()
    private fun isIdentifierContinue(c: Char) = isIdentifierStart(c) || c.isDigit()

    companion object {
        private val semicolonEnders = setOf(TokenKind.IDENT, TokenKind.INT, TokenKind.FLOAT, TokenKind.IMAG,
            TokenKind.CHAR, TokenKind.STRING, TokenKind.BREAK, TokenKind.CONTINUE, TokenKind.FALLTHROUGH,
            TokenKind.RETURN, TokenKind.INC, TokenKind.DEC, TokenKind.RPAREN, TokenKind.RBRACK, TokenKind.RBRACE)
        private val keywords = mapOf(
            "break" to TokenKind.BREAK, "case" to TokenKind.CASE, "chan" to TokenKind.CHAN,
            "const" to TokenKind.CONST, "continue" to TokenKind.CONTINUE, "default" to TokenKind.DEFAULT,
            "defer" to TokenKind.DEFER, "else" to TokenKind.ELSE, "fallthrough" to TokenKind.FALLTHROUGH,
            "for" to TokenKind.FOR, "func" to TokenKind.FUNC, "go" to TokenKind.GO, "goto" to TokenKind.GOTO,
            "if" to TokenKind.IF, "import" to TokenKind.IMPORT, "interface" to TokenKind.INTERFACE,
            "map" to TokenKind.MAP, "package" to TokenKind.PACKAGE, "range" to TokenKind.RANGE,
            "return" to TokenKind.RETURN, "select" to TokenKind.SELECT, "struct" to TokenKind.STRUCT,
            "switch" to TokenKind.SWITCH, "type" to TokenKind.TYPE, "var" to TokenKind.VAR
        )
        private val operators = mapOf(
            "+" to TokenKind.ADD, "-" to TokenKind.SUB, "*" to TokenKind.MUL, "/" to TokenKind.QUO,
            "%" to TokenKind.REM, "&" to TokenKind.AND, "|" to TokenKind.OR, "^" to TokenKind.XOR,
            "<<" to TokenKind.SHL, ">>" to TokenKind.SHR, "&^" to TokenKind.AND_NOT,
            "+=" to TokenKind.ADD_ASSIGN, "-=" to TokenKind.SUB_ASSIGN, "*=" to TokenKind.MUL_ASSIGN,
            "/=" to TokenKind.QUO_ASSIGN, "%=" to TokenKind.REM_ASSIGN, "&=" to TokenKind.AND_ASSIGN,
            "|=" to TokenKind.OR_ASSIGN, "^=" to TokenKind.XOR_ASSIGN, "<<=" to TokenKind.SHL_ASSIGN,
            ">>=" to TokenKind.SHR_ASSIGN, "&^=" to TokenKind.AND_NOT_ASSIGN,
            "&&" to TokenKind.LAND, "||" to TokenKind.LOR, "<-" to TokenKind.ARROW,
            "++" to TokenKind.INC, "--" to TokenKind.DEC, "==" to TokenKind.EQL,
            "<" to TokenKind.LSS, ">" to TokenKind.GTR, "=" to TokenKind.ASSIGN, "!" to TokenKind.NOT,
            "!=" to TokenKind.NEQ, "<=" to TokenKind.LEQ, ">=" to TokenKind.GEQ, ":=" to TokenKind.DEFINE,
            "..." to TokenKind.ELLIPSIS, "(" to TokenKind.LPAREN, "[" to TokenKind.LBRACK,
            "{" to TokenKind.LBRACE, "," to TokenKind.COMMA, "." to TokenKind.PERIOD,
            ")" to TokenKind.RPAREN, "]" to TokenKind.RBRACK, "}" to TokenKind.RBRACE,
            ";" to TokenKind.SEMICOLON, ":" to TokenKind.COLON
        )
    }
}
