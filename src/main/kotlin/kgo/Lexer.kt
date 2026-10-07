package kgo

/** Scanner for the Go 1.0 lexical grammar, including automatic semicolon insertion. */
class Lexer(private val source: String) {
    private var offset = 0
    private var byteOffset = 0
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
                isIdentifierStart(codePointAtOffset()) -> identifier(start)
                isAsciiDigit(c) || (c == '.' && isAsciiDigit(peek(1))) -> number(start)
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
        while (offset < source.length && isIdentifierContinue(codePointAtOffset())) advance()
        val text = source.substring(begin, offset)
        return Token(keywords[text] ?: TokenKind.IDENT, text, start)
    }

    private fun number(start: Position): Token {
        val begin = offset
        var kind = TokenKind.INT
        val hexadecimal = peek() == '0' && (peek(1) == 'x' || peek(1) == 'X')
        if (peek() == '.') {
            kind = TokenKind.FLOAT
            advance()
            while (isAsciiDigit(peek())) advance()
            scanExponent(start)
        } else if (hexadecimal) {
            advance(); advance()
            val digits = offset
            while (offset < source.length && isAsciiRadixDigit(peek(), 16)) advance()
            if (offset == digits) throw ScanError("hexadecimal literal has no digits", start)
        } else {
            while (isAsciiDigit(peek())) advance()
            if (peekOrNull() == '.') {
                kind = TokenKind.FLOAT
                advance()
                while (isAsciiDigit(peek())) advance()
            }
            if (scanExponent(start)) kind = TokenKind.FLOAT
        }
        val imaginary = !hexadecimal && peekOrNull() == 'i'
        if (imaginary) {
            advance()
            kind = TokenKind.IMAG
        }
        if (!imaginary && kind == TokenKind.INT && source[begin] == '0' && offset - begin > 1 &&
            source.substring(begin, offset).any { it in '8'..'9' }) {
            throw ScanError("invalid digit in octal literal", start)
        }
        return Token(kind, source.substring(begin, offset), start)
    }

    private fun scanExponent(start: Position): Boolean {
        if (peekOrNull() != 'e' && peekOrNull() != 'E') return false
        advance()
        if (peekOrNull() == '+' || peekOrNull() == '-') advance()
        val digits = offset
        while (isAsciiDigit(peek())) advance()
        if (digits == offset) throw ScanError("malformed exponent", start)
        return true
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
                if (c == '\\') scanEscape(start, quote) else advance()
            }
        }
        throw ScanError("unterminated string literal", start)
    }

    private fun rune(start: Position): Token {
        val begin = offset
        advance()
        if (offset >= source.length || peek() == '\n' || peek() == '\'') throw ScanError("empty or unterminated rune literal", start)
        if (peek() == '\\') scanEscape(start, '\'') else advance()
        if (peekOrNull() != '\'') throw ScanError("rune literal must contain one character", start)
        advance()
        return Token(TokenKind.CHAR, source.substring(begin, offset), start)
    }

    private fun scanEscape(start: Position, quote: Char) {
        advance()
        if (offset >= source.length) throw ScanError("unfinished escape sequence", start)
        val escaped = peek()
        if (escaped in "abfnrtv\\" || (escaped == '"' && quote == '"') || (escaped == '\'' && quote == '\'')) {
            advance()
            return
        }
        when (escaped) {
            in '0'..'7' -> {
                val begin = offset
                repeat(3) {
                    if (peek() !in '0'..'7') throw ScanError("octal escape must have three digits", start)
                    advance()
                }
                if (source.substring(begin, offset).toInt(8) > 0xff)
                    throw ScanError("octal escape value exceeds one byte", start)
            }
            'x' -> { advance(); consumeDigits(2, 16, start) }
            'u' -> { advance(); validateUnicodeEscape(4, start) }
            'U' -> { advance(); validateUnicodeEscape(8, start) }
            else -> throw ScanError("invalid escape sequence \\$escaped", start)
        }
    }

    private fun consumeDigits(count: Int, radix: Int, start: Position): String {
        val begin = offset
        repeat(count) {
            if (!isAsciiRadixDigit(peek(), radix)) throw ScanError("invalid escape sequence", start)
            advance()
        }
        return source.substring(begin, offset)
    }

    private fun validateUnicodeEscape(count: Int, start: Position) {
        val digits = consumeDigits(count, 16, start)
        val cp = digits.toLong(16)
        if (cp > 0x10ffff)
            throw ScanError("invalid Unicode code point", start)
    }

    private fun operator(start: Position): Token {
        val begin = offset
        val candidates = operators.keys.sortedByDescending { it.length }
        val op = candidates.firstOrNull { startsWith(it) } ?: throw ScanError("unexpected character '${peek()}'", start)
        repeat(op.length) { advance() }
        return Token(operators.getValue(op), source.substring(begin, offset), start)
    }

    private fun position() = Position(byteOffset, line, column)
    private fun startsWith(s: String) = source.startsWith(s, offset)
    private fun peek(ahead: Int = 0): Char = source.getOrElse(offset + ahead) { '\u0000' }
    private fun peekOrNull(): Char? = source.getOrNull(offset)
    private fun advance() {
        if (offset >= source.length) return
        val cp = source.codePointAt(offset)
        val count = Character.charCount(cp)
        offset += count
        val byteCount = when {
            cp <= 0x7f -> 1
            cp <= 0x7ff -> 2
            cp <= 0xffff -> 3
            else -> 4
        }
        byteOffset += byteCount
        if (cp == '\n'.code) { line++; column = 1 } else column += byteCount
    }

    private fun codePointAtOffset() = if (offset < source.length) source.codePointAt(offset) else 0
    private fun isIdentifierStart(c: Int) = c == '_'.code || GoUnicode6.isLetter(c)
    private fun isIdentifierContinue(c: Int) = isIdentifierStart(c) || GoUnicode6.isDecimalDigit(c)
    private fun isAsciiDigit(c: Char) = c in '0'..'9'
    private fun isAsciiRadixDigit(c: Char, radix: Int) = when (c) {
        in '0'..'9' -> c - '0' < radix
        in 'a'..'f' -> c - 'a' + 10 < radix
        in 'A'..'F' -> c - 'A' + 10 < radix
        else -> false
    }

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
