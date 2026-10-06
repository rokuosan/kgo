package kgo

internal fun canonicalGoStringLiteral(text: String): String =
    decodeGoStringLiteralBytes(text).joinToString(separator = "") { byte ->
        (byte.toInt() and 0xff).toString(16).padStart(2, '0')
    }

internal fun decodeGoStringLiteralBytes(text: String): ByteArray {
    if (text.length < 2) throw RuntimeGoError("invalid string literal")
    if (text.first() == '`') return text.substring(1, text.length - 1).replace("\r", "").toByteArray(Charsets.UTF_8)
    val body = text.substring(1, text.length - 1)
    val bytes = mutableListOf<Byte>()
    fun appendCodePoint(codePoint: Int) { bytes += String(Character.toChars(codePoint)).toByteArray(Charsets.UTF_8).toList() }
    var i = 0
    while (i < body.length) {
        val c = body[i++]
        if (c != '\\') {
            val codePoint = if (Character.isHighSurrogate(c) && i < body.length && Character.isLowSurrogate(body[i]))
                Character.toCodePoint(c, body[i++]) else c.code
            appendCodePoint(codePoint)
            continue
        }
        if (i >= body.length) throw RuntimeGoError("unfinished escape")
        when (val escaped = body[i++]) {
            'a' -> bytes += 0x07.toByte(); 'b' -> bytes += 0x08.toByte(); 'f' -> bytes += 0x0c.toByte()
            'n' -> bytes += 0x0a.toByte(); 'r' -> bytes += 0x0d.toByte(); 't' -> bytes += 0x09.toByte()
            'v' -> bytes += 0x0b.toByte(); '\\' -> bytes += 0x5c.toByte(); '"' -> bytes += 0x22.toByte()
            'x' -> { bytes += body.substring(i, i + 2).toInt(16).toByte(); i += 2 }
            in '0'..'7' -> {
                bytes += body.substring(i - 1, i + 2).toInt(8).toByte()
                i += 2
            }
            'u', 'U' -> {
                val digits = if (escaped == 'u') 4 else 8
                val codePoint = body.substring(i, i + digits).toLong(16).toInt()
                appendCodePoint(codePoint)
                i += digits
            }
            else -> throw RuntimeGoError("unknown escape sequence \\$escaped")
        }
    }
    return bytes.toByteArray()
}
