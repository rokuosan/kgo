package kgo

import java.math.BigInteger

internal fun canonicalGoStringLiteral(text: String): String =
    decodeGoStringLiteralBytes(text).joinToString(separator = "") { byte ->
        (byte.toInt() and 0xff).toString(16).padStart(2, '0')
    }

internal fun decodeGoCharacterLiteral(text: String): Int {
    if (text.length < 3 || text.first() != '\'' || text.last() != '\'')
        throw RuntimeGoError("invalid character literal")
    val body = text.substring(1, text.length - 1)
    if (body.isEmpty()) throw RuntimeGoError("empty character literal")
    if (body.first() != '\\') {
        if (body.codePointCount(0, body.length) != 1)
            throw RuntimeGoError("character literal must contain one Unicode code point")
        return body.codePointAt(0)
    }
    val escape = body.substring(1)
    return when (escape.firstOrNull()) {
        'a' -> 7
        'b' -> 8
        'f' -> 12
        'n' -> 10
        'r' -> 13
        't' -> 9
        'v' -> 11
        '\\' -> 92
        '\'' -> 39
        'x' -> {
            if (escape.length != 3 || !escape.drop(1).all(Char::isHexDigit))
                throw RuntimeGoError("invalid hexadecimal character escape")
            escape.drop(1).toInt(16)
        }
        'u', 'U' -> {
            val digits = if (escape.first() == 'u') 4 else 8
            val hex = escape.drop(1)
            if (hex.length != digits || !hex.all(Char::isHexDigit))
                throw RuntimeGoError("invalid Unicode character escape")
            val codePoint = hex.toLong(16).toInt()
            if (codePoint !in 0..0x10ffff || codePoint in 0xd800..0xdfff)
                throw RuntimeGoError("invalid Unicode code point")
            codePoint
        }
        in '0'..'7' -> {
            if (escape.length != 3 || !escape.all { it in '0'..'7' })
                throw RuntimeGoError("invalid octal character escape")
            val value = escape.toInt(8)
            if (value > 0xff) throw RuntimeGoError("octal character escape out of range")
            value
        }
        else -> throw RuntimeGoError("invalid character escape")
    }
}

private fun Char.isHexDigit(): Boolean = this in '0'..'9' || this in 'a'..'f' || this in 'A'..'F'

internal fun decodeGoStringLiteralBytes(text: String): ByteArray {
    if (text.length < 2) throw RuntimeGoError("invalid string literal")
    if (text.first() == '`') return text.substring(1, text.length - 1).replace("\r", "").toByteArray(Charsets.UTF_8)
    val body = text.substring(1, text.length - 1)
    val bytes = mutableListOf<Byte>()
    fun appendCodePoint(codePoint: Int) { bytes += encodeGoCodePoint(codePoint).toList() }
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
                if (codePoint in 0xd800..0xdfff) throw RuntimeGoError("invalid Unicode code point")
                appendCodePoint(codePoint)
                i += digits
            }
            else -> throw RuntimeGoError("unknown escape sequence \\$escaped")
        }
    }
    return bytes.toByteArray()
}

internal fun encodeGoCodePoint(value: Int): ByteArray {
    val codePoint = if (value in 0..0x10ffff) value else 0xfffd
    return when {
        codePoint <= 0x7f -> byteArrayOf(codePoint.toByte())
        codePoint <= 0x7ff -> byteArrayOf(
            (0xc0 or (codePoint shr 6)).toByte(),
            (0x80 or (codePoint and 0x3f)).toByte()
        )
        codePoint <= 0xffff -> byteArrayOf(
            (0xe0 or (codePoint shr 12)).toByte(),
            (0x80 or ((codePoint shr 6) and 0x3f)).toByte(),
            (0x80 or (codePoint and 0x3f)).toByte()
        )
        else -> byteArrayOf(
            (0xf0 or (codePoint shr 18)).toByte(),
            (0x80 or ((codePoint shr 12) and 0x3f)).toByte(),
            (0x80 or ((codePoint shr 6) and 0x3f)).toByte(),
            (0x80 or (codePoint and 0x3f)).toByte()
        )
    }
}

internal fun encodeGoCodePoint(value: Long): ByteArray =
    encodeGoCodePoint(if (value in 0..0x10ffff) value.toInt() else -1)

internal fun encodeGoCodePoint(value: BigInteger): ByteArray =
    encodeGoCodePoint(if (value >= BigInteger.ZERO && value <= BigInteger.valueOf(0x10ffff)) value.toInt() else -1)

internal fun encodeGoUtf8Text(text: String): ByteArray {
    val bytes = mutableListOf<Byte>()
    var offset = 0
    while (offset < text.length) {
        val first = text[offset++]
        val codePoint = if (Character.isHighSurrogate(first) && offset < text.length && Character.isLowSurrogate(text[offset]))
            Character.toCodePoint(first, text[offset++]) else first.code
        bytes += encodeGoCodePoint(codePoint).toList()
    }
    return bytes.toByteArray()
}

internal fun decodeGoUtf8Rune(bytes: ByteArray, offset: Int): Pair<Int, Int> {
    val first = bytes[offset].toInt() and 0xff
    if (first < 0x80) return first to 1
    fun continuation(index: Int) = index < bytes.size && (bytes[index].toInt() and 0xc0) == 0x80
    if (first in 0xc2..0xdf && continuation(offset + 1)) {
        val codePoint = ((first and 0x1f) shl 6) or (bytes[offset + 1].toInt() and 0x3f)
        return codePoint to 2
    }
    if (first in 0xe0..0xef && continuation(offset + 1) && continuation(offset + 2)) {
        val second = bytes[offset + 1].toInt() and 0xff
        if (first != 0xe0 || second >= 0xa0) {
            val codePoint = ((first and 0x0f) shl 12) or ((second and 0x3f) shl 6) or
                (bytes[offset + 2].toInt() and 0x3f)
            if (codePoint in 0xd800..0xdfff) return 0xfffd to 1
            return codePoint to 3
        }
    }
    if (first in 0xf0..0xf4 && continuation(offset + 1) && continuation(offset + 2) && continuation(offset + 3)) {
        val second = bytes[offset + 1].toInt() and 0xff
        if ((first != 0xf0 || second >= 0x90) && (first != 0xf4 || second <= 0x8f)) {
            val codePoint = ((first and 0x07) shl 18) or ((second and 0x3f) shl 12) or
                ((bytes[offset + 2].toInt() and 0x3f) shl 6) or (bytes[offset + 3].toInt() and 0x3f)
            return codePoint to 4
        }
    }
    return 0xfffd to 1
}

internal fun decodeGoUtf8Text(bytes: ByteArray): String = buildString {
    var offset = 0
    while (offset < bytes.size) {
        val (codePoint, width) = decodeGoUtf8Rune(bytes, offset)
        appendCodePoint(codePoint)
        offset += width
    }
}
