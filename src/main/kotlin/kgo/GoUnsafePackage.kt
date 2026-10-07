package kgo

import java.math.BigInteger

/** Go 1.0 unsafe intrinsics and the 64-bit data layout used by this JVM target. */
internal object GoUnsafePackage {
    private val uintptr = NamedGoType("uintptr")
    private val any = InterfaceGoType(emptyList())

    private val functions = setOf("Sizeof", "Alignof", "Offsetof")
    private val types = setOf("Pointer")

    val exportedNames: Set<String> get() = functions + types
    val exportedTypes: Set<String> get() = types

    fun constant(name: String): BigInteger? = null

    fun memberType(name: String): GoTypeSyntax? = when {
        functionType(name) != null -> functionType(name)
        name == "Pointer" -> QualifiedGoType("unsafe", name)
        else -> null
    }

    fun functionType(name: String): FunctionGoType? = if (name in functions)
        FunctionGoType(listOf(ParameterSyntax(null, any)), listOf(uintptr)) else null

    data class Layout(val size: Long, val align: Long)

    fun layout(
        type: GoTypeSyntax,
        underlying: (GoTypeSyntax) -> GoTypeSyntax,
        arrayLength: (Expression) -> BigInteger
    ): Layout = when (val actual = underlying(type)) {
        is NamedGoType -> when (actual.name) {
            "bool", "#predeclared-uint8", "int8", "uint8" -> Layout(1, 1)
            "int16", "uint16" -> Layout(2, 2)
            "int32", "uint32", "float32", "#predeclared-float32" -> Layout(4, 4)
            "#predeclared-int", "int64", "uint64", "int", "uint", "uintptr", "float64", "#predeclared-float64" -> Layout(8, 8)
            "complex64", "#predeclared-complex64" -> Layout(8, 4)
            "complex128", "#predeclared-complex128" -> Layout(16, 8)
            "string", "#predeclared-string" -> Layout(16, 8)
            else -> throw IllegalArgumentException("unknown Go type layout: $actual")
        }
        is PointerGoType, is MapGoType, is ChannelGoType, is FunctionGoType -> Layout(8, 8)
        is SliceGoType -> Layout(24, 8)
        is InterfaceGoType -> Layout(16, 8)
        is ArrayGoType -> {
            val length = actual.length?.let(arrayLength)?.longValueExact()
                ?: throw IllegalArgumentException("array type has no constant length")
            val element = layout(actual.element, underlying, arrayLength)
            Layout(Math.multiplyExact(length, element.size), element.align)
        }
        is StructGoType -> {
            var offset = 0L
            var alignment = 1L
            structFields(actual).forEach { (_, fieldType) ->
                val field = layout(fieldType, underlying, arrayLength)
                alignment = maxOf(alignment, field.align)
                offset = alignUp(offset, field.align)
                offset = Math.addExact(offset, field.size)
            }
            Layout(alignUp(offset, alignment), alignment)
        }
        is QualifiedGoType -> throw IllegalArgumentException("unknown Go type layout: $actual")
    }

    fun fieldOffset(
        type: GoTypeSyntax,
        name: String,
        underlying: (GoTypeSyntax) -> GoTypeSyntax,
        arrayLength: (Expression) -> BigInteger
    ): Pair<Long, GoTypeSyntax>? {
        data class Node(val type: GoTypeSyntax, val offset: Long, val ancestors: Set<String>)
        var level = listOf(Node(type, 0L, emptySet()))
        while (level.isNotEmpty()) {
            val found = mutableListOf<Pair<Long, GoTypeSyntax>>()
            val next = mutableListOf<Node>()
            level.forEach { node ->
                val struct = when (val actual = underlying(node.type)) {
                    is StructGoType -> actual
                    is PointerGoType -> underlying(actual.element) as? StructGoType
                    else -> null
                } ?: return@forEach
                var fieldOffset = 0L
                struct.fields.forEach { source ->
                    expandedFieldNames(source).forEach { fieldName ->
                        val fieldType = source.type
                        val fieldLayout = layout(fieldType, underlying, arrayLength)
                        fieldOffset = alignUp(fieldOffset, fieldLayout.align)
                        val absoluteOffset = Math.addExact(node.offset, fieldOffset)
                        if (fieldName == name) found += absoluteOffset to fieldType
                        if (source.names.isEmpty()) {
                            val key = source.type.toString()
                            if (key !in node.ancestors) next += Node(source.type, absoluteOffset, node.ancestors + key)
                        }
                        fieldOffset = Math.addExact(fieldOffset, fieldLayout.size)
                    }
                }
            }
            if (found.isNotEmpty()) return found.singleOrNull()
            level = next
        }
        return null
    }

    private fun structFields(type: StructGoType): List<Pair<String, GoTypeSyntax>> = type.fields.flatMap { field ->
        expandedFieldNames(field).map { it to field.type }
    }

    private fun expandedFieldNames(field: StructFieldSyntax): List<String> = field.names.ifEmpty {
        listOf(embeddedName(field.type))
    }

    private fun embeddedName(type: GoTypeSyntax): String = when (type) {
        is NamedGoType -> type.name
        is QualifiedGoType -> type.name
        is PointerGoType -> embeddedName(type.element)
        else -> ""
    }

    private fun alignUp(value: Long, alignment: Long): Long {
        val remainder = value % alignment
        return if (remainder == 0L) value else Math.addExact(value, alignment - remainder)
    }
}
