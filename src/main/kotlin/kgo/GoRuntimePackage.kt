package kgo

/** The Go 1.0 runtime declarations required by the language specification. */
internal object GoRuntimePackage {
    private val errorType = InterfaceGoType(
        listOf(InterfaceMethodSyntax("RuntimeError", emptyList(), emptyList())),
        listOf(NamedGoType("error"))
    )

    val exportedTypes = setOf("Error")

    fun type(name: String): GoTypeSyntax? = when (name) {
        "Error" -> errorType
        else -> null
    }
}
