package kgo

/** The Go 1.0 runtime declarations required by the language specification. */
internal object GoRuntimePackage {
    private val errorType = InterfaceGoType(
        listOf(InterfaceMethodSyntax("String", emptyList(), listOf(NamedGoType("string")))),
        listOf(NamedGoType("#predeclared-error"))
    )

    val exportedTypes = setOf("Error")

    fun type(name: String): GoTypeSyntax? = when (name) {
        "Error" -> errorType
        else -> null
    }
}
