package kgo

/** Exported declarations provided by the interpreter's Go 1.0 fmt shim. */
internal object GoFmtPackage {
    private val any = InterfaceGoType(emptyList())
    private val variadic = ParameterSyntax(null, SliceGoType(any), variadic = true)
    private val int = NamedGoType("#predeclared-int")
    private val error = NamedGoType("error")
    private val byte = NamedGoType("#predeclared-uint8")
    private val writer = InterfaceGoType(listOf(
        InterfaceMethodSyntax(
            "Write",
            listOf(ParameterSyntax("p", SliceGoType(byte))),
            listOf(int, error)
        )
    ))

    val exportedNames = setOf("Print", "Println", "Fprint", "Fprintln")

    fun functionType(name: String): FunctionGoType? = when (name) {
        "Print", "Println" -> FunctionGoType(listOf(variadic), listOf(int, error))
        "Fprint", "Fprintln" -> FunctionGoType(listOf(ParameterSyntax(null, writer), variadic), listOf(int, error))
        else -> null
    }
}
