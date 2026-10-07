package kgo

/** Go 1.0 math package declarations exposed by the JVM runtime. */
internal object GoMathPackage {
    private val float64 = NamedGoType("float64")
    private val float32 = NamedGoType("float32")
    private val int = NamedGoType("int")
    private val bool = NamedGoType("bool")
    private val integerConstants = setOf(
        "MaxInt8", "MinInt8", "MaxInt16", "MinInt16", "MaxInt32", "MinInt32", "MaxInt64", "MinInt64",
        "MaxUint8", "MaxUint16", "MaxUint32", "MaxUint64"
    )

    val constants = linkedMapOf(
        "E" to "2.71828182845904523536028747135266249775724709369995957496696763",
        "Pi" to "3.14159265358979323846264338327950288419716939937510582097494459",
        "Phi" to "1.61803398874989484820458683436563811772030917980576286213544862",
        "Sqrt2" to "1.41421356237309504880168872420969807856967187537694807317667974",
        "SqrtE" to "1.64872127070012814684865078781416357165377610071014801157507931",
        "SqrtPi" to "1.77245385090551602729816748334114518279754945612238712821380779",
        "SqrtPhi" to "1.27201964951406896425242246173749149171560804184009624861664038",
        "Ln2" to "0.693147180559945309417232121458176568075500134360255254120680009",
        "Log2E" to "1.44269504088896340735992468100189213742664595415298593413544941",
        "Ln10" to "2.30258509299404568401799145468436420760110148862877297603332790",
        "Log10E" to "0.43429448190325182765112891891660508229439700580366656611445378",
        "MaxFloat32" to "3.40282346638528859811704183484516925440e+38",
        "SmallestNonzeroFloat32" to "1.401298464324817070923729583289916131280e-45",
        "MaxFloat64" to "1.797693134862315708145274237317043567981e+308",
        "SmallestNonzeroFloat64" to "4.940656458412465441765687928682213723651e-324",
        "MaxInt8" to "127",
        "MinInt8" to "-128",
        "MaxInt16" to "32767",
        "MinInt16" to "-32768",
        "MaxInt32" to "2147483647",
        "MinInt32" to "-2147483648",
        "MaxInt64" to "9223372036854775807",
        "MinInt64" to "-9223372036854775808",
        "MaxUint8" to "255",
        "MaxUint16" to "65535",
        "MaxUint32" to "4294967295",
        "MaxUint64" to "18446744073709551615"
    )

    private val functions: Map<String, FunctionGoType> = buildMap {
        val unary = setOf(
            "Abs", "Acos", "Acosh", "Asin", "Asinh", "Atan", "Atanh", "Cbrt", "Ceil", "Cos", "Cosh", "Exp", "Exp2",
            "Expm1", "Floor", "Log", "Log10", "Log1p", "Log2", "Sin", "Sinh", "Sqrt",
            "Tan", "Tanh", "Trunc"
        )
        unary.forEach { put(it, FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64))) }
        setOf("Atan2", "Copysign", "Dim", "Hypot", "Max", "Min", "Mod", "Pow", "Remainder")
            .forEach { put(it, FunctionGoType(List(2) { ParameterSyntax(null, float64) }, listOf(float64))) }
        setOf("Erf", "Erfc", "Gamma", "J0", "J1", "Y0", "Y1")
            .forEach { put(it, FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64))) }
        put("Jn", FunctionGoType(listOf(ParameterSyntax(null, int), ParameterSyntax(null, float64)), listOf(float64)))
        put("Yn", FunctionGoType(listOf(ParameterSyntax(null, int), ParameterSyntax(null, float64)), listOf(float64)))
        put("IsNaN", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(bool)))
        put("IsInf", FunctionGoType(listOf(ParameterSyntax(null, float64), ParameterSyntax(null, int)), listOf(bool)))
        put("Signbit", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(bool)))
        put("Inf", FunctionGoType(listOf(ParameterSyntax(null, int)), listOf(float64)))
        put("NaN", FunctionGoType(emptyList(), listOf(float64)))
        put("Sincos", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64, float64)))
        put("Modf", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64, float64)))
        put("Frexp", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64, int)))
        put("Ldexp", FunctionGoType(listOf(ParameterSyntax(null, float64), ParameterSyntax(null, int)), listOf(float64)))
        put("Ilogb", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(int)))
        put("Logb", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64)))
        put("Pow10", FunctionGoType(listOf(ParameterSyntax(null, int)), listOf(float64)))
        put("Nextafter", FunctionGoType(List(2) { ParameterSyntax(null, float64) }, listOf(float64)))
        put("Lgamma", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(float64, int)))
        put("Float32bits", FunctionGoType(listOf(ParameterSyntax(null, float32)), listOf(NamedGoType("uint32"))))
        put("Float32frombits", FunctionGoType(listOf(ParameterSyntax(null, NamedGoType("uint32"))), listOf(float32)))
        put("Float64bits", FunctionGoType(listOf(ParameterSyntax(null, float64)), listOf(NamedGoType("uint64"))))
        put("Float64frombits", FunctionGoType(listOf(ParameterSyntax(null, NamedGoType("uint64"))), listOf(float64)))
    }

    val exportedNames: Set<String> get() = constants.keys + functions.keys
    fun memberType(name: String): GoTypeSyntax? = when {
        name in integerConstants -> NamedGoType("#untyped-int")
        name in constants -> NamedGoType("#untyped-float")
        else -> functions[name]
    }
    fun functionType(name: String): FunctionGoType? = functions[name]
    fun constant(name: String): String? = constants[name]
}
