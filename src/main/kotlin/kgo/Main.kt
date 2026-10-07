package kgo

import java.io.File

fun main(args: Array<String>) {
    val explicitMode = args.firstOrNull()?.takeIf { it.startsWith("--") }
    val mode = explicitMode ?: "--run"
    val path = if (explicitMode == null) args.firstOrNull() else args.getOrNull(1)
    if (path == null || args.size > 2 || mode !in setOf("--run", "--tokens", "--parse")) {
        System.err.println("usage: kgo [--run|--parse|--tokens] <source.go|package-dir>")
        return
    }
    try {
        val source = File(path)
        val files = if (source.isDirectory) {
            if (mode == "--tokens") throw GoTypeError("--tokens requires a source file")
            parseGoFiles(source)
        } else listOf(parseGoFile(source))
        if (files.isEmpty()) throw GoTypeError("no Go source files in $path")
        if (mode == "--tokens") {
            Lexer(readGoSource(source)).scan().forEach { token ->
                if (token.kind != TokenKind.EOF) println("${token.position.line}:${token.position.column}\t${token.kind}\t${token.lexeme}")
            }
            return
        }
        val packageName = files.first().packageName
        if (files.any { it.packageName != packageName }) {
            throw GoTypeError("all source files in a package directory must declare package $packageName")
        }
        val file = GoFile(packageName, files.flatMap { it.declarations })
        if (mode == "--parse") println("package ${file.packageName}: ${file.declarations.size} declaration(s)")
        else {
            val sourceDirectory = if (source.isDirectory) source else source.parentFile ?: File(".")
            val packages = GoSourcePackageLoader(sourceDirectory).dependencies(files)
            val packageCheckers = linkedMapOf<String, TypeChecker>()
            packages.forEach { imported ->
                val checker = TypeChecker(packageCheckers)
                checker.checkFiles(imported.files)
                packageCheckers[imported.importPath] = checker
            }
            TypeChecker(packageCheckers).checkFiles(files)
            Interpreter().run(files, packages)
        }
    } catch (e: ScanError) {
        System.err.println(e.message)
        kotlin.system.exitProcess(1)
    } catch (e: ParseError) {
        System.err.println(e.message)
        kotlin.system.exitProcess(1)
    } catch (e: RuntimeGoError) {
        System.err.println(e.message)
        kotlin.system.exitProcess(1)
    } catch (e: GoTypeError) {
        System.err.println(e.message)
        kotlin.system.exitProcess(1)
    }
}
