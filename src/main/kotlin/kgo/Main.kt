package kgo

import java.io.File
import java.nio.ByteBuffer
import java.nio.charset.CodingErrorAction
import java.nio.charset.StandardCharsets

fun main(args: Array<String>) {
    val mode = args.firstOrNull()?.takeIf { it.startsWith("--") } ?: "--run"
    val path = if (mode == "--run") args.firstOrNull() else args.getOrNull(1)
    if (path == null || args.size > 2 || mode !in setOf("--run", "--tokens", "--parse")) {
        System.err.println("usage: kgo [--run|--parse|--tokens] <source.go|package-dir>")
        return
    }
    try {
        val source = File(path)
        val sourceFiles = if (source.isDirectory) {
            if (mode == "--tokens") throw GoTypeError("--tokens requires a source file")
            source.listFiles()
                ?.filter { it.isFile && it.extension == "go" && !it.name.startsWith(".") &&
                    !it.name.startsWith("_") && !it.name.endsWith("_test.go") }
                ?.sortedBy { it.name }
                ?: throw GoTypeError("cannot read package directory: $path")
        } else listOf(source)
        if (sourceFiles.isEmpty()) throw GoTypeError("no Go source files in $path")
        if (mode == "--tokens") {
            Lexer(readGoSource(source)).scan().forEach { token ->
                if (token.kind != TokenKind.EOF) println("${token.position.line}:${token.position.column}\t${token.kind}\t${token.lexeme}")
            }
            return
        }
        val files = sourceFiles.map { file -> Parser(Lexer(readGoSource(file)).scan()).parseFile() }
        val packageName = files.first().packageName
        if (files.any { it.packageName != packageName }) {
            throw GoTypeError("all source files in a package directory must declare package $packageName")
        }
        val file = GoFile(packageName, files.flatMap { it.declarations })
        if (mode == "--parse") println("package ${file.packageName}: ${file.declarations.size} declaration(s)")
        else {
            TypeChecker().checkFiles(files)
            Interpreter().run(file)
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

private fun readGoSource(file: File): String = try {
    StandardCharsets.UTF_8.newDecoder()
        .onMalformedInput(CodingErrorAction.REPORT)
        .onUnmappableCharacter(CodingErrorAction.REPORT)
        .decode(ByteBuffer.wrap(file.readBytes()))
        .toString()
} catch (_: java.nio.charset.CharacterCodingException) {
    throw GoTypeError("source file is not valid UTF-8: ${file.path}")
}
