package kgo

import java.io.File

fun main(args: Array<String>) {
    val mode = args.firstOrNull()?.takeIf { it.startsWith("--") } ?: "--run"
    val path = if (mode == "--run") args.firstOrNull() else args.getOrNull(1)
    if (path == null || args.size > 2 || mode !in setOf("--run", "--tokens", "--parse")) {
        System.err.println("usage: kgo [--run|--parse|--tokens] <source.go>")
        return
    }
    try {
        val tokens = Lexer(File(path).readText()).scan()
        when (mode) {
            "--tokens" -> tokens.forEach { token ->
                if (token.kind != TokenKind.EOF) println("${token.position.line}:${token.position.column}\t${token.kind}\t${token.lexeme}")
            }
            else -> {
                val file = Parser(tokens).parseFile()
                if (mode == "--parse") println("package ${file.packageName}: ${file.declarations.size} declaration(s)")
                else Interpreter().run(file)
            }
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
    }
}
