package kgo

import java.io.File

fun main(args: Array<String>) {
    if (args.size != 1) {
        System.err.println("usage: kgo <source.go>")
        return
    }
    try {
        Lexer(File(args[0]).readText()).scan().forEach { token ->
            if (token.kind != TokenKind.EOF) println("${token.position.line}:${token.position.column}\t${token.kind}\t${token.lexeme}")
        }
    } catch (e: ScanError) {
        System.err.println(e.message)
        kotlin.system.exitProcess(1)
    }
}
