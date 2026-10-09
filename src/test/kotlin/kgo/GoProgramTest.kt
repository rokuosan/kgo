package kgo

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class GoProgramTest {
    @Test
    fun `copy from nil slice leaves destination unchanged`() {
        assertEquals(
            "0 [1 2 3]\n",
            runGo("""
                package main
                import "fmt"

                func main() {
                    destination := []int{1, 2, 3}
                    count := copy(destination, nil)
                    fmt.Println(count, destination)
                }
            """.trimIndent())
        )
    }

    @Test
    fun `copy to nil slice returns zero`() {
        assertEquals(
            "0 [1 2 3]\n",
            runGo("""
                package main
                import "fmt"

                func main() {
                    source := []int{1, 2, 3}
                    count := copy(nil, source)
                    fmt.Println(count, source)
                }
            """.trimIndent())
        )
    }

    @Test
    fun `copy with typed nil slices returns zero`() {
        assertEquals(
            "0 0\n",
            runGo("""
                package main
                import "fmt"

                func main() {
                    var source []int
                    destination := []int{1}
                    copiedFromNil := copy(destination, source)

                    var nilDestination []int
                    copiedToNil := copy(nilDestination, []int{2})
                    fmt.Println(copiedFromNil, copiedToNil)
                }
            """.trimIndent())
        )
    }

    @Test
    fun `copy rejects slices with different element types`() {
        val file = parseGo("""
            package main

            func main() {
                copy([]int{1}, []string{"x"})
            }
        """.trimIndent())

        assertFailsWith<GoTypeError> { TypeChecker().check(file) }
    }

    @Test
    fun `scanner inserts semicolon after a multiline block comment`() {
        val tokens = Lexer("package main /* newline\n inside */ func main() {} ").scan()

        assertEquals(
            listOf(TokenKind.PACKAGE, TokenKind.IDENT, TokenKind.SEMICOLON,
                TokenKind.FUNC, TokenKind.IDENT, TokenKind.LPAREN, TokenKind.RPAREN,
                TokenKind.LBRACE, TokenKind.RBRACE, TokenKind.SEMICOLON, TokenKind.EOF),
            tokens.map { it.kind }
        )
    }

    private fun parseGo(source: String): GoFile = Parser(Lexer(source).scan()).parseFile()

    private fun runGo(source: String): String {
        val output = StringBuilder()
        Interpreter(output = output::append).run(parseGo(source))
        return output.toString()
    }
}
