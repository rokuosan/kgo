package kgo

import java.io.File
import java.nio.ByteBuffer
import java.nio.charset.CodingErrorAction
import java.nio.charset.StandardCharsets

internal data class GoSourcePackage(
    val importPath: String,
    val directory: File,
    val packageName: String,
    val files: List<GoFile>
)

/** Loads local Go source dependencies using relative paths, a go.mod module path, or GOPATH. */
internal class GoSourcePackageLoader(entryDirectory: File) {
    private val entryDirectory = entryDirectory.canonicalFile
    private val module = findModule(this.entryDirectory)
    private val states = mutableMapOf<String, Int>()

    fun dependencies(files: List<GoFile>): List<GoSourcePackage> {
        val order = mutableListOf<GoSourcePackage>()
        files.flatMap { it.importBindings() }.forEach { binding ->
            visit(binding.path, entryDirectory, order)
        }
        return order
    }

    private fun visit(path: String, importerDirectory: File, order: MutableList<GoSourcePackage>) {
        if (path == "fmt" || path == "math") return
        when (states[path]) {
            2 -> return
            1 -> throw GoTypeError("import cycle involving $path")
        }
        states[path] = 1
        val directory = resolve(path, importerDirectory)
            ?: throw GoTypeError("cannot locate imported package $path")
        val files = parseGoFiles(directory)
        if (files.isEmpty()) throw GoTypeError("no Go source files in imported package $path")
        val packageName = files.first().packageName
        if (files.any { it.packageName != packageName })
            throw GoTypeError("source files in imported package $path declare different package names")
        val loaded = GoSourcePackage(path, directory, packageName, files)
        files.flatMap { it.importBindings() }.forEach { binding -> visit(binding.path, directory, order) }
        states[path] = 2
        order += loaded
    }

    private fun resolve(path: String, importerDirectory: File): File? {
        val candidates = buildList {
            if (path.startsWith("./") || path.startsWith("../")) {
                add(importerDirectory.resolve(path))
            } else {
                add(importerDirectory.resolve(path))
                module?.let { (root, modulePath) ->
                    if (path == modulePath) add(root)
                    else if (path.startsWith("$modulePath/")) add(root.resolve(path.removePrefix("$modulePath/")))
                }
                System.getenv("GOPATH")?.split(File.pathSeparatorChar)?.filter(String::isNotBlank)?.forEach {
                    add(File(it).resolve("src").resolve(path))
                }
            }
        }
        return candidates.asSequence().mapNotNull { candidate ->
            runCatching { candidate.canonicalFile }.getOrNull()
        }.firstOrNull { it.isDirectory }
    }

    private fun findModule(directory: File): Pair<File, String>? {
        var current: File? = directory
        while (current != null) {
            val manifest = File(current, "go.mod")
            if (manifest.isFile) {
                val modulePath = runCatching {
                    manifest.useLines { lines ->
                        lines.map(String::trim).firstOrNull { it.startsWith("module ") }
                            ?.removePrefix("module ")?.trim()?.trim('"')
                    }
                }.getOrNull()
                if (!modulePath.isNullOrEmpty()) return current.canonicalFile to modulePath
            }
            current = current.parentFile
        }
        return null
    }
}

internal fun parseGoFiles(directory: File): List<GoFile> {
    val sourceFiles = directory.listFiles()
        ?.filter { it.isFile && it.extension == "go" && !it.name.startsWith(".") &&
            !it.name.startsWith("_") && !it.name.endsWith("_test.go") }
        ?.sortedBy { it.name }
        ?: throw GoTypeError("cannot read package directory: ${directory.path}")
    return sourceFiles.map(::parseGoFile)
}

internal fun parseGoFile(file: File): GoFile = Parser(Lexer(readGoSource(file)).scan()).parseFile()

internal fun readGoSource(file: File): String = try {
    StandardCharsets.UTF_8.newDecoder()
        .onMalformedInput(CodingErrorAction.REPORT)
        .onUnmappableCharacter(CodingErrorAction.REPORT)
        .decode(ByteBuffer.wrap(file.readBytes()))
        .toString()
} catch (_: java.nio.charset.CharacterCodingException) {
    throw GoTypeError("source file is not valid UTF-8: ${file.path}")
}
