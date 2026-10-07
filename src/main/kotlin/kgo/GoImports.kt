package kgo

import java.nio.ByteBuffer
import java.nio.charset.CodingErrorAction

/** A source-file import with its decoded path and effective package name. */
internal data class GoImportBinding(
    val specification: ImportSpecSyntax,
    val path: String,
    val alias: String
)

internal fun ImportSpecSyntax.decodedPath(): String {
    val pathBytes = decodeGoStringLiteralBytes(path)
    return try {
        Charsets.UTF_8.newDecoder()
            .onMalformedInput(CodingErrorAction.REPORT)
            .onUnmappableCharacter(CodingErrorAction.REPORT)
            .decode(ByteBuffer.wrap(pathBytes))
            .toString()
    } catch (_: java.nio.charset.CharacterCodingException) {
        throw RuntimeGoError("import path is not valid UTF-8")
    }
}

internal fun GoFile.importBindings(packageNames: Map<String, String> = emptyMap()): List<GoImportBinding> =
    declarations.filterIsInstance<ImportDeclaration>().flatMap { declaration ->
        declaration.imports.map { specification ->
            val path = specification.resolvedPath ?: specification.decodedPath()
            val alias = specification.alias ?: packageNames[path] ?: path.substringAfterLast('/')
            GoImportBinding(specification, path, alias)
        }
    }
