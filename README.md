# kgo

An experimental Go 1.0 language implementation targeting the JVM, written in Kotlin.

The first milestone is the lexical front end: Go 1.0 keywords, operators, literals,
comments, source locations, and automatic semicolon insertion. Run it with
`gradle run --args='path/to/file.go'` to inspect the token stream.

This is not yet a Go compiler or interpreter. The next layers are parsing, type
checking, and execution on the JVM. The language target is the March 2012 Go 1.0
specification, so newer features such as generics and later literal syntax are out
of scope.
