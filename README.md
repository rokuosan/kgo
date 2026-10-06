# kgo

An experimental Go 1.0 language implementation targeting the JVM, written in Kotlin.

The interpreter currently covers a growing Go 1.0 core: declarations and basic
type syntax, functions, scalar expressions, variables, assignments, `if`, `for`,
`switch`, `select`, `defer`, channels, goroutines, and string/channel `range`.
Composite literals, structs, arrays, slices, maps, indexing, slicing, and their
basic built-ins (`make`, `append`, `copy`, `delete`, `len`, and `cap`) are also
implemented in the runtime subset. Named struct methods support value and pointer
receivers for the implemented runtime types.
Function literals capture their surrounding variables, and variadic functions
accept both individual arguments and slice expansion with `...`.
Labeled `break` and `continue` statements can target enclosing loops and
switch/select statements as permitted by their branch kind. `goto` supports
same-block and outward jumps, and rejects jumps into blocks or over variable
declarations.
Goroutines use `kotlinx.coroutines`; channel operations suspend through Kotlin
channels. The `fmt` calls are a small runtime shim, not the Go standard library.
Before execution, a static checker validates function signatures, declared
types, initializers, and many expression and statement type rules. It is still
an incomplete subset of the Go 1.0 type system.

```sh
./gradlew run --args='hello.go'          # execute package main
./gradlew run --args='--tokens hello.go' # inspect scanner output
./gradlew run --args='--parse hello.go'  # parse and summarize declarations
```

This is ongoing work toward the March 2012 Go 1.0 language specification.
Empty-interface values and type assertions are supported for the runtime types
currently represented, but non-empty interface method sets and assignment rules
are incomplete. Full package resolution and standard-library/runtime support
are also missing. Go features added after Go 1.0, such as generics and later
literal syntax, are out of scope. The project builds and runs on JDK 27 with Gradle
9.6.1 and Kotlin 2.4.20. Kotlin currently emits JVM 26 bytecode, which runs on
JDK 27. `kotlinx.coroutines` provides the goroutine runtime.
