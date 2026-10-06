# kgo

An experimental Go 1.0 language implementation targeting the JVM, written in Kotlin.

The interpreter currently covers a growing Go 1.0 core: declarations and basic
type syntax, functions, scalar expressions, variables, assignments, `if`, `for`,
`switch`, `select`, `defer`, channels, goroutines, and `range` over arrays,
pointers to arrays, slices, maps, strings, and channels.
Complex values, complex arithmetic, and the `complex`, `real`, and `imag`
built-ins are supported for represented numeric types.
`panic` and `recover` unwind deferred calls per goroutine, and `recover` succeeds
only when called directly from a deferred function.
Package constants and variables initialize in dependency order, including
dependencies reached through package functions.
Numeric constant expressions retain exact integer and rational values until a
concrete numeric type is selected.
Composite literals, structs, arrays, slices, maps, indexing, slicing, and their
basic built-ins (`make`, `append`, `copy`, `delete`, `len`, and `cap`) are also
implemented in the runtime subset. Pointers to arrays support indexing,
slicing, and ranging. Named struct, scalar, array, slice, map, channel, and
function types retain method receiver information for value and pointer
receiver dispatch. Method expressions on named types and pointers expose the
receiver as their first function argument.
Method calls and bound method values are supported.
Array and struct comparisons use Go value equality, including when they are used
as map keys. Arrays and structs copy at value-transfer points; slices, maps,
channels, and pointers keep their reference semantics.
Function literals capture their surrounding variables, and variadic functions
accept both individual arguments and slice expansion with `...`.
Named result parameters are local variables; empty `return` uses their current
values after deferred calls run.
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
./gradlew run --args='src/example'       # execute a package from its .go files
```

This is ongoing work toward the March 2012 Go 1.0 language specification.
Identifier letters and decimal digits use the Unicode 6.0 categories specified
by Go 1.0, rather than the host JDK's current Unicode tables.
Empty and basic non-empty interface values use method-set checks for declared
methods on named types, with value and pointer receiver dispatch. Embedded
struct-field and interface-method promotion follow breadth-first selector
lookup. Some interface assignment cases remain incomplete.
Interface type assertions and type switches are supported for the runtime
types currently represented, including typed nil pointers, slices, maps,
channels, and functions stored in interfaces. Nil slices and maps have their
specified zero-length behavior; nil channel operations block and are disabled
as `select` cases.
The command-line runner accepts a source file or a directory of `.go` files;
directory input combines files declaring the same package and ignores test files.
Import aliases are scoped to their source file during static checking. Full
imported-package resolution and standard-library/runtime support are also
missing. Bodyless function and method declarations are parsed and type-checked,
but their external implementations cannot be linked by the interpreter.
Go features added after Go 1.0, such as generics and later literal syntax, are
out of scope. The project builds and runs on JDK 27 with Gradle
9.8.0 and Kotlin 2.4.20. Kotlin currently emits JVM 26 bytecode, which runs on
JDK 27. `kotlinx.coroutines` provides the goroutine runtime.
