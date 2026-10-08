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
dependencies reached through package functions, methods, method values, and
promoted methods.
Numeric constant expressions retain exact integer and rational values until a
concrete numeric type is selected.
Composite literals, structs, arrays, slices, maps, indexing, slicing, and their
basic built-ins (`make`, `append`, `copy`, `delete`, `len`, and `cap`) are also
implemented in the runtime subset. Pointers to arrays support indexing,
slicing, and ranging. Named struct, scalar, array, slice, map, channel, and
function types retain method receiver information for value and pointer
receiver dispatch. Method expressions on named types, pointers, and interfaces
expose the receiver as their first function argument.
Bound method values evaluate and save their receiver when the selector is
evaluated; the resulting function value can be called later.
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
Goroutines use `kotlinx.coroutines`; Go channel buffers and wait queues are
managed by the interpreter, and channel operations suspend through coroutine
continuations. The `fmt` calls are a small runtime shim, not the Go standard library;
its `Print`, `Println`, `Fprint`, and `Fprintln` functions can also be dot-imported.
Select cases register with the channel wait queues under a shared coordinator,
so a select cannot match its own send and receive cases and ready cases can
resume without polling.
The `Print` variants follow Go's adjacent-string spacing rule, and the `Fprint`
variants call the writer's `Write([]byte)` method.
The `math` import exposes the Go 1.0 constants and function signatures. JVM math
operations handle the elementary functions, while Apache Commons Math provides
error and gamma functions; Bessel Y functions use an in-runtime approximation.
The `unsafe` import implements Go 1.0's `Sizeof`, `Alignof`, and `Offsetof`
intrinsics and `Pointer` using a fixed 64-bit Go data layout on the JVM.
Intrinsic arguments are type-checked but not evaluated, and their `uintptr`
results can be used as constants. Pointer and `uintptr` conversions use
interpreter-managed addresses.
The `runtime` import exposes the Go 1.0 `Error` interface with its
`String() string` method for run-time panic values.
Before execution, a static checker validates function signatures, declared
types, initializers, and many expression and statement type rules. It is still
an incomplete subset of the Go 1.0 type system. The Go 1.0 specification leaves
the exact return requirement undefined; this checker follows the Go compiler's
terminating-statement rules for functions with results, including terminating
`if`, `switch`, `select`, and unconditional `for` statements.
Constant comparisons retain the untyped boolean result. A boolean type required
by the surrounding context determines the comparison result type.

```sh
./gradlew run --args='hello.go'          # execute package main
./gradlew run --args='--tokens hello.go' # inspect scanner output
./gradlew run --args='--parse hello.go'  # parse and summarize declarations
./gradlew run --args='src/example'       # execute a package from its .go files
```

This is ongoing work toward the [Go 1.0 language specification, version of
March 17, 2012](https://go.googlesource.com/go/+/6174b5e21e73714c63061e66efdbe180e1c5491d/doc/go_spec.html),
published with the Go 1 release.
Identifier letters and decimal digits use the Unicode 6.0 categories specified
by Go 1.0, rather than the host JDK's current Unicode tables. In Go 1.0, `rune`
is an alias for `int32`; the implementation uses its documented 64-bit `int`
layout.
Empty and basic non-empty interface values use method-set checks for declared
methods on named types, with value and pointer receiver dispatch. Embedded
struct-field and interface-method promotion follow breadth-first selector
lookup. Some interface assignment cases remain incomplete.
Unexported interface methods are identified by their declaring package path.
Untyped constants assigned to empty interfaces use their default types.
Non-constant shifts of untyped rune constants default to `rune`.
Interface type assertions and type switches are supported for the runtime
types currently represented, including typed nil pointers, slices, maps,
channels, and functions stored in interfaces. Nil slices and maps have their
specified zero-length behavior; nil channel operations block and are disabled
as `select` cases.
The command-line runner accepts a source file or a directory of `.go` files;
directory input combines files declaring the same package and ignores test files.
Import aliases are scoped to their source file during static checking and
execution. Local source packages can be loaded from relative paths, a `go.mod`
module path, or `GOPATH/src`; exported functions, constants, and variables can
be accessed through named or dot imports, and dependencies initialize before
their importers. Exported package types can be named, converted, and used in
composite literals; exported methods on those types can be called. Some
cross-package type details and general standard-library/runtime support are
still incomplete.
Bodyless function and method declarations are parsed and type-checked,
but their external implementations cannot be linked by the interpreter.
Go features added after Go 1.0, such as generics and later literal syntax, are
out of scope. The project builds and runs on JDK 27 with Gradle
9.7.1 and Kotlin 2.4.20. Kotlin currently emits JVM 26 bytecode, which runs on
JDK 27. `kotlinx.coroutines` provides the goroutine runtime.
