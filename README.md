# kgo

An experimental Go 1.0 language implementation targeting the JVM, written in Kotlin.

The current vertical slice scans and parses a Go source file, then interprets a
small executable core: functions, integer/string/boolean expressions, variables,
assignments, `if`, `for`, returns, and basic `print`/`fmt.Print*` calls.

```sh
./gradlew run --args='hello.go'          # execute package main
./gradlew run --args='--tokens hello.go' # inspect scanner output
./gradlew run --args='--parse hello.go'  # parse and summarize declarations
```

This is ongoing work toward the March 2012 Go 1.0 language specification. Static
type checking, most types and declarations, packages, and complete runtime support
are still missing. Go features added after Go 1.0, such as generics and later
literal syntax, are out of scope. The project builds and runs on JDK 27 with
Gradle 9.6.1 and Kotlin 2.4.20. Kotlin currently emits JVM 26 bytecode, which runs
on JDK 27. `kotlinx.coroutines` is included for the planned goroutine runtime.
