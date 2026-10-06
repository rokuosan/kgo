plugins {
    kotlin("jvm") version "2.4.20"
    application
}

group = "dev.rokuosan"
version = "0.1.0"

repositories { mavenCentral() }

kotlin {
    jvmToolchain(27)
    compilerOptions {
        // Kotlin 2.4.20 runs on JDK 27 but currently emits bytecode through JVM 26.
        jvmTarget.set(org.jetbrains.kotlin.gradle.dsl.JvmTarget.JVM_26)
    }
}

java {
    sourceCompatibility = JavaVersion.VERSION_26
    targetCompatibility = JavaVersion.VERSION_26
}

dependencies {
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.11.0")
}

application { mainClass.set("kgo.MainKt") }
