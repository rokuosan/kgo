plugins {
    kotlin("jvm") version "2.2.20"
    application
}

group = "dev.rokuosan"
version = "0.1.0"

repositories { mavenCentral() }

kotlin { jvmToolchain(17) }

application { mainClass.set("kgo.MainKt") }
