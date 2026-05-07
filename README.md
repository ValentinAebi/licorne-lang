# The Licorne 🦄 programming language

Licorne is an experimental programming language exploring refinement types and language-based support for lightweight verification.

The compiler supports parsing (although the parser is very basic), IR generation, type inference, and type-checking. It does not have a backend (yet).

Some features that are already supported:
 - Dependent range types
 - General refinement types
 - Bidirectional type inference
 - Kotlin-style smartcasts (including range types inference from branching conditions)
 - Explicit method preconditions
 - Kotlin-style nullable types

Code examples can be found in the [test resources directory](licorne-compiler/src/test/res/analyzer-tests).

## Build and run

To build the compiler, run `sbt assembly` in the [licorne-compiler](./licorne-compiler) directory.

To type-check a program using the (jar of the) compiler, run `java -jar <jar-name> compile src_file.lic` (or `java -jar <jar-name> compile src/*` to compile all files in `./src`).

## Additional notes

SMT solver integration: the compiler uses [Z3](https://github.com/z3prover/z3) via the [KSMT](https://github.com/UnitTestBot/ksmt) API.

Notes on naming: Licorne stands for "<b>L</b>anguage-level <b>I</b>nferen<b>C</b>e <b>O</b>f <b>R</b>efi<b>NE</b>ments", and means "unicorn" in French. Earlier versions of Licorne were called Rattlesnake and [Grattlesnake](https://github.com/epfl-systemf/grattlesnake-lang), the former being a very simple toy language, and the latter corresponding to my master's thesis work on gradual object capabilities. They can be found on other branches of this repository.

