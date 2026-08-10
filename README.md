# The Licorne programming language 🦄

Licorne is an experimental programming language exploring refinement types and language-based support for lightweight verification.

The compiler is still only partially implemented. It supports parsing, IR generation, type inference, and type-checking. It does not have a backend (yet).

Some features that are already supported:
 - General refinement types
 - Dependent integer range types, treated as a restricted form of refinement types
 - Nullability aware types (non-nullability is partly treated as a refinement)
 - Function-wide bidirectional type inference
 - Smart casts (think of Kotlin's smart casts, but generalized to refinement types)
 - Explicit method preconditions

Code examples can be found in the [test resources directory](licorne-compiler/src/test/res/analyzer-tests).


## Build and run

To build the compiler, run `sbt clean assembly` in the [`licorne-compiler` directory](./licorne-compiler). The Licorne compiler can then be found as a jar file in the [`licorne-compiler/target/scala-<version>` directory](./licorne-compiler/target/scala-3.8.0).

To type-check a program using the (jar of the) compiler, run `java -jar licorne-compiler.jar compile src_file.lic` (or `java -jar licorne-compiler.jar compile src/*` to compile all files in `./src`).


## SMT solver integration

Licorne uses [Z3](https://github.com/z3prover/z3) via the [KSMT](https://github.com/UnitTestBot/ksmt) API. KSMT bundles Z3 into the compiler jar, so there is no need to install it separately.


## Why that name?

Licorne stands for "<b>L</b>ightweight <b>I</b>nferen<b>C</b>e <b>O</b>f <b>R</b>efi<b>NE</b>ments", and means "unicorn" in French. Earlier versions of Licorne were called Rattlesnake and [Grattlesnake](https://github.com/epfl-systemf/grattlesnake-lang), the former being a very simple toy language, and the latter corresponding to my master's thesis work on gradual object capabilities. They can be found as secondary branches of this repository.
