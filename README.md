# The Licorne programming language 🦄

Licorne is an experimental programming language exploring refinement types and language-based support for lightweight verification.
Its syntax is heavily inspired from Kotlin, of which Licorne can be considered a dialect. Beside Kotlin, Licorne draws some inspiration from Scala, which is also the implementation language of the compiler.

Some of Licorne's features:
 - Refinement types: `Int with it % 2 == 0`
 - Dependent integer range types, treated as a restricted form of refinement types: `[0 ..< array.length()]`
 - Nullability aware types (non-nullability is partly treated as a refinement): `T?`
 - Function-wide bidirectional type inference (see for instance the `reverse` and `filter` methods in [the OOP lists example](./licorne-compiler/src/test/res/analyzer-tests/lists_oop_style.lic))
 - Smart casts (think of Kotlin's smart casts, but generalized to refinement types)
 - Automated type simplification
 - Constrained generics, with covariance and contravariance: `Foo[out/in TypeParam : UpperBound super LowerBound]` (note that unlike Kotlin, Licorne uses square brackets instead of angle brackets for generics, as it's pretty hard for the parser to distinguish a closing `>` from a `>` arithmetic operator when the last type argument of the list is a refined type)
 - Union and intersection types: `A | B`, `A & B`
 - Explicit method preconditions


## Code examples

Code examples can be found in the test resource directories 
[here (typecheck tests)](licorne-compiler/src/test/res/analyzer-tests) and 
[here (full compilation tests)](licorne-compiler/src/test/res/execution-tests).


## Build and run

*These instructions are best effort and might not be up-to-date. In case of doubt please consider referring to the [CI workflow file](./.github/workflows/ci.yml).*

To build the compiler, run `sbt clean assembly` in the [`licorne-compiler` directory](./licorne-compiler). The Licorne compiler can then be found as a jar file in the [`licorne-compiler/target/scala-<version>` directory](./licorne-compiler/target/scala-3.8.0).

To type-check a program using the (jar of the) compiler, run `java -jar licorne-compiler.jar compile src_file.lic` (or `java -jar licorne-compiler.jar compile src/*` to compile all files in `./src`).

In order for the compiler to be able to find the sources of the standard library, you need to set the `LICORNE_HOME` 
environment variable on the host machine, which should point to this directory. 
Alternatively, you can use the `licorne-root` compiler flag.

If you want to use the parts of the standard library that are written in Java (currently only file IO), you need to compile them separately, using `javac`. 
For those, Licorne expects the class files to be in the same directory as the corresponding Java source files.

Compiler help command: `java -jar .\licorne-compiler.jar help`


## SMT solver integration

Licorne uses [Z3](https://github.com/z3prover/z3) via the [KSMT](https://github.com/UnitTestBot/ksmt) API. KSMT bundles Z3 into the compiler jar, so there is no need to install it separately.


## Papers

[Practical range refinement types with inference](https://arxiv.org/abs/2607.00824) (SEFM 2026)


## Project name and history

"Licorne" stands for "<b>L</b>ightweight <b>I</b>nferen<b>C</b>e <b>O</b>f <b>R</b>efi<b>NE</b>ments", and means "unicorn" in French.

Earlier versions of Licorne were called Rattlesnake and [Grattlesnake](https://github.com/epfl-systemf/grattlesnake-lang), the former being a very simple toy language, and the latter being part of my master's thesis work on gradual object capabilities. They can be found as secondary branches of this repository.
