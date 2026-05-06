## The Licorne 🦄 programming language

Licorne is an experimental programming language exploring refinement types and language-based support for lightweight verification.

The compiler supports parsing (although the parser is very basic), IR generation, type inference, and type-checking. It does not have a backend (yet).

Some features that are already supported:
 - Dependent range types
 - Bidirectional type inference
 - Kotlin-style smartcasts (including range types inference from branching conditions)
 - Explicit method preconditions
 - Kotlin-style nullable types

Code examples can be found in the [test resources directory](licorne-compiler/src/test/res/analyzer-tests).

Notes on naming: Licorne stands for "<b>L</b>anguage-level <b>I</b>nferen<b>C</b>e <b>O</b>f <b>R</b>efi<b>NE</b>ments", and means "unicorn" in French. Earlier versions of Licorne were called Rattlesnake (see the corresponding branch) and [Grattlesnake](https://github.com/epfl-systemf/grattlesnake-lang), the latter corresponding to my master's thesis work on gradual object capabilities.

