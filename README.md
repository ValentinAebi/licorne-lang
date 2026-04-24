## The Rattlesnake programming language

The version of Rattlesnake on this branch is a work-in-progress experimental implementation of refinement types and language-based support for lightweight verification. For my master's thesis work (about gradual capabilities tracking), see the [v0.2 branch](https://github.com/ValentinAebi/Rattlesnake/tree/rattlesnake-v0.2-gradient), or its [mirror](https://github.com/epfl-systemf/grattlesnake-lang).

The compiler supports parsing (although the parser is very basic), IR generation, type inference, and type-checking. It currently has no backend.

Some features that are already supported:
 - Dependent range types
 - Bidirectional type inference
 - Kotlin-style smartcasts (including range types inference from branching conditions)
 - Explicit method preconditions
 - Kotlin-style nullable types

Code examples can be found in the [test resources directory](rattlesnake-compiler/src/test/res/analyzer-tests).

The runtime and agent are legacies from a previous version of the language. They currently have no function.
