# Compiler documentation

**This documentation was written for a previous version of the compiler and is not up-to-date.**

## Compiler stages

1. Frontend (lexer + parser): runs separately on each source file and creates the AST
2. Imports scanner: fetches the packages and devices imported by each module definition
3. Context creator: creates an `AnalysisContext` that contains all the signatures of all the types and functions in the program
4. Type checker: performs type checking and writes the types of each expression into the AST
5. Control-flow analyzer: checks that non-Void functions always end with a `return` or `panic` and that locals are initialized before being read
6. Lowerer: transforms the AST to reduce the number of different constructs that the backend will have to handle
7. Tail recursions checker: checks that calls marked for elimination are in tail position
8. Backend: emits the bytecode
