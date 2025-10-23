## The Rattlesnake programming language

This is a work-in-progress implementation of refinement types in the Rattlesnake experimental programming language.

See the other branches for more "stable" versions of the language.


## Library references

The lexer and the parser are inspired from https://github.com/epfl-lara/silex and https://github.com/epfl-lara/scallion, respectively (but they do not use these libraries).

The backend and the agent use the ASM bytecode manipulation library for code generation: https://asm.ow2.io/

The runtime uses the fastutil type-specific collection framework: https://fastutil.di.unimi.it/

