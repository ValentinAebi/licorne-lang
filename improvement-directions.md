# Improvement directions

**This documentation was written for a previous version of the compiler and is not up-to-date.**

## Language features

- Support for closures and heap-allocated variables
- Support for interfaces that modules may implement
- Make `panic` an expression of type `Nothing` rather than a statement
- Support for basic expressions in constants initializers


## Compiler improvements

- Make lowering phase less aggressive (this produces overcomplicated bytecode)
- Add an optimizer


