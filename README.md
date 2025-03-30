# Rattlesnake 🐍

Simple procedural programming language, statically typed and compiled to JVM bytecode

## Warning ⚠️

⚠️ This version of the language (0.1) is no longer maintained. The compiler has known bugs, in particular regarding the order in which operands are evaluated. See other branches of this repo for more recent versions of the language.

## Example project

A sudoku solver: https://github.com/ValentinAebi/Rattlesnake-sudoku-solver

## Example program
```
fn joinWords(words: arr String, endSymbol: Char) -> String {
    var joined = "";
    for var i = 0; i < #words; i += 1 {
        joined += words[i];
        if i < #words-1 {
            joined += " ";
        }
    };
    return joined + charToString(endSymbol)
}

fn main(arr String){
    val msgWords = ["Hello", "world"];
    val msg = joinWords(msgWords, '!');
    print(msg)   // displays "Hello world!"
}

```

[Compiler documentation here](CompilerDoc.md)

## Command-line program

Run `help` to see the available commands and options

## Language description

The language does not support modules. All functions and data structures are top-level and identified by their textual name across the whole program. Functions and types can be referred to from inside the file that defines them or from another file in the exact same way.

### Code blocks

Statements are separated with `;`. `;` may be omitted after the last statement.

### Types and data structures

- Primitive types:
    - `Int`, `Double`, `Bool`, `Char`
    - `Void`: return type of a function that does not return any value
    - `Nothing`: return type of a function that terminates the program and thus never returns

- `String`

- Arrays: `arr <element type>`, e.g. `arr Int`

    Creation:
    - `arr <type>[<size>]`, e.g. `val array = arr Int[10]` (such an array is always mutable)
    - `[<elems>*]`, e.g. `val array = [-7, 31, 14, 11]` <br> (or `val array = mut [-7, 31, 14, 11]` if the array must be mutable)
    
    Access an element: `<array>[<index>]`, e.g. `xs[7]`
    
- Structures, e.g. `struct Foo { bar: Int }`
  
  Fields are unmodifiable by default. Reassignable fields must be marked with `var`, e.g. `struct Abc { x: Int, var y: Int }`
    
  Creation and field access: `val foo = new Foo { 0 }; val b = foo.bar`
  
  Creating a mutable structure: `new mut Abc { 10, 15 }`

- Interfaces, e.g. `interface I { x: Int, var s: String }`

  The subtyping relation between structures and interfaces must be declared explicitely: `struct A : I { x: Int, y: Double, var s: String }`.
  The structure must then provide at least the fields declared by the interface. If a field is declared reassignable in an interface (`var` keyword),
  then it must be reassignable in the structure as well. If a structure `A` is a subtype of an interface `I`, then the fields of `A` declared in `I` and non-reassignable in `I`
  must declare a type that is a subtype of their type in `I`. If a field is reassignable in `I`, then it must declare the exact same type as in `I`. E.g.,
  assuming the existence of an interface `Z` and a struct `U` that is a subtype of `Z` (denoted `U <: Z` in the following snippet):
  ```
  // We assume the existence of U and Z such that U <: Z
  interface I { f: Z, var g: Z }
  struct A : I { f: Z, var h: String, var g: Z } // valid, extends I with an additional field h
  struct B : I { f: U, var g: Z }                // valid, U <: Z and f is not reassignable
  struct C : I { f: U, var g: U }                // not valid, as U != Z and g is reassignable
  struct D : I { f: Z, g: Z }                    // not valid, as g is reassignable in I but not in D
  ```
  

### Subtyping

- `Nothing` is a subtype of all other types
- `mut X` is a subtype of `X` (but not the other way around)
- arrays are covariant iff they are immutable (e.g. `arr mut Foo` is a subtype of `arr Foo` but `mut arr mut Foo` is not a subtype of `mut arr Foo`)
- the subtyping relation between structures and interfaces is declared explicitely

### Functions

```
fn <function name>(<args>*) -> <return type> {
   ...
}
```
Return type can be omitted if it is `Void`

E.g.:
```
fn bar(i: Int, b: Bool) -> String {
   ...
   return "Hello"
}
```
A non-void function must contain a `return <value>` for each control-flow path in the function. If the function has return type `Void`, then `return` is not required but may be used (without a value) for early exit.

Parameters may not be named. This is particularly useful for the `main` function when the program ignores its arguments (as unused named parameters produce a warning):
```
fn main(arr String){
  ...
}
```

### Locals

```
val <name>: <type> = ...
```
Type may be omitted in almost all cases, except if the right hand-side is a ternary operation involving a complex hierarchy of structures and interfaces. `var`s are defined similarly.
E.g.:
```
val x: Int = 0;
val str = "Rattlesnake";
```
`var`s (but not `val`s) can be reassigned: `x = <new value>`

### Constants

Constants can only be of primitive types. Their name must be lowercase.
```
const <name>: <type> = <value>
```
Type may be omitted, e.g. `const anwser = 42`


### Control structures

#### If-else
```
if <cond> {
   ...
} else if <cond> {
   ...
} else {
   ...
}
```
or without `else` branch:
```
if <cond> {
   ...
}
```

#### While loop
```
while <cond> {
   ...
}
```

#### For loop
```
for <stat>;<cond>;<stat> {
   ...
}
```
E.g.:
```
for var i = 0; i < #array; i += 1 {
   ...
}
```

#### Tail calls

Tail calls are eliminated only if explicitly requested. 
This is done by adding `!` between the name of the called 
function and the parameters list: `recurse!(arg1, arg2)`.


### Operators

#### Unary operators
- `-`: opposite of an `Int` or a `Double`
- `!`: logical negation of a `Bool`
- `#`: length operator for `String`s and arrays

#### Binary operators
- Mathematical: `+`, `-`, `*`, `/`, `%` (can be combined with `=`: `+=`, `/=`, etc.)
- Comparisons (between `Int`s or `Double`s): `<`, `>`, `>=`, `<=`
- Equality: `==`, `!=` (strings are compared by structure, `struct`s are compared by reference)
- Logical: `&&`, `||` (implement lazy evaluation of second operand)
- String concatenation: `+`

#### Ternary operator
```
when <cond> then <expr1> else <expr2>
```

#### Cast/type conversion
Additionaly to casts, the following conversions can be performed:
- `Int` <-> `Char`
- `Int` <-> `Double`

Syntax: `<expr> as <type>`, e.g. `10 as Double`, `x as Foo`

#### Type tests and smartcasts

Syntax: `<expr> is <type>`

E.g.:
```
interface Foo {}
struct Bar : Foo { x: Int }
...
val f: Foo = ...
val t = when f is Bar then f.x else 0;    // smartcast on ternary operator
val condition = f is Bar && f.x == 42;    // smartcast on &&
if (f is Bar){                            // smartcast on if statement
    ... = f.x;
}
```

#### Panic
Terminates the program with an exception:
`panic <message>`, e.g. <br> `panic "forbidden argument " + arg`

## Built-in functions

The compiler replaces calls to these functions with special instructions.

- `print(s: String)`: displays `s` on the console
- `?ToString(...)` with `?` one of `int`, `double`, `char`, `bool`, and the corresponding parameter type (e.g. `intToString(Int) -> String`): conversion to a string
- `toCharArray(s: String)`: converts a string into an array of all its characters (the returned array is mutable)

## Tests

Tests are defined similarly to functions, but `fn` is replaced by `test` and there is no parameters list. Failures are reported using `panic`:
```
test exampleTest {
    val i = 1 + 1;
    if i != 2 {
        panic "We have a problem!"
    }
}
```

## References

Lexer and parser are inspired from https://github.com/epfl-lara/silex and https://github.com/epfl-lara/scallion, respectively.

Backend uses the ASM bytecode manipulation library: https://asm.ow2.io/

