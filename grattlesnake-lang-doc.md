# The Grattlesnake programming language

**This documentation was written for a previous version of the language and is not up-to-date.**

## Language modes

Code must obey the ocap discipline by default (ocap mode). A file can be declared non-ocap by putting `#nocap;` at the very beginning of the file, before any declaration (non-ocap mode).


## Resources and graduality


In ocap mode, access to resources (devices and mutable state) is protected. Any value that captures a resource must declare it in its type: `val f: Foo^{r}`, where `r` is a region. Devices are os functionalities, while regions are marker for mutable state: every mutable object is declared with an associated region. Regions are the granularity level of runtime checks for mutability permissions: runtime-restricted environments (see the description of enclosure statements below) decides if an object can be modified by looking up its region.

Still in ocap mode only, resources and values that capture resources directly or transitively are called capabilities. All capabilities must have a capture set that mentions the capabilities they are allowed to capture. These capture sets can be more or less precise: if `f` has type `Foo^{fs}`, the canonical type of a structure `Bar` that captures `f` is `Bar^{f}` but may be widened to `Bar^{fs}` (which is a supertype of `Bar^{f}`). An extreme case is the one of capturing the root capability, simply denoted `Foo^` and meaning that the value can capture anything. These rules are the same as the ones of capture-tracking in Scala (at the time of writing this doc at least). See https://docs.scala-lang.org/scala3/reference/experimental/cc.html.

Non-ocap packages and modules have no capture set and are marked instead: `NonOcapModule^#`. Function invocations on marked receivers may only occur inside enclosures.

Graduality essentially comes from the existence of the non-ocap sublanguage and the possibility for ocap code to invoke functions written in the non-ocap sublanguage. See the enclosure statement for more details.


## Basic types

`Int`, `Bool`, `Char`, `Double`, `String` (conversions between some of them, and especially to `String` can be performed using the `as` keyword: `x as Double`)

Note that `String` is treated like a primitive type. In particular, strings are considered equal if and only if they are _structurally_ equal.

`Region`s are supported only in ocap mode.

`Void` can be used as the return type of functions that return without a result value.

`Nothing` can be used as the return type of functions that can not return (note that the compiler is conservative and in complex cases it may not be able to prove that a function indeed never returns).

Arrays are supported and have the following syntax: `arr <element type>`, e.g. `arr Int` or `arr arr String`. They are mutable and invariant. Arrays of primitive types other than `String` are initialized with 0s (or false for booleans). Other arrays must be initialized explicitly: loading from an uninitialized array cell results in a runtime error.


## Supported devices

Grattlesnake offers two devices: the filesystem (referred to as `fs`) and the console (referred to as `console`). See the [filesystem API](./rattlesnake-compiler/src/main/scala/lang/FileSystemApi.scala) and the [console API](./rattlesnake-compiler/src/main/scala/lang/ConsoleApi.scala) for the list of functions they give access to. They have to be imported explicitly in modules. In packages, merely using them imports them automatically and adds them to the capture set of the package.


## Declaring a type

### Modules
`module MyModule(x: Int, f: Foo, ...){ <functions> }`

In ocap mode, a module must also import the devices and packages it uses: `module MyModule(x: Int, f: Foo, package P, device fs)`
The `package` keyword becomes `#package` if the imported package is a non-ocap one.

Modules fields (also named parametric imports) have _internal_ visibility: they can only be accessed in functions invoked on the module instance they belong to. This instance is designated by the `me` keyword, which must prefix every occurrence of a field: `me.f` (this is to distinguish fields from locals with the same identifier).

### Packages
`package MyPackage { <functions> }`

### Structs and datatypes

Structs are instantiable unencapsulated data structures: `struct S { x: Int, f: Foo }`

Datatypes are "sealed abstract structs". They are declared like structs but using `datatype` instead of `struct`. They are not instantiable but structs that have the fields specified by the datatype can be subtype of datatypes that are declared omn the same file: `struct S : D { <fields> }`, where `D` is a datatype.

Structs and datatypes may be declared mutable and have reassignable fields: `mut struct S { var value: Double }`.

A mutable struct may subtype an immutable datatype. But in any case, a field that is reassignable in the supertype must be reassignable in the subtype as well.

Final (i.e. non reassignable) fields are covariant (they may have a more restrictive type in the subtype). Reassignable fields are invariant.

Datatypes may subtype other datatypes, following the same rules as subtyping between a struct and a datatype.


### Constants

Basic constants are supported: `const pi: Double = 3.142` The type annotation is optional. The right-hand side must be a literal of a primitive type.


### Declaring functions

Functions can be declared in the body of modules and packages: `fn foo(x: Int, ...) -> String`.

Two modifiers are supported (they must precede `fn`): `private`, which allows only functions in the current module or package to refer to the private function), and `main` to mark a function that is an entry point of the program. A main function must take a single argument of type `arr String` and return `Void`. Only packages can define a (single) main function.

`Void` return type may be omitted: `fn foo()` declares a `Void` function.

Arguments may be reassignable (`fn foo(var x: Int)`) or unnamed: `main fn run(arr String)`.


## Statements and expressions

### Type initializers

Arrays: `arr@r Int[length]`: creates an array of `length` integers. Literals like `[1, 2, 3]@r` can also be used. In both cases, `r` is the region associated with the array and `@r` should be omitted in non-ocap mode.

Structs: `new@r S(x, y, z)`: invokes the automatically-created constructor for struct `S`, that takes arguments for all fields in the order they have been declared. The region works similarly as for arrays.

Modules: like structs but without region, as they are (shallow) immutable. Package and device imports are implicit and and not added to the constructor (but their presence in the environment where the instantiation happens is checked).


### Declaring a local

`val x: Int = ...`

`val`s are final, `var`s are reassignable. The type annotation may be omitted when an initializer is provided.

`val`s and `var`s are allowed to be initialized later than their declaration, as long as the compiler can prove that they are initialized before being read and that `val`s are never assigned more than once:

```
val x: Int;
if cond {
    x = 0;
} else {
    x = 1;
};
console.print(x as String);     // OK, x has been initialized exactly once in all possible execution paths
```


### Unary operators

`-` (on integers and doubles), `!` (on booleans)

Length operator: `len` on arrays and strings


### Binary operators

`+`, `-`, `*`, `/`, `%` are supported on integers and doubles. They may be combined with an assignment: `x += y`.

Comparison operators `<`, `<=`, `>`, `>=`, are supported on integers and doubles. `==`, `!=` are supported on any type (structures and modules are checked for equality _by reference_).

`&&`, `||` are supported on booleans.


### Ternary operator

`when x then y else z`


### Function calls

Syntax: `receiver.methodName(arg1, arg2, ...)`

The receiver may be omitted if it is `me` (the current module or package).

Tails calls are eliminated if marked with a `!`: `receiver.methodName!(arg1, arg2, ...)`


### Indexing

Arrays and strings may be indexed to retrieve an element: `array[i]`.


### Casts and types tests

User-defined types may be cast: `x as Foo`

Type tests: `val b: Bool = x is Foo`



### Control structures

If: `if cond { ... } else { ... }`

The else branch is optional. `else if` clauses are supported.

`if` can be used for pattern matching on datatypes:

```
datatype Result
struct Success : Result { value: Int }
struct Failure : Result { errorMsg: String }
--------------------------------------------
fn printResult(res: Result) {
    val s: String;
    if res is Success {
        s = "succeeded with a result value of " + res.value as String;
    } else if res is Failure {
        s = "failed: " + res.errorMsg;
    };
    console.print(s + "\n");
}
```

For and while loops:

```
for var i = 0; i < len array; i += 1 {
    array[i] = i;
}
```
is equivalent to:
```
var i = 0;
while i < len array {
    array[i] = i;
    i += 1;
}
```

### Returning from a function

The `return` statement allows to return a value: `return x`. It may also be used without a return value to exit a void function.


### Panic

`panic msg` (where `msg` is a value of type string) crashes the program with the given message.


### Restricted blocks

`restricted {fs, r} { <body statements> }` statically asserts that no capability defined outside of the block except the ones explicitly allowed by the capture set (here `fs` and `r`) is accessed from inside it.


### Enclosures

Enclosures are the dynamic counterpart of `restricted`. They use the exact same syntax as restricted blocks (except that `restricted` is replaced by `enclosed`) and crash the program if code executed in their body tries to access a capability other than the ones mentioned in the capture set. Note that because of restrictions on runtime checks, only regions and devices may be included in the capture set given to an enclosure.

```
enclosed {fs} {
    console.print("Hello");     // runtime error
}
```

It is not allowed to use `return` inside an enclosure.


