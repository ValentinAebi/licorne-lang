# The Licorne programming language 🦄

Licorne is an experimental programming language exploring refinement types and language-based support for lightweight verification.
It is primarily inspired from Kotlin and Scala.

The compiler is still only partially implemented. It supports parsing, IR generation, type inference, and type-checking. 
A backend to JVM bytecode is work in progress.

Some features that are already supported:
 - General refinement types: `Int with it % 2 == 0`
 - Dependent integer range types, treated as a restricted form of refinement types: `[0 ..< array.length()]`
 - Nullability aware types (non-nullability is partly treated as a refinement): `T?`
 - Function-wide bidirectional type inference (see for instance the `reverse` and `filter` methods in [the OOP lists example](./licorne-compiler/src/test/res/analyzer-tests/lists_oop_style.lic))
 - Smart casts (think of Kotlin's smart casts, but generalized to refinement types)
 - Automated type simplification
 - Constrained generics, with covariance and contravariance (like Kotlin or Scala): `Foo[TypeParam sub UpperBound]`
 - Union and intersection types (like Scala): `A | B`, `A & B`
 - Explicit method preconditions

## Code examples

The following code example gives a high-level idea of what Licorne is about 
(only to a limited extent, for instance it makes little use of Licorne's type inference capabilities). 

More code examples can be found in the [test resources directory](licorne-compiler/src/test/res/analyzer-tests).

```
package examples.books;

// counts are represented using a half-open interval that forbids negative numbers
typealias Cnt = [0..]

// page numbers of a book range from 1 to the number of pages in that book
typealias PageNumber(b: Book) = [1 .. b.pagesCnt()]

object Example {
    main fn example() {

        val book = new Book(title = "Modern Graph Theory",
                            pagesCnt = 394,
                            currPage = null);

        // Licorne detects that the given page (399) is greater than book.pagesCnt() (= 394).
        // Error message: first argument of call to openAtPage: expected PageNumber(book), found 399
        book.openAtPage(399);

        // This call is valid.
        book.openAtPage(104);
    }
}

class Book(
    public title: String,
    public pagesCnt: Cnt,
    var currPage: PageNumber(this)?
) {
    fn openAtPage(this, p: PageNumber(this)) {
        currPage = p
    }
}
```

## Build and run

To build the compiler, run `sbt clean assembly` in the [`licorne-compiler` directory](./licorne-compiler). The Licorne compiler can then be found as a jar file in the [`licorne-compiler/target/scala-<version>` directory](./licorne-compiler/target/scala-3.8.0).

To type-check a program using the (jar of the) compiler, run `java -jar licorne-compiler.jar compile src_file.lic` (or `java -jar licorne-compiler.jar compile src/*` to compile all files in `./src`).


## SMT solver integration

Licorne uses [Z3](https://github.com/z3prover/z3) via the [KSMT](https://github.com/UnitTestBot/ksmt) API. KSMT bundles Z3 into the compiler jar, so there is no need to install it separately.


## What's that name?

"Licorne" stands for "<b>L</b>ightweight <b>I</b>nferen<b>C</b>e <b>O</b>f <b>R</b>efi<b>NE</b>ments", and means "unicorn" in French. Earlier versions of Licorne were called Rattlesnake and [Grattlesnake](https://github.com/epfl-systemf/grattlesnake-lang), the former being a very simple toy language, and the latter corresponding to my master's thesis work on gradual object capabilities. They can be found as secondary branches of this repository.
