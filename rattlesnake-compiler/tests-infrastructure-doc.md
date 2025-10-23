# Tests system

**This documentation was written for a previous version of the compiler and might be out-of-date.**

## Analyzer tests

Analyzer tests (runner [here](./src/test/scala/compiler/AnalyzerTests.scala)) run a truncated compilation pipeline that does not include code generation. Their purpose is to make sure that the compiler detects and reports the expected errors on malformed programs.

To add a test, create a new program in the [analyzer tests directory](./src/test/res/analyzer-tests). This may be a single file or a directory containing a multi-files program. To specify which errors are expected, use the following system of formalized comments:

- The system recognizes as a formal comment any comment that starts with `//>`.
- On the line where an error is expected, a comment specifies the type of error (E for error or W for warning) as well as the expected error message. For instance:
    ```
    //> W : unused local: 'x' is never queried`
    ```

    Optionally, one may specify the column at which the error is expected, e.g.:
    ```
    //> E@col=41 : expected 'S', found 'I'
    ```
  
    If several errors are expected on the same line, they should be separated using `<//>`.

- By default, the system expects all errors reported by the compiler to correspond to expected errors. Allowing additional errors to be reported can be done inserting the following comment at the very beginning of the file:
    ```
    //> allow-more-errors
    ```

## Execution tests

Execution tests (runner [here](./src/test/scala/compiler/ExecutionTests.scala)) compile and run example programs and test their output (on the console as well as a potential crash).

To add a test, create a new directory in the [execution tests directory](./src/test/res/execution-tests). This directory should contain the following files:

- One or more `.rsn` source files, constituting the program.
- A file named `stdout.exp` and containing the _exact_ output expected on the console.
- Optionally, a file named `error-trace.exp` and containing the error message passed to the `panic` statement that terminated the program. In this case, one or more lines in source files have to be terminated by a formal comment like this (pay attention to the absence of space):
  ```
  //>STACKTRACE
  ```
  Lines annotated like this have to be part of the stacktrace of the exception thrown by `panic` to terminate the program. The test fails if the program exits normally.
