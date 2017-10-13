# Haskell compiler

This is a compiler for Haskell written in the [Rust programming language](https://www.rust-lang.org). This is no longer actively being worked on since I am currently working on other projects (mainly [gluon](https://github.com/gluon-lang/gluon). Though this should continue to compile on newer versions of Rustc it is possible that it may stop working as it is not actively maintained. Do let me know if that is the case though as I do still want to keep the project working.

As the project is right now it can handle quite large parts of Haskell though bugs have to be expected.

## "Implemented" features
* Typechecking
* Higher kinded types
* Algebraic data types
* newtypes
* Type classes
* Large parts of the Prelude
* `do` expressions
* Simple REPL

## Known unimplemented features

* Kind inference
* Arithmetic sequences
* List comprehensions
* Foreign Function Interface
* Most of the standard library
* deriving other than for `Eq` and `Ord`
* Type definitions
* and more!
