# Mojo

Mojo is going to be a scripting engine inspired by TypeScript, Rust, Go, Scala
any other bits of languages I like (not the languages, the bits. It will be
written in Rust. It's NOT going to be backwards compatible with JavaScript or
TypeScript. Some key differences will be:

* No `any` type
* No `null`, `nil` `undefined` or other lack of data type, use `Option<T>` instead
* No `|` in type definitions, you shouldn't need that
* Native `Option<T>` type
* Native `Either<Left<T>,Right<T>>` type
* Native `Result<Ok<T>,Err<E>>` type
    * with '^' error propagation (think Rusts '?' error propagator)
* No `var` declarations, only `let` or `const`
* No Try/Catch blocks
    * I know this is a big one, but I subscribe to the belief that Try/Catch all too often leads to bad coding
      practices (using it as flow control) and anti-patterns (catching everything and doing nothing, empty catch blocks
      enrage me).
    * Use `Result` and it's error propagator '^' instead
* A different kind of deconstructing
    * I like JavaScripts deconstructing assignments ok, but I think they're on the wrong side of the '=' sign. The thing
      being assigned to shouldn't have to know the shape of the thing being assigned.
    * Instead I'm planning a way you can deconstruct an object and use it wherever.
    * Let's put the deconstruction syntax on the other side of the '='
    * For example `let name, id = user{name, metadata.id}`
    * You can use this anywhere lists are accepted
        * For example given a function signature of `sayHi(name: string, id: number)`
        * `sayHi(user{name, metadata.id})`
            * Note that a static list like this is NOT an array. A static list can have mixed types, an array can not.
              You can make an array out of a static list, if they're all the same type.
            * This will NOT work `[user{name, id}]` but `[user{firstName, lastName}]` will
* Duck typing, as per Go, enforced at compile time
* Parallel processing, also Go style
* Continuous garbage collection
  * Garbage is collected unlike Rust, but unlike JavaScript or other garbage collecting systems it happens in real time not requiring the system to pause
  * I have a method of doing this I call Power Line, but it hasn't been proven yet.

It is expected to be very fast.

It is based on the [Flywheel](https://github.com/JeffThomas/flywheel) prototype which
contains a Pratt inspired Parser, and the [Lexx](https://github.com/JeffThomas/lexx)
a fast, extensible, greedy, single-pass text tokenizer.
