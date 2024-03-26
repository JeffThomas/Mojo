# Mojo

Mojo is going to be a native TypeScrypt engine similar to `node`, written in Rust. 
It's NOT going to be backwards compatible with JavaScript and will NOT be 100% 
compatible with TypeScrypt as `node` uses it. Some key differences will be:

* No `any` type
* No `null` type
* No `|` in type definitions.
* Native `option` type
* Native `result` type
* No `var` declarations, only `let` or `const`

It is expected to be very fast.

It is based on the [Flywheel](https://github.com/JeffThomas/flywheel) prototype which 
contains a Pratt inspired Parser and the [Lexx](https://github.com/JeffThomas/lexx) 
a fast, extensible, greedy, single-pass text tokenizer.
