![Build status](https://github.com/01mf02/parcours/actions/workflows/rust.yml/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/parcours.svg)](https://crates.io/crates/parcours)
[![Documentation](https://docs.rs/parcours/badge.svg)](https://docs.rs/parcours)
[![Rust 1.53+](https://img.shields.io/badge/rust-1.53+-orange.svg)](https://www.rust-lang.org)

# Parser Combinators for Unique Results

parcours is a minimalistic crate to help with the creation of parsers and lexers.
It provides a set of **par**ser **co**mbinators for parsers that return
**u**nique **r**e**s**ults; that is, at most one output.

The name "parcours" is inspired from the sport [Parkour],
in which practitioners attempt to
"get from point A to point B in the fastest and most efficient way possible,
without assisting equipment".

In the same sense, parcours provides only very basic building blocks for parsers,
but these building blocks are very generic and incur very small overhead,
so you can do nearly everything with them.

[Parkour]: https://en.wikipedia.org/wiki/Parkour

## Features

* `no_std` and no dependency on `alloc` → suitable for constrained (embedded) environments
* no other dependencies
* zero-copy parsing
* fast build times: ~600ms for a JSON parser with `--release`
* high performance
* works on any kind of input (helpers for `&str` and `&[T]` are provided)
* precedence climbing

## Related Work

I discovered the [lip] crate only once I was already on a good way into writing parcours.
It is spiritually the closest to parcours in the Rust ecosystem that I found so far.
Apart from it, there are many parser combinator crates.
I have personally implemented quite complex parsers using [nom] and [chumsky],
which both provide nice machinery for common use cases, but
I always struggled once I wanted to do something that was not intended by these crates.
In contrast, parcours provides much less machinery,
and it is my hope that this makes it also more flexible.

[lip]: https://crates.io/crates/lip
[nom]: https://crates.io/crates/nom
[chumsky]: https://crates.io/crates/chumsky
