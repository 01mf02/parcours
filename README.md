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
