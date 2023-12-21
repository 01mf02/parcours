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
