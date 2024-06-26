//! Parsers for [`&str`] input.

use crate::{from_fn, Combinator, Parser};

/// If the input is not empty, return its first character and advance input.
pub fn next<'a, S>() -> crate::Next<&'a str, S> {
    crate::Next(core::marker::PhantomData)
}

impl<'a, S> Parser<&'a str, S> for crate::Next<&'a str, S> {
    type O = char;

    fn parse(self, input: &'a str, _state: &mut S) -> Option<(Self::O, &'a str)> {
        let mut chars = input.chars();
        chars.next().map(|c| (c, chars.as_str()))
    }
}

/// Collect longest prefix of a [`&str`] whose bytes satisfy the given condition.
pub fn take_while<S, F: FnMut(&char, &mut S) -> bool>(f: F) -> TakeWhile<F> {
    TakeWhile(f)
}

/// A parser returned by [`take_while`].
#[derive(Copy, Clone)]
pub struct TakeWhile<F>(F);

impl<'a, S, F: FnMut(&char, &mut S) -> bool> Parser<&'a str, S> for TakeWhile<F> {
    type O = &'a str;

    fn parse(mut self, input: &'a str, state: &mut S) -> Option<(Self::O, &'a str)> {
        let len = input
            .char_indices()
            .find(|(_, c)| !self.0(c, state))
            .map_or_else(|| input.len(), |(len, _)| len);
        Some((&input[..len], &input[len..]))
    }
}

type TakeWhile1<F> = crate::combinator::Filter<TakeWhile<F>, fn(&&str) -> bool>;

/// Collect longest *non-empty* prefix of a [`&str`] whose bytes satisfy the given condition.
///
/// If the prefix is empty, this returns no output, unlike [`take_while`].
pub fn take_while1<S, F: FnMut(&char, &mut S) -> bool>(f: F) -> TakeWhile1<F> {
    take_while(f).filter(|n| !n.is_empty())
}

/// If the input starts with the given string, return `()` and remove the string from the input.
pub fn matches<'a, 'i: 'a, S>(x: &'a str) -> impl Parser<&'i str, S, O = ()> + Clone + 'a {
    from_fn(move |input: &str, _| Some(((), input.strip_prefix(x)?)))
}

/// Subtract one string slice from another.
///
/// Case 1 (reading from the left; most frequent):
///
/// ~~~ text
///        large
/// -------------------
///             small
///        ------------===
/// \-----/
///    | what we want
/// ~~~
///
/// Case 2 (reading from the right):
///
/// ~~~ text
///           large
///    -------------------
///      small
/// ===------------
///                \-----/
///                   | what we want
/// ~~~
///
/// Here, the parts indicated by `===` are anomalies that are not expected to occur,
/// but which are supported nonetheless by this function.
///
fn minus<'a>(large: &'a str, small: &'a str) -> Option<&'a str> {
    let small_start = small.as_ptr() as usize;
    let large_start = large.as_ptr() as usize;
    let small_end = small_start.wrapping_add(small.len());
    let large_end = large_start.wrapping_add(large.len());

    if small_start >= large_start && small_end >= large_end {
        Some(&large[..small_start.wrapping_sub(large_start)])
    } else if small_start <= large_start && small_end <= large_end {
        Some(&large[small_end.wrapping_sub(large_start)..])
    } else {
        None
    }
}

/// If the beginning of `inner` lies inside `outer`, return its offset.
///
/// Example:
///
/// ~~~
/// let outer = "Hello world!";
/// assert_eq!(parcours::str::offset(outer, &outer[6..]), Some(6));
/// // here, `inner` exceeds `outer`, but it's okay, because
/// // the start of `inner` still lies within `outer`
/// assert_eq!(parcours::str::offset(&outer[..7], &outer[6..]), Some(6));
/// assert_eq!(parcours::str::offset(outer, "something else"), None);
/// ~~~
pub fn offset<'a>(outer: &'a str, inner: &'a str) -> Option<usize> {
    let outer_ptr = outer.as_ptr() as usize;
    let inner_ptr = inner.as_ptr() as usize;
    if inner_ptr < outer_ptr || inner_ptr > outer_ptr.wrapping_add(outer.len()) {
        None
    } else {
        Some(inner_ptr.wrapping_sub(outer_ptr))
    }
}

/// Run the given parser and combine its output with the slice of the input string it consumed.
///
/// You can use this to find out via [`offset`] the span of the parsed element.
///
/// Example:
///
/// ~~~
/// # use parcours::str::{take_while, with_consumed};
/// # use parcours::{Parser, Combinator};
/// let digits = take_while(|c, _| c.is_ascii_digit());
/// let alphas = take_while(|c, _| c.is_ascii_alphabetic());
/// let parser = with_consumed(digits.then(alphas));
/// let input = "123abcäöü";
/// let result = ("123", "abc");
/// let consumed = "123abc";
/// let rest = "äöü";
/// assert_eq!(parser.parse(input, &mut ()), Some(((result, consumed), rest)));
///
/// ~~~
pub fn with_consumed<'a, S, P: Parser<&'a str, S>>(p: P) -> crate::WithConsumed<P> {
    crate::WithConsumed(p)
}

impl<'a, S, P: Parser<&'a str, S>> Parser<&'a str, S> for crate::WithConsumed<P> {
    type O = (P::O, &'a str);

    fn parse(self, input: &'a str, state: &mut S) -> Option<(Self::O, &'a str)> {
        let (y, rest) = self.0.parse(input, state)?;
        Some(((y, minus(input, rest)?), rest))
    }
}
