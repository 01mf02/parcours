//! Parsers for [`&str`] input.

use crate::{from_fn, Combinator, Parser};

/// Collect longest prefix of a [`&str`] whose bytes satisfies the given condition.
pub fn take_while<'a, S, F: FnMut(&u8, &mut S) -> bool>(f: F) -> TakeWhile<F> {
    TakeWhile(f)
}

#[derive(Clone)]
pub struct TakeWhile<F>(F);

impl<'a, S, F: FnMut(&u8, &mut S) -> bool> Parser<&'a str, S> for TakeWhile<F> {
    type O = &'a str;

    fn parse(mut self, input: &'a str, state: &mut S) -> Option<(Self::O, &'a str)> {
        let len = input.bytes().take_while(|c| self.0(c, state)).count();
        Some((&input[..len], &input[len..]))
    }
}

type TakeWhile1<F> = crate::combinator::Filter<TakeWhile<F>, fn(&&str) -> bool>;

pub fn take_while1<'a, S, F: FnMut(&u8, &mut S) -> bool>(f: F) -> TakeWhile1<F> {
    take_while(f).filter(|n| !n.is_empty())
}

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

pub fn offset<'a>(large: &'a str, small: &'a str) -> Option<usize> {
    let large_ptr = large.as_ptr() as usize;
    let small_ptr = small.as_ptr() as usize;
    if small_ptr < large_ptr || small_ptr > large_ptr.wrapping_add(large.len()) {
        None
    } else {
        Some(small_ptr.wrapping_sub(large_ptr))
    }
}

pub fn with_str<'a, S, P: Parser<&'a str, S>>(
    p: P,
) -> impl Parser<&'a str, S, O = (P::O, &'a str)> {
    from_fn(|input, state| {
        let (y, rest) = p.parse(input, state)?;
        Some(((y, minus(input, rest)?), rest))
    })
}
