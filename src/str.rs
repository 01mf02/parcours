//! Parsers for [`&str`] input.

use crate::{from_fn, Combinator, Parser};

/// Collect longest prefix of a [`&str`] whose bytes satisfies the given condition.
///
/// # Implementation notes
///
/// The parser returned by this function does not implement [`Clone`],
/// because it is supposed to also accept functions that do not implement [`Clone`].
/// However, we could make this function return a parser that conditionally implements [`Clone`],
/// by making it return some struct `TakeWhile<F>` that implements [`Clone`] when `F` implements [`Clone`].
/// However, when I tried this approach, I had the problem that type inference broke down,
/// because `TakeWhile` does not contain any information about `S`.
/// To fix this, we can put `S` into a [`PhantomData`](core::marker::PhantomData) in `TakeWhile`,
/// but then, we have to implement [`Clone`] ourselves, because the automatic derivation of
/// [`Clone`] will impose that `S` has to implement [`Clone`], which is unnecessary.
/// In summary, it is probably not worth going through all this hassle just to get [`Clone`].
pub fn take_while0<'a, S>(mut f: impl FnMut(&u8) -> bool) -> impl Parser<&'a str, S, O = &'a str> {
    from_fn(move |input: &'a str, _state: &mut S| {
        let len = input.bytes().take_while(|c| f(c)).count();
        Some((&input[..len], &input[len..]))
    })
}

pub fn take_while1<'a, S>(f: impl FnMut(&u8) -> bool) -> impl Parser<&'a str, S, O = &'a str> {
    take_while0(f).filter(|n| !n.is_empty())
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
