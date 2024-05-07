//! Parsers for [`slice`] input.

use crate::Parser;

/// If the input is not empty, return its first element and advance input.
pub fn next<'a, T, S>() -> crate::Next<&'a [T], S> {
    crate::Next(core::marker::PhantomData)
}

impl<'a, T, S> Parser<&'a [T], S> for crate::Next<&'a [T], S> {
    type O = &'a T;

    fn parse(self, input: &'a [T], _state: &mut S) -> Option<(Self::O, &'a [T])> {
        input.split_first()
    }
}

/// Subtract one slice from another.
///
/// See the equivalent function in the [`crate::str`] module for more information.
fn minus<'a, T>(large: &'a [T], small: &'a [T]) -> Option<&'a [T]> {
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

/// Run the given parser and combine its output with the slice of the input it consumed.
pub fn with_consumed<I, S, P: Parser<I, S>>(p: P) -> crate::WithConsumed<P> {
    crate::WithConsumed(p)
}

impl<'a, T, S, P: Parser<&'a [T], S>> Parser<&'a [T], S> for crate::WithConsumed<P> {
    type O = (P::O, &'a [T]);

    fn parse(self, input: &'a [T], state: &mut S) -> Option<(Self::O, &'a [T])> {
        let (y, rest) = self.0.parse(input, state)?;
        Some(((y, minus(input, rest)?), rest))
    }
}
