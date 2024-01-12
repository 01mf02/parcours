//! Parsers for [`slice`] input.

use crate::Parser;

/// If the first element of the input satisfies the given condition, return it and advance input.
pub fn first_filter<T, S, F: FnOnce(&T, &mut S) -> bool>(f: F) -> FirstFilter<F> {
    FirstFilter(f)
}

/// A parser returned by [`first_filter`].
#[derive(Clone)]
pub struct FirstFilter<F>(F);

impl<'a, T, S, F: FnOnce(&T, &mut S) -> bool> Parser<&'a [T], S> for FirstFilter<F> {
    type O = &'a T;

    fn parse(self, input: &'a [T], state: &mut S) -> Option<(Self::O, &'a [T])> {
        input
            .split_first()
            .filter(|(first, _rest)| self.0(first, state))
    }
}

/// If the given function returns `Some(y)` for the first element of the input, return `y` and advance input.
pub fn first_filter_map<T, U, S, F: FnOnce(&T, &mut S) -> U>(f: F) -> FirstFilterMap<F> {
    FirstFilterMap(f)
}

/// A parser returned by [`first_filter_map`].
#[derive(Clone)]
pub struct FirstFilterMap<F>(F);

impl<'a, T, U, S, F: FnOnce(&T, &mut S) -> Option<U>> Parser<&'a [T], S> for FirstFilterMap<F> {
    type O = U;

    fn parse(self, input: &'a [T], state: &mut S) -> Option<(Self::O, &'a [T])> {
        input
            .split_first()
            .and_then(|(first, rest)| Some((self.0(first, state)?, rest)))
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
pub fn with_consumed<'a, T: 'a, S, P: Parser<&'a [T], S>>(p: P) -> WithConsumed<P> {
    WithConsumed(p)
}

/// A parser returned by [`with_consumed`].
#[derive(Clone)]
pub struct WithConsumed<P>(P);

impl<'a, T, S, P: Parser<&'a [T], S>> Parser<&'a [T], S> for WithConsumed<P> {
    type O = (P::O, &'a [T]);

    fn parse(self, input: &'a [T], state: &mut S) -> Option<(Self::O, &'a [T])> {
        let (y, rest) = self.0.parse(input, state)?;
        Some(((y, minus(input, rest)?), rest))
    }
}
