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
