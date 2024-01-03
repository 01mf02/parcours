//! Parsers for [`slice`] input.

use crate::Parser;

pub fn first_filter<T, S, F: FnOnce(&T) -> bool>(f: F) -> FirstFilter<F> {
    FirstFilter(f)
}

pub struct FirstFilter<F>(F);

impl<'a, T, S, F: FnOnce(&T) -> bool> Parser<&'a [T], S> for FirstFilter<F> {
    type O = &'a T;

    fn parse(self, input: &'a [T], _state: &mut S) -> Option<(Self::O, &'a [T])> {
        input.split_first().filter(|(first, _rest)| self.0(first))
    }
}

pub fn first_filter_map<T, U, S, F: FnOnce(&T) -> U>(f: F) -> FirstFilterMap<F> {
    FirstFilterMap(f)
}

pub struct FirstFilterMap<F>(F);

impl<'a, T, U, S, F: FnOnce(&T) -> Option<U>> Parser<&'a [T], S> for FirstFilterMap<F> {
    type O = U;

    fn parse(self, input: &'a [T], _state: &mut S) -> Option<(Self::O, &'a [T])> {
        let (first, rest) = input.split_first()?;
        Some((self.0(first)?, rest))
    }
}
