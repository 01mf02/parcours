//! Parsers for [`slice`] input.

use crate::{from_fn, Parser};

pub fn first_filter<'a, T, S>(f: impl FnOnce(&T) -> bool) -> impl Parser<&'a [T], S, O = &'a T> {
    from_fn(|input: &'a [T], state| input.split_first().filter(|(first, rest)| f(first)))
}

pub fn first_filter_map<'a, T, U, S>(
    f: impl FnOnce(&T) -> Option<U>,
) -> impl Parser<&'a [T], S, O = U> {
    from_fn(|input: &[T], state| {
        input
            .split_first()
            .and_then(|(first, rest)| Some((f(first)?, rest)))
    })
}
