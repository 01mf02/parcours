//! Parsers for [`&str`] input.

use crate::{from_fn, Parser};

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
    from_fn(move |input: &'i str, _state: &mut S| input.strip_prefix(x).map(|rest| ((), rest)))
}
