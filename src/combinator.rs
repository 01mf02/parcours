use crate::Parser;

pub trait Combinator<I, S>: Parser<I, S>
where
    Self: Sized,
{
    fn then<P: Parser<I, S>>(self, other: P) -> All<(Self, P)> {
        All((self, other))
    }

    fn or<P: Parser<I, S>>(self, other: P) -> Any<(Self, P)> {
        Any((self, other))
    }

    fn map<O, F: FnOnce(Self::O) -> O>(self, f: F) -> Map<Self, F> {
        Map(self, f)
    }

    fn map_with<O, F: FnOnce(Self::O, &mut S) -> O>(self, f: F) -> MapWith<Self, F> {
        MapWith(self, f)
    }

    fn filter<F: FnOnce(&Self::O) -> bool>(self, f: F) -> Filter<Self, F> {
        Filter(self, f)
    }

    fn filter_map<O, F: FnOnce(Self::O) -> Option<O>>(self, f: F) -> FilterMap<Self, F> {
        FilterMap(self, f)
    }

    fn then_ignore<P: Parser<I, S>>(self, other: P) -> ThenMap<Self, P, Self::O, P::O, Self::O> {
        self.then(other).map(|(l, _r): (Self::O, P::O)| l)
    }

    fn ignore_then<P: Parser<I, S>>(self, other: P) -> ThenMap<Self, P, Self::O, P::O, P::O> {
        self.then(other).map(|(_l, r): (Self::O, P::O)| r)
    }

    fn delimited_by<L: Parser<I, S>, R: Parser<I, S>>(
        self,
        l: L,
        r: R,
    ) -> DelimitedBy<L, Self, R, L::O, Self::O, R::O> {
        all((l, self, r)).map(|(_l, m, _r)| m)
    }

    fn repeated<O>(self) -> Repeated<Self, fn() -> O>
    where
        Self: Clone,
        O: Default + Extend<Self::O>,
    {
        Repeated(self, O::default)
    }

    fn separated_by<Sep, O>(self, sep: Sep) -> SeparatedBy<Self, Sep, fn() -> O>
    where
        Self: Clone,
        Sep: Parser<I, S> + Clone,
        O: Default + Extend<Self::O>,
    {
        SeparatedBy(self, sep, O::default)
    }

    fn opt(self) -> Opt<Self> {
        Opt(self)
    }

    fn and_then<P: Parser<I, S>, F: FnOnce(Self::O) -> P>(self, f: F) -> AndThen<Self, F> {
        AndThen(self, f)
    }
}

impl<I, S, T: Parser<I, S>> Combinator<I, S> for T {}

#[derive(Clone)]
pub struct All<T>(T);

/// If all provided parsers succeed, return all of their outputs.
///
/// This function takes a tuple of parsers,
/// which may all return different types of outputs.
///
/// ~~~
/// use parcours::{Parser, all, str::take_while1};
/// let digit = || take_while1(|c| c.is_ascii_digit());
/// let alpha = || take_while1(|c| c.is_ascii_alphabetic());
/// let parser = || all((digit(), alpha(), digit()));
/// let input = "123abc456 rest";
/// let output = ("123", "abc", "456");
/// assert_eq!(parser().parse(input, &mut ()), Some((output, " rest")));
/// assert_eq!(parser().parse("???", &mut ()), None);
/// ~~~
pub fn all<T>(t: T) -> All<T> {
    All(t)
}

#[derive(Clone)]
pub struct Any<T>(T);

/// Return output of the first provided parser that succeeds.
///
/// This function takes a tuple of parsers,
/// which all have to return the same type of output.
///
/// ~~~
/// use parcours::{Parser, any, str::take_while1};
/// let digit = || take_while1(|c| c.is_ascii_digit());
/// let alpha = || take_while1(|c| c.is_ascii_alphabetic());
/// let parser = || any((digit(), alpha()));
/// assert_eq!(parser().parse("123abc", &mut ()), Some(("123", "abc")));
/// assert_eq!(parser().parse("abc123", &mut ()), Some(("abc", "123")));
/// assert_eq!(parser().parse("???", &mut ()), None);
/// ~~~
pub fn any<T>(t: T) -> Any<T> {
    Any(t)
}

/// Generate parsing code for `Any<(P0, P1, ..., Pn)>`.
///
/// `impl_any!(input, state, p0 p1 ... pn)` generates the following code:
///
/// ~~~
/// # use parcours::Parser;
/// # fn f<I: Clone, S, O, P: Parser<I, S, O = O>>(input: I, state: &mut S, p0: P, p1: P, pn: P) -> Option<(O, I)> {
/// if let Some(y) = p0.parse(input.clone(), state) {
///     return Some(y)
/// }
/// if let Some(y) = p1.parse(input.clone(), state) {
///     return Some(y)
/// }
/// // ...
/// return pn.parse(input, state)
/// # }
/// ~~~
///
/// The idea behind it is that the input has to be cloned for all but the last parser,
/// which is able to consume the input.
macro_rules! impl_any {
    ($input:ident, $state:ident, $head:ident $($tail:ident)+) => {
        if let Some(y) = $head.parse($input.clone(), $state) {
            return Some(y)
        }
        impl_any!($input, $state, $($tail)+)
    };
    ($input:ident, $state:ident, $head:ident) => {
        return $head.parse($input, $state)
    }
}

/// Generate `impl`s for `Any<(P0, P1, ..., Pn)>` and `All<(P0, P1, ..., Pn)>`.
///
/// This is inspired by winnow's
/// [`impl_parser_for_tuples`](https://github.com/winnow-rs/winnow/blob/02561943e396aab9fc268ec00c88273e3315ef0a/src/parser.rs#L943).
macro_rules! impl_for_tuples {
    ($($acc:ident)+; $head:ident $($tail:ident)*) => {
        impl_for_tuples!($($acc)+      ;          );
        impl_for_tuples!($($acc)+ $head; $($tail)*);
    };
    ($($parser:ident)+;) => {
        #[allow(non_snake_case)]
        impl<I, S, $($parser: Parser<I, S>),+> Parser<I, S> for All<($($parser),+,)> {
            type O = ($($parser::O),+,);

            #[inline(always)]
            fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
                let Self(($($parser),+,)) = self;
                $(let ($parser, input) = $parser.parse(input, state)?;)+
                Some((($($parser),+,), input))
            }
        }

        #[allow(non_snake_case)]
        impl<I: Clone, S, O, $($parser: Parser<I, S, O = O>),+> Parser<I, S> for Any<($($parser),+,)> {
            type O = O;

            #[inline(always)]
            fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
                let Self(($($parser),+,)) = self;
                impl_any!(input, state, $($parser)*);
            }
        }
    }
}
impl_for_tuples!(P1; P2 P3 P4 P5 P6 P7 P8 P9);

#[derive(Clone)]
pub struct Map<P, F>(P, F);

impl<I, S, P: Parser<I, S>, O, F: FnOnce(P::O) -> O> Parser<I, S> for Map<P, F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0
            .parse(input, state)
            .map(|(y, rest)| (self.1(y), rest))
    }
}

#[derive(Clone)]
pub struct MapWith<P, F>(P, F);

impl<I, S, P: Parser<I, S>, O, F: FnOnce(P::O, &mut S) -> O> Parser<I, S> for MapWith<P, F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0
            .parse(input, state)
            .map(|(y, rest)| (self.1(y, state), rest))
    }
}

#[derive(Clone)]
pub struct Filter<P, F>(P, F);

impl<I, S, P: Parser<I, S>, F: FnOnce(&P::O) -> bool> Parser<I, S> for Filter<P, F> {
    type O = P::O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0.parse(input, state).filter(|(y, _rest)| self.1(y))
    }
}

#[derive(Clone)]
pub struct FilterMap<P, F>(P, F);

impl<I, S, P: Parser<I, S>, O, F: FnOnce(P::O) -> Option<O>> Parser<I, S> for FilterMap<P, F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0
            .parse(input, state)
            .and_then(|(y, rest)| self.1(y).map(|y| (y, rest)))
    }
}

type ThenMap<P1, P2, O1, O2, O> = Map<All<(P1, P2)>, fn((O1, O2)) -> O>;
type DelimitedBy<L, M, R, LO, MO, RO> = Map<All<(L, M, R)>, fn((LO, MO, RO)) -> MO>;

#[derive(Clone)]
pub struct Opt<P>(P);

impl<I: Clone, S, P: Parser<I, S>> Parser<I, S> for Opt<P> {
    type O = Option<P::O>;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        Some(match self.0.parse(input.clone(), state) {
            Some((y, rest)) => (Some(y), rest),
            None => (None, input),
        })
    }
}

pub fn repeat<P, O: Default>(p: P) -> Repeat<P, fn() -> O> {
    Repeat(p, || O::default())
}

#[derive(Clone)]
pub struct Repeat<P, O>(P, O);

impl<I: Clone, S, P: Parser<I, S>, O: Extend<P::O>, PF: FnMut() -> P, OF: FnOnce() -> O>
    Parser<I, S> for Repeat<PF, OF>
{
    type O = O;

    fn parse(mut self, mut input: I, state: &mut S) -> Option<(Self::O, I)> {
        let mut out = self.1();
        while let Some((y, rest)) = self.0().parse(input.clone(), state) {
            out.extend(core::iter::once(y));
            input = rest;
        }
        Some((out, input))
    }
}

#[derive(Clone)]
pub struct Repeated<P, O>(P, O);

impl<I: Clone, S, P: Parser<I, S> + Clone, O: Extend<P::O>, OF: FnOnce() -> O> Parser<I, S>
    for Repeated<P, OF>
{
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        Repeat(|| self.0.clone(), self.1).parse(input, state)
    }
}

pub fn separate_by<P, Sep, O: Default>(p: P, sep: Sep) -> SeparateBy<P, Sep, fn() -> O> {
    SeparateBy(p, sep, || O::default())
}

#[derive(Clone)]
pub struct SeparateBy<P, Sep, O>(P, Sep, O);

impl<I: Clone, S, P: Parser<I, S>, Sep: Parser<I, S>, O: Extend<P::O>, PF, SepF, OF> Parser<I, S>
    for SeparateBy<PF, SepF, OF>
where
    PF: FnMut() -> P,
    SepF: FnMut() -> Sep,
    OF: FnOnce() -> O,
{
    type O = O;

    fn parse(self, mut input: I, state: &mut S) -> Option<(Self::O, I)> {
        let Self(mut p, mut sep, init) = self;
        let mut out = init();
        if let Some((head, rest)) = p().parse(input.clone(), state) {
            out.extend(core::iter::once(head));
            input = rest;
        } else {
            return Some((out, input));
        }

        while let Some((_, rest)) = sep().parse(input.clone(), state) {
            if let Some((y, rest)) = p().parse(rest, state) {
                out.extend(core::iter::once(y));
                input = rest;
            } else {
                break;
            }
        }
        Some((out, input))
    }
}

#[derive(Clone)]
pub struct SeparatedBy<P, Sep, O>(P, Sep, O);

impl<I: Clone, S, P, Sep, O: Extend<P::O>, OF> Parser<I, S> for SeparatedBy<P, Sep, OF>
where
    P: Parser<I, S> + Clone,
    Sep: Parser<I, S> + Clone,
    OF: FnOnce() -> O,
{
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        SeparateBy(|| self.0.clone(), || self.1.clone(), self.2).parse(input, state)
    }
}

#[derive(Clone)]
pub struct AndThen<P, F>(P, F);

impl<I, S, P1: Parser<I, S>, P2: Parser<I, S>, F: FnOnce(P1::O) -> P2> Parser<I, S>
    for AndThen<P1, F>
{
    type O = P2::O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let (y, rest) = self.0.parse(input, state)?;
        self.1(y).parse(rest, state)
    }
}
