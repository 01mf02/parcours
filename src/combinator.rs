//! Create new parsers by combining existing ones.
//!
//! There are two flavours of combinators in parcours:
//!
//! * Combinators in the [`Combinator`] trait:
//!   These take a fixed number of parsers; for example,
//!   [`Combinator::opt`] takes one parser and
//!   [`Combinator::then`] takes two parsers.
//! * Combinators outside the [`Combinator`] trait: These either take
//!   functions that yield combinators ([`repeat`], [`separate_by`]) or
//!   n-tuples of combinators ([`any`], [`all`]).
//!
//! # Overview
//!
//! The following table gives an overview of the main combinators in parcours.
//! Here, `a` and `b` are two languages that are recognized by parsers of the same name.
//!
//! | Language             | Parser
//! | :------------------- | :----------------------
//! | `ab`                 | [`a.then(b)`](Combinator::then)
//! | `abc`                | [`a.then(b).then(c)`](Combinator::then) or [`all((a, b, c))`](all)
//! | <code>a\|b</code>    | [`a.or(b)`](Combinator::or)
//! | <code>a\|b\|c</code> | [`a.or(b).or(c)`](Combinator::or) or [`any((a, b, c))`](any)
//! | `a?`                 | [`a.opt()`](Combinator::opt)
//! | `a*`                 | [`a.repeated()`](Combinator::repeated) or [`repeat(a)`](repeat)
//! | `a+`                 | [`a.repeated()`](Combinator::repeated).[<code>filter(\|o\| !o.is_empty())</code>](Combinator::filter)
//! | `(a(ba)*)?`          | [`a.separated_by(b)`](Combinator::separated_by) or [`separate_by(a, b)`](separate_by)
//!
//! We also have a few combinators that operate on the output of a parser `a`.
//! These are defined as follows:
//!
//! Parser `p`                                  | `p.parse(i, s)`
//! :------------------------------------------ | :---------------------------------------------
//! [`a.map(f)`](Combinator::map)               | <code>a.parse(i, s).map(\|(y, rest)\| (f(y), rest))</code>
//! [`a.map_with(f)`](Combinator::map_with)     | <code>a.parse(i, s).map(\|(y, rest)\| (f(y, s), rest))</code>
//! [`a.filter(f)`](Combinator::filter)         | <code>a.parse(i, s).filter(\|(y, rest)\| f(y))</code>
//! [`a.filter_map(f)`](Combinator::filter_map) | <code>a.parse(i, s).and_then(\|(y, rest)\| Some((f(y)?, rest)))</code>
//! [`a.and_then(f)`](Combinator::and_then)     | <code>a.parse(i, s).and_then(\|(y, rest)\| f(y).parse(rest, s))</code>
//!
//! Last, but not least, we have a few combinators that throw away results.
//! For parsers `a`, `b`, and `c`, we have:
//!
//! Parser                                             | Definition
//! :------------------------------------------------- | :-------------------------------------------------
//! [`a.then_ignore(b)`](Combinator::then_ignore)      | <code>a.then(b).map(\|(a, _b)\| a)</code>
//! [`a.ignore_then(b)`](Combinator::ignore_then)      | <code>a.then(b).map(\|(_a, b)\| b)</code>
//! [`b.delimited_by(a, c)`](Combinator::delimited_by) | <code>all((a, b, c)).map(\|(_a, b, _c)\| b)</code>
use crate::Parser;

/// A combinator combines parsers to form new ones.
///
/// Every [`Parser`] implements the [`Combinator`] trait.
/// To use the [`Combinator`] trait, import it as follows:
///
/// ~~~
/// use parcours::Combinator;
/// ~~~
pub trait Combinator<I, S>: Parser<I, S>
where
    Self: Sized,
{
    /// If both parsers yield an output, return the pair of their outputs.
    ///
    /// The expression `p0.then(p1)` is equivalent to `all((p0, p1))`.
    /// However, `p0.then(p1).then(p2)` is equivalent to
    /// `all((all((p0, p1)), p2))` not
    /// `all((p0, p1, p2))`.
    /// That means that if you chain together more than two parsers with `then`,
    /// things might get a bit messy, because you get nested tuples.
    /// In that case, using [`all`] directly is preferable.
    fn then<P: Parser<I, S>>(self, other: P) -> All<(Self, P)> {
        All((self, other))
    }

    /// If the first parser succeeds, return its output, otherwise
    /// return the output of the second parser.
    ///
    /// The expression `p0.or(p1)/*...*/.or(pn)` is equivalent to
    /// `any((p0, p1,/*..., */pn))`.
    /// However, if more than two parsers are combined,
    /// [`any`] might yield better performance.
    fn or<P: Parser<I, S>>(self, other: P) -> Any<(Self, P)>
    where
        I: Clone,
    {
        Any((self, other))
    }

    /// Apply a function to the output of the parser.
    fn map<O, F: FnOnce(Self::O) -> O>(self, f: F) -> Map<Self, F> {
        Map(self, f)
    }

    /// Apply a function to the output of the parser as well as the mutable state.
    fn map_with<O, F: FnOnce(Self::O, &mut S) -> O>(self, f: F) -> MapWith<Self, F> {
        MapWith(self, f)
    }

    /// Succeed only if the given function yields `true` for the parser output.
    fn filter<F: FnOnce(&Self::O) -> bool>(self, f: F) -> Filter<Self, F> {
        Filter(self, f)
    }

    /// If the given function yields `Some(y)` for the parser output, succeed with `y`, else fail.
    fn filter_map<O, F: FnOnce(Self::O) -> Option<O>>(self, f: F) -> FilterMap<Self, F> {
        FilterMap(self, f)
    }

    /// Run two parsers in sequence and discard result of second one.
    fn then_ignore<P: Parser<I, S>>(self, other: P) -> ThenMap<Self, P, Self::O, P::O, Self::O> {
        self.then(other).map(|(l, _r): (Self::O, P::O)| l)
    }

    /// Run two parsers in sequence and discard result of first one.
    fn ignore_then<P: Parser<I, S>>(self, other: P) -> ThenMap<Self, P, Self::O, P::O, P::O> {
        self.then(other).map(|(_l, r): (Self::O, P::O)| r)
    }

    /// Run parsers `l`, `self`, and `r` in sequence and return only the output of `self`.
    fn delimited_by<L, R>(self, l: L, r: R) -> DelimitedBy<L, Self, R, L::O, Self::O, R::O>
    where
        L: Parser<I, S>,
        R: Parser<I, S>,
    {
        all((l, self, r)).map(|(_l, m, _r)| m)
    }

    /// Apply the given parser as often as possible.
    ///
    /// This collect the outputs of the parser into the type `O`.
    /// If you do not want to allocate, you can use `()` as `O`.
    fn repeated<O>(self) -> Repeated<Self, fn() -> O>
    where
        I: Clone,
        Self: Clone,
        O: Default + Extend<Self::O>,
    {
        Repeated(self, O::default)
    }

    /// Apply the given parser as often as possible, separated by `sep`.
    ///
    /// `a.separated_by(b)` corresponds to the regular expression `(a(ba)*)?`.
    /// The output of this parser is the collection of the outputs of `a`;
    /// that is, the outputs of `b` are discarded.
    /// Trailing `b`s are not consumed; for this, use
    /// `a.separated_by(b).then_ignore(b.opt())`.
    ///
    /// To keep the outputs of `b` and demand at least one match of `a`,
    /// you may use `a.then(b.then(a).repeated())` instead.
    fn separated_by<Sep, O>(self, sep: Sep) -> SeparatedBy<Self, Sep, fn() -> O>
    where
        I: Clone,
        Self: Clone,
        Sep: Parser<I, S> + Clone,
        O: Default + Extend<Self::O>,
    {
        SeparatedBy(self, sep, O::default)
    }

    /// If the given parser succeeds, wrap its output in `Some`, else return `None`.
    ///
    /// The resulting parser always succeeds.
    fn opt(self) -> Opt<Self>
    where
        I: Clone,
    {
        Opt(self)
    }

    /// Run the first parser, then create a second parser from its output and run it.
    fn and_then<P: Parser<I, S>, F: FnOnce(Self::O) -> P>(self, f: F) -> AndThen<Self, F> {
        AndThen(self, f)
    }
}

impl<I, S, T: Parser<I, S>> Combinator<I, S> for T {}

/// A parser returned by [`all`].
#[derive(Clone)]
pub struct All<T>(T);

/// Return outputs of all provided parsers, if all succeed.
///
/// This function takes a tuple of parsers,
/// which may all return different types of outputs.
///
/// ~~~
/// use parcours::{Parser, all, str::take_while1};
/// let digit = || take_while1(|c, _| c.is_ascii_digit());
/// let alpha = || take_while1(|c, _| c.is_ascii_alphabetic());
/// let parser = || all((digit(), alpha(), digit()));
/// let input = "123abc456 rest";
/// let output = ("123", "abc", "456");
/// assert_eq!(parser().parse(input, &mut ()), Some((output, " rest")));
/// assert_eq!(parser().parse("???", &mut ()), None);
/// ~~~
pub fn all<T>(t: T) -> All<T> {
    All(t)
}

/// A parser returned by [`any`].
#[derive(Clone)]
pub struct Any<T>(T);

/// Return output of the first provided parser that succeeds.
///
/// This function takes a tuple of parsers,
/// which all have to return the same type of output.
///
/// ~~~
/// use parcours::{Parser, any, str::take_while1};
/// let digit = || take_while1(|c, _| c.is_ascii_digit());
/// let alpha = || take_while1(|c, _| c.is_ascii_alphabetic());
/// let parser = || any((digit(), alpha()));
/// assert_eq!(parser().parse("123abc", &mut ()), Some(("123", "abc")));
/// assert_eq!(parser().parse("abc123", &mut ()), Some(("abc", "123")));
/// assert_eq!(parser().parse("???", &mut ()), None);
/// ~~~
pub fn any<T>(t: T) -> Any<T> {
    Any(t)
}

impl<I: Clone, S, O, P: Parser<I, S, O = O>, const N: usize> Parser<I, S> for Any<[P; N]> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let mut iter = IntoIterator::into_iter(self.0).rev();
        let last = iter.next()?;
        for p in iter.rev() {
            if let Some((y, rest)) = p.parse(input.clone(), state) {
                return Some((y, rest));
            }
        }
        last.parse(input, state)
    }
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
macro_rules! impl_all_any {
    ($($acc:ident)+; $head:ident $($tail:ident)*) => {
        impl_all_any!($($acc)+      ;          );
        impl_all_any!($($acc)+ $head; $($tail)*);
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
impl_all_any!(P1; P2 P3 P4 P5 P6 P7 P8 P9);

/// For a tuple `t` of pairs `(l, r)` and a parser `last`,
/// if there is a first `l` that returns a result `y`, then parse with `r(y)`,
/// otherwise parse with `last`.
///
/// We have the following equivalences:
/// * `decide(((l1, r1), ..., (ln, rn)), last)` is equivalent to
///   `decide(((l1, r1)), decide(((l2, r2), ..., (ln, rn)), last))`.
/// * `decide((), last)` is equivalent to `last`.
///
/// `decide(((l, r)), last).parse(input, state)` is defined as:
///
/// ~~~
/// # use parcours::Parser;
/// # fn f<I: Clone, S, P: Parser<I, S>>(input: I, state: &mut S, l: P, r: impl FnOnce(P::O) -> P, last: P) {
/// if let Some((y, rest)) = l.parse(input.clone(), state) {
///     core::mem::drop(input);
///     r(y).parse(rest, state)
/// } else {
///     last.parse(input, state)
/// }
/// # ;}
/// ~~~
pub fn decide<T, P>(t: T, last: P) -> Decide<T, P> {
    Decide(t, last)
}

/// A parser returned by [`decide`].
#[derive(Clone)]
pub struct Decide<T, Last>(T, Last);

macro_rules! impl_decide {
    ($($acc:ident)*; $lp:ident $rp:ident $rf:ident $($tail:ident)*) => {
        impl_decide!($($acc)*            ;          );
        impl_decide!($($acc)* $lp $rp $rf; $($tail)*);
    };
    ($($lp:ident $rp:ident $rf:ident)*;) => {
        #[allow(non_snake_case)]
        impl<I: Clone, S, $($lp, $rp, $rf),*, Last: Parser<I, S>> Parser<I, S> for Decide<($(($lp, $rf)),*,), Last>
        where
        $(
            $lp: Parser<I, S>,
            $rp: Parser<I, S, O = Last::O>,
            $rf: FnOnce($lp::O) -> $rp
        ),*,
        {
            type O = Last::O;

            #[inline(always)]
            fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
                let Self(($(($lp, $rf)),*,), last) = self;
                $(
                if let Some((y, rest)) = $lp.parse(input.clone(), state) {
                    core::mem::drop(input);
                    return $rf(y).parse(rest, state)
                })*
                return last.parse(input, state)
            }
        }
    }
}

impl_decide!(
    L1 R1 F1;
    L2 R2 F2
    L3 R3 F3
    L4 R4 F4
    L5 R5 F5
    L6 R6 F6
    L7 R7 F7
    L8 R8 F8
    L9 R9 F9
);

/// A parser returned by [`Combinator::map`].
#[derive(Clone)]
pub struct Map<P, F>(P, F);

impl<I, S, P: Parser<I, S>, O, F: FnOnce(P::O) -> O> Parser<I, S> for Map<P, F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let (p, f) = (self.0, self.1);
        p.parse(input, state).map(|(y, rest)| (f(y), rest))
    }
}

/// A parser returned by [`Combinator::map_with`].
#[derive(Clone)]
pub struct MapWith<P, F>(P, F);

impl<I, S, P: Parser<I, S>, O, F: FnOnce(P::O, &mut S) -> O> Parser<I, S> for MapWith<P, F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let (p, f) = (self.0, self.1);
        p.parse(input, state).map(|(y, rest)| (f(y, state), rest))
    }
}

/// A parser returned by [`Combinator::filter`].
#[derive(Clone)]
pub struct Filter<P, F>(P, F);

impl<I, S, P: Parser<I, S>, F: FnOnce(&P::O) -> bool> Parser<I, S> for Filter<P, F> {
    type O = P::O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let (p, f) = (self.0, self.1);
        p.parse(input, state).filter(|(y, _rest)| f(y))
    }
}

/// A parser returned by [`Combinator::filter_map`].
#[derive(Clone)]
pub struct FilterMap<P, F>(P, F);

impl<I, S, P: Parser<I, S>, O, F: FnOnce(P::O) -> Option<O>> Parser<I, S> for FilterMap<P, F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let (p, f) = (self.0, self.1);
        p.parse(input, state)
            .and_then(|(y, rest)| Some((f(y)?, rest)))
    }
}

type ThenMap<P1, P2, O1, O2, O> = Map<All<(P1, P2)>, fn((O1, O2)) -> O>;
type DelimitedBy<L, M, R, LO, MO, RO> = Map<All<(L, M, R)>, fn((LO, MO, RO)) -> MO>;

/// A parser returned by [`Combinator::opt`].
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

/// Apply a parser `p()` as often as possible.
///
/// This is a more general version of [`Combinator::repeated`],
/// which takes a single parser that must implement [`Clone`],
/// whereas this function takes a *function* that produces parsers
/// (which do not have to implement [`Clone`]).
///
/// Because the parser function is [`FnMut`],
/// it can yield *different* parsers on each repetition.
/// The following example shows a parser that matches
/// the sequence of numbers starting from 1:
///
/// ~~~
/// # use parcours::{Parser, from_fn, repeat};
/// let mut i = 0;
/// let p = repeat(|| {
///     i += 1;
///     from_fn(move |input: &str, _| Some(((), input.strip_prefix(&i.to_string())?)))
/// });
/// assert_eq!(p.parse("12345", &mut ()), Some(((), "")));
/// ~~~
pub fn repeat<I, S, P: Parser<I, S>, PF: FnMut() -> P, O>(p: PF) -> Repeat<PF, fn() -> O>
where
    O: Default + Extend<P::O>,
{
    Repeat(p, || O::default())
}

/// A parser returned by [`repeat`].
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

/// A parser returned by [`Combinator::repeated`].
#[derive(Clone)]
pub struct Repeated<P, O>(P, O);

impl<I: Clone, S, P: Parser<I, S> + Clone, O: Extend<P::O>, OF: FnOnce() -> O> Parser<I, S>
    for Repeated<P, OF>
{
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        let (p, o) = (self.0, self.1);
        Repeat(|| p.clone(), o).parse(input, state)
    }
}

/// Apply a parser `p()` as often as possible, separated by `sep()`.
///
/// This is a more general version of [`Combinator::separated_by`],
/// which operates on two parsers that must implement [`Clone`],
/// whereas this function takes two functions that yield parsers
/// (which do not necessarily implement [`Clone`]).
///
/// See [`repeat`] for an example how to exploit this.
pub fn separate_by<I, S, P: Parser<I, S>, Sep: Parser<I, S>, PF, SepF, O>(
    p: PF,
    sep: SepF,
) -> SeparateBy<PF, SepF, fn() -> O>
where
    PF: FnMut() -> P,
    SepF: FnMut() -> Sep,
    O: Default + Extend<P::O>,
{
    SeparateBy(p, sep, || O::default())
}

/// A parser returned by [`separate_by`].
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

/// A parser returned by [`Combinator::separated_by`].
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
        let (p, sep, o) = (self.0, self.1, self.2);
        SeparateBy(|| p.clone(), || sep.clone(), o).parse(input, state)
    }
}

/// A parser returned by [`Combinator::and_then`].
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
