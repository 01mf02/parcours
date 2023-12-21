/// A parser takes input and mutable state, and maybe yields an output and remaining input.
///
/// # History
///
/// This trait, and especially its function [`Parser::parse`] shapes everything that goes on in this crate.
/// It is inspired to a great extent by a rhyme:
///
/// > *A Parser for Things  
/// > is a function from Strings  
/// > to Lists of Pairs  
/// > of Things and Strings!*  
/// > (Fritz Ruehr, ["Dr. Seuss on Parser Monads"](https://willamette.edu/~fruehr/haskell/seuss.html))
///
/// Ruehr uses the following type signature for parsers in Haskell:
///
/// ~~~ haskell
/// type Parser a = String -> [(a, String)]
/// ~~~
///
/// The function signature in this crate diverges from that in several aspects:
///
/// * It generalises the type of input to be `I`,
///   whereas it is always `String` in the Haskell case.
/// * It takes some mutable reference to a state `S`,
///   which is passed to every sub-parser and can be very useful,
///   for example to keep track of errors.
/// * The largest change, however, is the output type, which is
///   an `Option` instead of a list in Haskell.
///
/// The last change deserves some justification.
/// I tried for some time to recreate Ruehr's approach,
/// using `Iterator` as output type,
/// because this most closely resembles Haskell's lazy lists.
/// (The codename for this experiment was "parasite", standing for
/// "parsers as iterators".)
/// I imagined the ideal type signature to resemble this:
///
/// ~~~
/// trait Parser<I> {
///     type O;
///     fn parse(&self, x: I) -> Box<dyn Iterator<Item = (Self::O, I)>>;
/// }
/// ~~~
///
/// However, as I pursued with this approach,
/// I found myself quickly in lifetime and typing hell.
/// Everything was so hard that I stepped back and asked myself:
///
/// > *Is this too much Voodoo?*  
/// > (Terry Davis, ["Hardest Question in Programming"](https://www.youtube.com/watch?v=EAeYn1xWqm8))
///
/// I then thought that for my purposes,
/// I could actually do with a single output (instead of arbitrarily many),
/// thus eliminating lifetime hell that stems from returning a `dyn Iterator`.
/// And thus `parcours` was born.
///
/// ## The Importance of Being Your`self`
///
/// You might ask why [`Parser::parse`] takes `self` instead of `&self`.
/// After all, the former consumes a parser when calling it, whereas
/// the latter allows calling a parser multiple times.
///
/// To answer your question, curious reader,
/// let us suppose that the [`Parser`] trait was defined as follows:
///
/// ~~~
/// pub trait Parser<I, S = ()> {
///     type O;
///     fn parse(&self, input: I, state: &mut S) -> Option<(Self::O, I)>;
/// }
/// ~~~
///
/// This is basically the same as what we have in parcours, only that
/// `parse` takes `&self`, not `self`.
///
/// The problem with this approach is that it effectively
/// **prohibits the construction of parsers that take [`FnOnce`] closures**.
/// That is because we cannot call an [`FnOnce`] if we have a reference to it:
///
/// ~~~ compile_fail
/// fn call_fn_once(f: &impl FnOnce()) {
///     f()
/// }
/// ~~~
///
/// And that means that if we have only a *reference* to a parser,
/// the parser cannot call any [`FnOnce`] closure that it might possess.
/// Which is logical, if you consider that a function taking `&self`
/// can be called arbitrarily often on some object,
/// yet [`FnOnce`] means that it can be called, well, only once.
/// This clashes.
///
/// So what's the big deal about [`FnOnce`]? Can't we just use [`Fn`] and take `&self`?
/// Yes, we can. That's actually the first thing I tried.
/// But this has a double negative impact on performance.
/// First, while it allows us to take a `Box<dyn Parser>` and call `parse` on it,
/// I found in benchmarks that just putting a single `Box` around a (heavily used) parser
/// increased runtime by about 10%.
/// So just being able to box a parser might tempt people to do it,
/// without realising the negative impact on performance.
/// Furthermore, when we use [`Fn`], we tend to have to move and clone more data.
/// Consider the following example, which is a very inefficient implementation of
/// [`core::iter::once`]:
///
/// ~~~ compile_fail
/// pub fn stupid_once<T>(x: T) -> impl Iterator<Item = T> {
///     core::iter::once(0).map(|_| x)
/// }
/// ~~~
///
/// Here, the compiler errors lead us quickly to the following solution:
///
/// ~~~
/// pub fn stupid_once<T: Clone>(x: T) -> impl Iterator<Item = T> {
///     core::iter::once(0).map(move |_| x.clone())
/// }
/// ~~~
///
/// This means that we *have* to clone `x` here,
/// even if we know that it will be returned just once.
/// That is because [`Iterator::map`] does not accept [`FnOnce`].
/// This pattern showed up a lot when using
/// the alternative `Parser` trait where `parse()` takes `&self`.
/// Aside from looking verbose, it is bad for performance.
///
/// On the other hand, take the following implementation:
///
/// ~~~
/// pub fn nice_once<T>(x: T) -> Option<T> {
///     Some(0).map(|_| x)
/// }
/// ~~~
///
/// Here, because [`Option::map`] takes [`FnOnce`], we neither have to move nor clone `x`.
///
/// All this means that once there was the decision for [`Parser::parse`] to return [`Option`],
/// there was a clear incentive to take `self` in [`Parser::parse`] in order to allow for [`FnOnce`].
pub trait Parser<I, S = ()>
where
    Self: Sized,
{
    type O;

    /// Parse a value of type [`Self::O`].
    ///
    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)>;

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

#[derive(Clone)]
pub struct All<T>(T);

pub fn all<T>(t: T) -> All<T> {
    All(t)
}

#[derive(Clone)]
pub struct Any<T>(T);

pub fn any<T>(t: T) -> Any<T> {
    Any(t)
}

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
                $(if let Some(y) = $parser.parse(input.clone(), state) {
                    return Some(y)
                })+
                None
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

pub fn from_fn<I, S, O, F: FnOnce(I, &mut S) -> Option<(O, I)>>(f: F) -> FromFn<F> {
    FromFn(f)
}

#[derive(Clone)]
pub struct FromFn<F>(F);

impl<I, S, O, F: FnOnce(I, &mut S) -> Option<(O, I)>> Parser<I, S> for FromFn<F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0(input, state)
    }
}
