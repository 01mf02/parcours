//! Parser Combinators for Unique Results.
//!
//! This crate provides building blocks to create parsers (and lexers) that return at most one output.
//!
//! # Quickstart
//!
//! The following shows a CSV line parser realised in parcours:
//!
//! ~~~
//! use parcours::{Parser, Combinator};
//!
//! // CSV line parser               👇 input 👇 state
//! fn csv_line<'a>() -> impl Parser<&'a str, (), O = Vec<&'a str>> {
//!     use parcours::str::{matches, take_while};
//!     take_while(|c, _| *c != ',').separated_by(matches(","))
//! }
//!
//! assert_eq!(
//!     //               👇 input                👇 state
//!     csv_line().parse("apples,oranges,pears", &mut ()),
//!     //    👇 output                           👇 remaining input
//!     Some((vec!["apples", "oranges", "pears"], ""))
//! );
//! ~~~
//!
//! # Examples
//!
//! parcours provides a few examples that are each designed to teach a few concepts:
//!
//! * [JSON](../../../examples/json.rs): zero-copy string parsing, combinators
//! * [Lambda calculus](../../../examples/lambda.rs): error handling & mutable state
//! * [bc](../../../examples/bc.rs): separate lexer/parser, precedence climbing
//!
//! # Topics
//!
//! ## Error Recovery
//!
//! My opinion on error recovery has been shaped by the lecture of
//! [Don't Panic! Better, Fewer, Syntax Errors for LR Parsers](https://arxiv.org/pdf/1804.07133.pdf)
//! by Lukas Diekmann and Laurence Tratt, who write in their introduction:
//!
//! > When error recovery works well, it is a useful productivity gain.
//! > Unfortunately, most current error recovery approaches are simplistic.
//! > The most common grammar-neutral approach to error recovery are those algorithms described as
//! > "panic mode" [...] which skip input until the parser finds something it is able to parse.
//! > A more grammar-speciﬁc variation of this idea is to skip input until a
//! > pre-determined synchronisation token (e.g. ';' in Java) is reached [...],
//! > or to try inserting a single synchronisation token.
//! > Such strategies are often unsuccessful, leading to a cascade of spurious syntax errors [...].
//! > Programmers quickly learn that only the location of the first error in a file --- not
//! > the reported repair, nor the location of subsequent errors --- can be relied upon to be accurate.
//!
//! Their proposed solution is for LR parsers, which parcours cannot adapt.
//! Therefore, instead of adopting a "simplistic" error recovery approach,
//! I leave all control about error recovery to the user of the parcours.
//! While parcours can be used to emit multiple error messages due to its mutable state,
//! I have found it most useful to emit only the first syntax error message, as
//! I find myself only looking at the first syntax error anyway (as observed in the citation).
//! If you want support for multiple parse errors that are automatically derived and good,
//! you may consider using the [grmtools](https://github.com/softdevteam/grmtools) suite of the authors.
#![no_std]
#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod combinator;
pub mod prec_climb;
pub mod slice;
pub mod str;

#[doc(inline)]
pub use combinator::{all, any, repeat, separate_by, Combinator};

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
///
/// **TL;DR**: When our input `I` is a string and we do not use mutable state `S`, we have:
///
/// > *A Parser for a Thing  
/// > is a function from a String  
/// > to an optional Pair of  
/// > a Thing and a String!*
pub trait Parser<I, S = ()> {
    /// Output of the parser.
    type O;

    /// Parse a value of type [`Self::O`].
    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)>;
}

/// Construct a parser from a function.
///
/// This is similar to [`core::iter::from_fn`].
/// It can be used to write a custom parser without having to write a lot of code.
/// For example, consider the following parser `value(o)` that simply returns
/// `o` without consuming any input:
///
/// ~~~
/// # use parcours::Parser;
/// fn value<O>(o: O) -> Value<O> {
///     Value(o)
/// }
///
/// struct Value<O>(O);
///
/// impl<I, S, O> Parser<I, S> for Value<O> {
///     type O = O;
///
///     fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
///         Some((self.0, input))
///     }
/// }
/// ~~~
///
/// `value` can be written more concisely as:
///
/// ~~~
/// # use parcours::{Parser, from_fn};
/// fn value<I, S, O>(o: O) -> impl Parser<I, S, O = O> {
///     from_fn(|input, _state| Some((o, input)))
/// }
/// ~~~
pub fn from_fn<I, S, O, F: FnOnce(I, &mut S) -> Option<(O, I)>>(f: F) -> FromFn<F> {
    FromFn(f)
}

/// A parser returned by [`from_fn`].
#[derive(Copy, Clone)]
pub struct FromFn<F>(F);

impl<I, S, O, F: FnOnce(I, &mut S) -> Option<(O, I)>> Parser<I, S> for FromFn<F> {
    type O = O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0(input, state)
    }
}

/// Lazily construct a parser from a function.
///
/// # Use cases
///
/// ## Construct recursive parsers
///
/// This allows you to create recursive parsers, like so:
///
/// ~~~
/// # use parcours::{Parser, lazy};
/// fn rec<I, S>() -> impl Parser<I, S, O = ()> {
///     lazy!(rec)
/// }
/// ~~~
///
/// This is equivalent to writing:
///
/// ~~~
/// # use parcours::{Parser, from_fn};
/// fn rec<I, S>() -> impl Parser<I, S, O = ()> {
///     from_fn(|input, state| rec().parse(input, state))
/// }
///
/// ~~~
///
/// You can also create recursive parsers from functions that take arguments:
///
/// ~~~
/// # use parcours::{Parser, Combinator, lazy};
/// fn rec<I: Clone, S, T: Clone>(x: T) -> impl Parser<I, S, O = ()> {
///     let x1 = x.clone();
///     lazy!(|| rec(x1)).or(lazy!(|| rec(x)))
/// }
/// ~~~
///
/// ## Reduce build times by type erasure
///
/// Like in `chumsky`, we can sometimes get very large parser types, even without recursion.
/// Such large parser types can significantly increase build times.
/// Consider the following example:
///
/// ~~~
/// # use parcours::{Parser, Combinator, lazy};
/// fn exp_type<I: Clone, S, P: Parser<I, S> + Clone>(p0: P) -> impl Parser<I, S, O = P::O> {
///     let p1 = p0.clone().or(p0);
///     let p2 = p1.clone().or(p1);
///     let p3 = p2.clone().or(p2);
///     let p4 = p3.clone().or(p3);
///     let p5 = p4.clone().or(p4);
///     let p6 = p5.clone().or(p5);
///     let p7 = p6.clone().or(p6);
///     let p8 = p7.clone().or(p7);
///     let p8 = lazy!(|| p8);  // <---- erase type, comment out to see effect
///     let p9 = p8.clone().or(p8);
///     let p10 = p9.clone().or(p9);
///     let p11 = p10.clone().or(p10);
///     let p12 = p11.clone().or(p11);
///     let p13 = p12.clone().or(p12);
///     let p14 = p13.clone().or(p13);
///     let p15 = p14.clone().or(p14);
///     let p16 = p15.clone().or(p15);
///     p16
/// }
/// ~~~
///
/// Here, we construct a number of parsers, where
/// the type of each parser contains *twice* the type of the previous parser.
/// Therefore, the type of the last parser has a size that is
/// *exponential* in the number of parsers.
///
/// Or let's rather say that the type of the last parser *would* have exponential size
/// *if* we wouldn't use [`lazy!`] to treat `p8`.
/// (Feel free to comment out this line if you want your CPU to get some exercise.)
/// Indeed, this line erases the type of `p8`, so the size of the total parser remains tractable.
///
/// While this is an artificial example,
/// such large types may well occur in your parsers ---
/// they have certainly occured in mine!
/// In such cases, putting a little [`lazy!`] at strategic places
/// should reduce your build time.
/// It may also decrease your runtime --- if you frequently construct the parser.
///
/// ## Make [`Parser`] clonable
///
/// If you have a parser that does not implement [`Clone`],
/// you might make it clonable by wrapping it in a little [`lazy!`] call:
///
/// ~~~
/// # use parcours::{Parser, lazy, str::take_while};
/// fn non_clonable<'a>() -> impl Parser<&'a str, O = &'a str> {
///     take_while(|_, _| true)
/// }
/// fn clonable<'a>() -> impl Parser<&'a str, O = &'a str> + Clone {
///     lazy!(clonable)
/// }
/// ~~~
///
/// # Background
///
/// In parcours, like in many other parser combinator libraries in Rust,
/// the type of a parser is determined by how the parser is constructed.
/// For example, if we have parsers `p1: P1` and `p2: P2` as well as a function `f: F`,
/// the combined parser `p1.or(p2).map(f)` has the type
/// `Map<Any<(P1, P2)>, F>`:
///
/// ~~~
/// # use parcours::Parser;
/// # use parcours::combinator::{Combinator, Any, Map};
/// fn map_any<I: Clone, S, X, Y, P1, P2, F>(p1: P1, p2: P2, f: F) -> Map<Any<(P1, P2)>, F>
/// where
///     P1: Parser<I, S, O = X>,
///     P2: Parser<I, S, O = X>,
///     F: FnOnce(X) -> Y,
/// {
///     p1.or(p2).map(f)
/// }
/// ~~~
///
/// That means that the type of the parser grows with the size of its definition.
/// The same mechanism occurs when using traits like [`Iterator`].
///
/// What happens when we want to construct an `Iterator` recursively?
///
/// ~~~ compile_fail
/// fn rec_iter() -> impl Iterator<Item = u8> {
///     core::iter::once(0).chain(rec_iter())
/// }
/// ~~~
///
/// This fails, because the compiler points out to us that
/// the return type of `rec_iter` is a "recursive opaque type".
/// In particular, the return type would look something like
/// `Chain<Once<u8>, Chain<Once<u8>, ...>>` and be of infinite size!
/// Rust does not allow that.
///
/// So how do we get around this restriction?
/// When using iterators, we can simply put a `Box` around its definition:
///
/// ~~~
/// fn rec_iter() -> Box<dyn Iterator<Item = u8>> {
///     Box::new(core::iter::once(0).chain(rec_iter()))
/// }
/// ~~~
///
/// The `Box` around our definition effectively erases its type,
/// which allows for the recursive definition to go through.
/// This approach is also used, for example, in the `chumsky` crate.
///
/// I originally tried to use the same approach in parcours;
/// however, I hurt myself against another restriction:
/// In particular, if we have a `Box<dyn Trait>` and we want to call
/// a function of that trait, that function is not allowed to take `self`.
/// It is allowed, however, to take `&self` or `&mut self`.
/// That is why we can box an [`Iterator`], because
/// [`Iterator::next`] takes `&mut self`.
/// Same story for `chumsky`, whose `Parser::parse` function takes `&self`.
/// See the documentation of [`Parser`] for why [`Parser::parse`] takes `self` instead of `&self`.
///
/// So how does [`lazy!`] now actually work?
/// As you can see from its definition, `lazy!(p)` expands to
/// `from_fn(|input, state| p().parse(input, state))`.
/// It turns out that the result of this has a very small type, namely `FromFn<F>`, where
/// `F` *does not contain any information about how the parser `p()` was constructed*.
/// So [`lazy!`] effectively performs type erasure, like boxing an [`Iterator`] did.
/// And this is also precisely what allows us to construct recursive parsers with it.
///
/// I asked myself whether this technique could be transferred over to [`Iterator`].
/// The compiler guided me towards this solution:
///
/// ~~~ compile_fail
/// fn rec_iter() -> impl Iterator<Item = u8> {
///     let mut iter = core::iter::once(0).chain(rec_iter());
///     core::iter::from_fn(move || iter.next())
/// }
/// ~~~
///
/// It does not work! Here, the problem is that
/// [`core::iter::from_fn`] always only yields a *single* element,
/// which means that we *have* to construct `iter` *outside* the closure,
/// if we want to return more than one element.
/// But this means that we again hit the nasty "recursive opaque type" error.
/// So the [`from_fn`] trick that [`lazy!`] so successfully exploits
/// cannot be used for [`Iterator`]. There, we are stuck with `Box` for good.
///
/// # Limitations
///
/// Sometimes, unfortunately,  [`lazy!`] doesn't cut it,
/// in particular when we apply it to parsers returned by closures.
/// In such cases, the compiler complains that we have to `move` stuff into the closures.
/// So here, we may fall back to using [`from_fn`]:
///
/// ~~~
/// # use parcours::{Parser, Combinator, from_fn};
/// fn exp_type<I: Clone, S, P: Parser<I, S>>(p0: impl Fn() -> P + Copy) -> impl Parser<I, S, O = P::O> {
///     let p1 = move || from_fn(move |i, s| p0().parse(i, s)).or(from_fn(move |i, s| p0().parse(i, s)));
///     let p2 = move || from_fn(move |i, s| p1().parse(i, s)).or(from_fn(move |i, s| p1().parse(i, s)));
///     p2()
/// }
/// ~~~
///
/// However, I noticed that in such cases, the build time remains exponential.
/// [`from_fn`] seems to fail to erase types! Yikes.
/// At this point, I have to confess that I do not really know *why* the [`from_fn`] trick works.
/// I just conclude that it must erase types, because we can then construct recursive parsers,
/// but I do not really understand why.
/// If you can point me to the cause, I would be most glad ...
///
/// # Future Work
///
/// On a related subject, I tried really hard to make [`lazy!`] a regular function, but I failed ...
/// For example, consider the following approach:
///
/// ~~~ compile_fail
/// # use parcours::{Parser, from_fn};
/// pub fn lazy2<I, S, P: Parser<I, S>, F: FnOnce() -> P>(f: F) -> impl Parser<I, S, O = P::O> {
///     from_fn(|input, state| f().parse(input, state))
/// }
///
/// fn rec<I, S>() -> impl Parser<I, S, O = ()> {
///     lazy2(rec)
/// }
/// ~~~
///
/// This fails because Rust encounters a "recursive opaque type" in `rec`.
///
/// If you can figure out a way to make [`lazy!`] a function, I would gladly accept a PR.
#[macro_export]
macro_rules! lazy {
    ($p:expr) => {
        $crate::from_fn(|input, state| $p().parse(input, state))
    };
}

/// Lazily construct a parser from a function.
///
/// This can be useful to make a parser that implements [`Clone`] from
/// a function that returns a parser which does *not* implement [`Clone`].
///
/// This function complements the [`lazy!`] macro, as
/// it can be applied in places where [`lazy!`] does not work.
/// In particular, when the compiler suggests that we use `move` when using [`lazy!`]
/// (which seems to happen when we give it a closure), consider this function.
///
/// However, unlike [`lazy!`], this function is not suitable for type erasure,
/// so it cannot be used to construct recursive parsers.
pub fn lazy<I, S, P: Parser<I, S>, F: FnOnce() -> P>(f: F) -> Lazy<F> {
    Lazy(f)
}

/// A parser returned by [`lazy()`].
#[derive(Copy, Clone)]
pub struct Lazy<F>(F);

impl<I, S, P: Parser<I, S>, F: FnOnce() -> P> Parser<I, S> for Lazy<F> {
    type O = P::O;

    fn parse(self, input: I, state: &mut S) -> Option<(Self::O, I)> {
        self.0().parse(input, state)
    }
}

/// A parser returned by [`next`].
pub struct Next<T, S>(core::marker::PhantomData<(T, S)>);

impl<T, S> Copy for Next<T, S> {}

impl<T, S> Clone for Next<T, S> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Run the given parser and return the input it consumed.
///
/// This is implemented for input types `&str` and `&[T]`.
pub fn consumed<I, S, P: Parser<I, S>>(p: P) -> Consumed<I, S, P>
where
    WithConsumed<P>: Parser<I, S, O = (P::O, I)>,
{
    WithConsumed(p).map(|(_y, i)| i)
}

type Consumed<I, S, P> =
    crate::combinator::Map<WithConsumed<P>, fn((<P as Parser<I, S>>::O, I)) -> I>;

/// A parser returned by [`with_consumed`].
#[derive(Copy, Clone)]
pub struct WithConsumed<P>(pub(crate) P);

/// Pattern matching for successful cases.
///
/// When using functions like [`Combinator::filter_map`],
/// we frequently end up with patterns like this:
///
/// ~~~
/// # use parcours::{Parser, Combinator, slice};
/// let p = || slice::next().filter_map(|first| match first {
///     0 => Some(false),
///     1 => Some(true),
///     _ => None,
/// });
/// assert_eq!(p().parse(&[0], &mut ()), Some((false, &[] as &[usize])));
/// assert_eq!(p().parse(&[1], &mut ()), Some((true, &[] as &[usize])));
/// ~~~
///
/// In the `match` statement, we have a few cases that yield [`Some`],
/// followed by a final one yielding [`None`].
/// Because this is such a common case, `select!` allows us to write it like that:
///
/// ~~~
/// # use parcours::{Parser, Combinator, select, slice};
/// let p = || slice::next().filter_map(select!(
///     0 => false,
///     1 => true,
/// ));
/// assert_eq!(p().parse(&[0], &mut ()), Some((false, &[] as &[usize])));
/// assert_eq!(p().parse(&[1], &mut ()), Some((true, &[] as &[usize])));
/// ~~~
///
/// We can also use pattern guards like in normal `match` statements.
///
/// This is inspired by [chumsky's `select!` macro](https://github.com/zesterer/chumsky/blob/40fe7d1966f375b3c676d01e04c5dca08f7615ac/src/lib.rs#L1486).
#[macro_export]
macro_rules! select {
    ($($p:pat $(if $guard:expr)? => $out:expr),+ $(,)?) => (|x| match x {
        $($p $(if $guard)? => ::core::option::Option::Some($out)),+,
        _ => ::core::option::Option::None,
    });
}
