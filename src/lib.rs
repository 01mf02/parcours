//! Parser Combinators for Unique Results.
#![no_std]
#![forbid(unsafe_code)]

pub mod prec_climb;
pub mod str;
mod parser;

pub use parser::{Parser, any, all, from_fn, repeat, separate_by};

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
/// # use parcours::{Parser, lazy};
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
/// # use parcours::{Parser, lazy};
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
/// There are some parsers, such as [`str::take_while0`], that do not implement [`Clone`].
/// In such a case, we can make it clonable by wrapping it in a little [`lazy!`] call:
///
/// ~~~
/// # use parcours::{Parser, lazy, str::take_while0};
/// fn everything<'a>() -> impl Parser<&'a str, O = &'a str> + Clone {
///     lazy!(|| take_while0(|_| true))
/// }
/// ~~~
///
/// # Background
///
/// In parcours, like in many other parser combinator libraries in Rust,
/// the type of a parser is determined by how the parser is constructed.
/// For example, if we have parsers `p1: P1` and `p2: P2` as well as a function `f: F`,
/// the combined parser `p1.or(p2).map(f)` has the type
/// `Map<Any<(P1, P2)>, F>`.
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
/// # use parcours::{Parser, from_fn};
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
        parcours::from_fn(|input, state| $p().parse(input, state))
    };
}
