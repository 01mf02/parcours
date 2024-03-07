//! A lambda expression parser.
//!
//! This example showcases the Art of the State; that is,
//! how to use parcours's mutable state to:
//! * store currently bound variables,
//! * record multiple recoverable errors,
//! * report a single non-recoverable error.
//!
//! You can try the following examples:
//! * `|x y| x`
//! * `|x y| y x`
//! * `|x y  x` <-- fails because `|` is not terminated
//! * `|x| |y| x`
//! * `|x| x y z` <-- fails because `y` and `z` are not bound
//! * `|x x| x
//! * `|fst snd| fst`
//! * `|x y| || x`
//! * `|一 二| 一`
//! * `|0| 0` <-- fails, because identifiers may not start with a digit
//! * `+` <-- fails, because this is not a valid term
//!
//! Many parsers in this example that do not access the state
//! are generic over any state `S`, whereas those which access the state
//! use `State`.
use parcours::str::{matches, take_while};
use parcours::{from_fn, lazy, Combinator, Parser};

/// A lambda expression.
#[derive(Debug)]
enum Term<'a> {
    /// Abstraction
    ///
    /// This has the shape `|x0 ... xn| t`, where
    /// `x0` to `xn` may be a (possibly empty) sequence of identifiers, and
    /// `t` is a term.
    Abst(Vec<&'a str>, Box<Self>),
    /// Application
    ///
    /// This has the shape `t t1 ... tn`, where
    /// `t` is a term and
    /// `t1` to `tn` is a non-empty sequence of terms.
    Appl(Box<Self>, Vec<Self>),
    /// Variable
    ///
    /// This is a [de Bruijn index](https://en.wikipedia.org/wiki/De_Bruijn_index)
    /// that points to a variable bound in an abstraction.
    Var(usize),
}

/// State of the parser.
#[derive(Default)]
struct State<'a> {
    /// currently bound variables
    vars: Vec<&'a str>,
    /// binding errors
    errs: Vec<Error<'a>>,
    /// parsing error (only one, namely the first, is recorded)
    expected: Option<(&'static str, &'a str)>,
}

#[derive(Debug)]
enum Error<'a> {
    UnboundVar(&'a str),
}

/// Parse whitespace and return it.
fn space<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    take_while(|c, _| c.is_ascii_whitespace())
}

/// Parse an identifier, potentially followed by whitespace.
///
/// An identifier consists of characters that are
/// either not in ASCII (such as 'ä') or that are alphanumeric ASCII.
/// Furthermore, the first character of an identifier must not be a digit.
fn ident<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    let pn = |c: &u8, _: &mut S| !c.is_ascii() || c.is_ascii_alphanumeric();
    let p0 = |c: char| !c.is_ascii_digit();
    take_while(pn)
        .filter(move |s| s.chars().next().map(p0).unwrap_or(false))
        .then_ignore(space())
}

/// Parse the given string, potentially followed by whitespace.
fn token<S>(x: &str) -> impl Parser<&str, S, O = ()> + Clone {
    matches(x).then_ignore(space())
}

/// Store the given error `s` if no other error was stored before, then fail.
///
/// Here, we use `from_fn` to implement some custom parsing logic
/// that we cannot express with the normal parser combinators in parcours,
/// in particular because we access and modify the state here.
///
/// We only store an error if no other error was stored before.
/// This is to prevent cascading errors which might be more confusing than helpful.
fn expected<'a, O>(s: &'static str) -> impl Parser<&'a str, State<'a>, O = O> + Clone {
    from_fn(move |input, state: &mut State| {
        state.expected.get_or_insert((s, input));
        None
    })
}

/// Parse an atomic term, namely either a variable or a term enclosed by parentheses.
fn atomic<'a>() -> impl Parser<&'a str, State<'a>, O = Term<'a>> + Clone {
    let var = ident().map_with(|v, state: &mut State<'a>| {
        // find the de Bruijn index of the variable
        let db = state.vars.iter().rev().position(|b| *b == v);
        // if the variable was not bound, then record this as error, but then continue,
        // because such errors are not fatal parsing errors
        Term::Var(db.unwrap_or_else(|| {
            state.errs.push(Error::UnboundVar(v));
            0
        }))
    });
    // here, we see error reporting in action:
    // if a term that was opened with a parenthesis is not closed by a parenthesis,
    // we store an error message and fail
    var.or(lazy!(term).delimited_by(token("("), token(")").or(expected("closing parenthesis"))))
}

/// Extend the state with variables, parse with `p`, then remove the variables again.
fn with_vars<'a, I, P>(vars: Vec<&'a str>, p: P) -> impl Parser<I, State<'a>, O = P::O>
where
    P: Parser<I, State<'a>>,
{
    from_fn(|input, state: &mut State<'a>| {
        let vars_len = vars.len();
        state.vars.extend(vars);
        let y = p.parse(input, state);
        state.vars.truncate(state.vars.len() - vars_len);
        y
    })
}

/// Parse a term.
fn term<'a>() -> impl Parser<&'a str, State<'a>, O = Term<'a>> {
    let vars = ident()
        .repeated()
        .delimited_by(token("|"), token("|").or(expected("identifier or |")));
    let abst = vars.and_then(|vars: Vec<_>| {
        // we parse a term with the bound variables put into the state
        with_vars(vars.clone(), lazy!(term)).map(|t| (Term::Abst(vars, Box::new(t))))
    });
    let args = atomic().repeated::<Vec<_>>();
    let appl = atomic().then(args).map(|(head, args)| {
        if args.is_empty() {
            head
        } else {
            Term::Appl(Box::new(head), args)
        }
    });
    abst.or(appl).then_ignore(space()).or(expected("term"))
}

fn handle(input: &str) {
    let mut state = State::default();
    let output = term().parse(input, &mut state);
    println!("{:?}", output);
    if let Some((e, location)) = state.expected {
        eprintln!("Error: expected {e} at {location}");
    }
    for e in state.errs {
        match e {
            Error::UnboundVar(v) => {
                let offset = v.as_ptr() as usize - input.as_ptr() as usize;
                println!("Error: unbound variable \"{v}\" at byte {offset}");
            }
        }
    }
}

fn main() -> std::io::Result<()> {
    //let input = r#"(|ä y| (ä y) X0) x  "#;
    std::io::stdin().lines().try_for_each(|line| {
        Ok(handle(&line?))
    })
}
