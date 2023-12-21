//! Art of the State

use parcours::str::{matches, take_while0};
use parcours::{from_fn, lazy, Parser};

#[derive(Debug)]
enum Error<'a> {
    UnboundVar(&'a str),
}

#[derive(Default)]
struct State<'a> {
    vars: Vec<&'a str>,
    errs: Vec<Error<'a>>,
}

fn space<'a, S>() -> impl Parser<&'a str, S, O = &'a str> {
    take_while0(|c| c.is_ascii_whitespace())
}

fn ident<'a, S>() -> impl Parser<&'a str, S, O = &'a str> {
    let pn = |c: &u8| !c.is_ascii() || c.is_ascii_alphanumeric();
    let p0 = |c: char| !c.is_ascii_digit();
    take_while0(pn)
        .filter(move |s| s.chars().next().map(p0).unwrap_or(false))
        .then_ignore(space())
}

#[derive(Debug)]
enum Term<'a> {
    Abst(Vec<&'a str>, Box<Self>),
    Appl(Box<Self>, Vec<Self>),
    Var(usize),
}

fn token<S>(x: &str) -> impl Parser<&str, S, O = ()> {
    matches(x).then_ignore(space())
}

fn atomic<'a>() -> impl Parser<&'a str, State<'a>, O = Term<'a>> {
    let var = ident().map_with(|v, state: &mut State<'a>| {
        let db = state.vars.iter().rev().position(|b| *b == v);
        Term::Var(db.unwrap_or_else(|| {
            state.errs.push(Error::UnboundVar(v));
            0
        }))
    });
    var.or(lazy!(term).delimited_by(token("("), token(")")))
}

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

fn term<'a>() -> impl Parser<&'a str, State<'a>, O = Term<'a>> {
    let vars = lazy!(ident).repeated().delimited_by(token("|"), token("|"));
    let abst = vars.and_then(|vars: Vec<_>| {
        with_vars(vars.clone(), lazy!(term)).map(|t| (Term::Abst(vars, Box::new(t))))
    });
    let args = lazy!(atomic).repeated::<Vec<_>>();
    let appl = atomic().then(args).map(|(head, args)| {
        if args.is_empty() {
            head
        } else {
            Term::Appl(Box::new(head), args)
        }
    });
    abst.or(appl).then_ignore(space())
}

fn main() {
    let input = r#"(|ä y| (ä y) X0) x  "#;
    let mut state = State::default();
    let output = term().parse(input, &mut state);
    println!("{:?}", output);
    for e in state.errs {
        match e {
            Error::UnboundVar(v) => {
                let offset = v.as_ptr() as usize - input.as_ptr() as usize;
                println!("Error: unbound variable \"{v}\" at byte {offset}");
            }
        }
    }
}
