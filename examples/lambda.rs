//! Art of the State

use parcours::str::{matches, take_while};
use parcours::{from_fn, lazy, Combinator, Parser};

#[derive(Debug)]
enum Error<'a> {
    UnboundVar(&'a str),
}

#[derive(Default)]
struct State<'a> {
    vars: Vec<&'a str>,
    errs: Vec<Error<'a>>,
    expected: Option<(&'static str, &'a str)>,
}

fn space<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    take_while(|c, _| c.is_ascii_whitespace())
}

fn ident<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    let pn = |c: &u8, _: &mut S| !c.is_ascii() || c.is_ascii_alphanumeric();
    let p0 = |c: char| !c.is_ascii_digit();
    take_while(pn)
        .filter(move |s| s.chars().next().map(p0).unwrap_or(false))
        .then_ignore(space())
}

#[derive(Debug)]
enum Term<'a> {
    Abst(Vec<&'a str>, Box<Self>),
    Appl(Box<Self>, Vec<Self>),
    Var(usize),
}

fn token<S>(x: &str) -> impl Parser<&str, S, O = ()> + Clone {
    matches(x).then_ignore(space())
}

fn expected<'a, O>(s: &'static str) -> impl Parser<&'a str, State<'a>, O = O> + Clone {
    from_fn(move |input, state: &mut State| {
        state.expected.get_or_insert((s, input));
        None
    })
}

fn atomic<'a>() -> impl Parser<&'a str, State<'a>, O = Term<'a>> + Clone {
    let var = ident().map_with(|v, state: &mut State<'a>| {
        let db = state.vars.iter().rev().position(|b| *b == v);
        Term::Var(db.unwrap_or_else(|| {
            state.errs.push(Error::UnboundVar(v));
            0
        }))
    });
    var.or(lazy!(term).delimited_by(token("("), token(")").or(expected("closing parenthesis"))))
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
    let vars = ident()
        .repeated()
        .delimited_by(token("|"), token("|").or(expected("identifier or |")));
    let abst = vars.and_then(|vars: Vec<_>| {
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

fn main() {
    //let input = r#"(|ä y| (ä y) X0) x  "#;
    for line in std::io::stdin().lines() {
        handle(&line.unwrap())
    }
}
