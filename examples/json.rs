//! A JSON value parser.
//!
//! You can test it by running
//!
//!     cargo run --example json -- foo.json
//!
//! to let it parse some file `foo.json`, or
//!
//!     cargo run --example json --
//!
//! to let it parse from standard input (terminate with CTRL-D or similar).
use parcours::str::{matches, take_while};
use parcours::{any, lazy, Combinator, Parser};

/// A JSON value generic over the type of strings `S`.
#[derive(Clone, Debug)]
enum JsonVal<S> {
    Arr(Vec<Self>),
    Map(Vec<(S, Self)>),
    Num(S),
    Str(S),
    True,
    False,
    Null,
}

/// Parse whitespace and return it.
fn space<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    take_while(|c, _| c.is_ascii_whitespace())
}

/// Parse a JSON number and return its string representation.
///
/// This is implemented as state machine to achieve better performance,
/// exploiting that `take_while` accepts mutable closures.
fn num<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    // are we reading the first character?
    let mut first = true;
    // have we encountered no dot so far?
    let mut no_dot = true;
    // have we encountered no exponent character ('e' or 'E') so far?
    let mut no_exp = true;
    take_while(move |c, _| match c {
        b'0'..=b'9' => {
            first = false;
            true
        }
        b'-' if first => core::mem::replace(&mut first, false),
        b'.' if !first && no_dot && no_exp => core::mem::replace(&mut no_dot, false),
        b'e' | b'E' if !first && no_exp => core::mem::replace(&mut no_exp, false),
        _ => false,
    })
    // the last character of a number must always be a digit
    .filter(|s| match s.bytes().last() {
        Some(c) => c.is_ascii_digit(),
        _ => false,
    })
}

/// Parse a string and return it.
///
/// Like `num()`, this is implemented as a state machine.
///
/// This parser does minimal work to handle escaping; in particular,
/// it does not specially handle escaping sequences such as "\n" or "\t",
/// because we can directly use newlines and tabulators in JSON strings,
/// however, this parser handles escaped quotes,
/// otherwise we could not parse any JSON string containing quotes.
fn str<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    // was the previous character an escaping backslash ('\')?
    let mut escaped = false;
    take_while(move |c, _| match c {
        b'\\' if !escaped => {
            escaped = true;
            true
        }
        b'"' if !escaped => false,
        // anything preceded by an escaped backslash is ignored
        _ if escaped => core::mem::replace(&mut escaped, false),
        _ => true,
    })
}

/// Parse a JSON value, possibly followed by some space.
///
/// Here, we use `lazy!` to construct a recursive parser.
fn json<'a>() -> impl Parser<&'a str, O = JsonVal<&'a str>> {
    let str = str().delimited_by(matches("\""), matches("\""));

    let token = |s: &'a str| matches(s).then_ignore(space());
    let arr = lazy!(json).separated_by(token(","));
    let arr = arr.delimited_by(token("["), matches("]"));
    let map = str.clone().then_ignore(token(":")).then(lazy!(json));
    let map = map.separated_by(token(","));
    let map = map.delimited_by(token("{"), matches("}"));

    any((
        arr.map(JsonVal::Arr),
        map.map(JsonVal::Map),
        str.map(JsonVal::Str),
        num().map(JsonVal::Num),
        matches("true").map(|_| JsonVal::True),
        matches("false").map(|_| JsonVal::False),
        matches("null").map(|_| JsonVal::Null),
    ))
    .then_ignore(space())
}

/*
/// Create a JSON array that contains `n` repetitions of `s`.
fn many(s: &str, n: usize) -> String {
    let mut json = "[".to_string();
    json.push_str(s);
    for _ in 1..n {
        json.push(',');
        json.push_str(s);
    }
    json.push(']');
    json
}
*/

fn main() -> std::io::Result<()> {
    /*
    let bla = "y̆es";
    let input = r#"[[1,true  ,   "bla" , 1  , []  ]] []2"#;
    */

    // read from file if one is provided as argument, else from standard input
    let mut args = std::env::args();
    args.next();
    let input = match args.next() {
        Some(arg) => std::fs::read_to_string(arg)?,
        None => std::io::read_to_string(std::io::stdin())?,
    };

    //let input = many(r#"{"key": 12345}"#, 10_000_000);
    //println!("{}", input.len());

    // we first have to strip away any space, because that's what the parser expects
    let out = space().ignore_then(json()).parse(&input, &mut ());
    println!("Parsed JSON: {:?}", out);
    Ok(())
}
