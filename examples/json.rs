use parcours::str::{matches, take_while};
use parcours::{any, lazy, Combinator, Parser};

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

fn space<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    take_while(|c, _| c.is_ascii_whitespace())
}

fn num<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    let mut first = true;
    let mut no_dot = true;
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
    .filter(|s| match s.bytes().last() {
        Some(c) => c.is_ascii_digit(),
        _ => false,
    })
}

fn str<'a, S>() -> impl Parser<&'a str, S, O = &'a str> + Clone {
    let mut escaped = false;
    take_while(move |c, _| match c {
        b'\\' if !escaped => {
            escaped = true;
            true
        }
        b'\\' | b'"' if escaped => core::mem::replace(&mut escaped, false),
        b'"' => false,
        _ => true,
    })
}

fn json<'a>() -> impl Parser<&'a str, O = JsonVal<&'a str>> {
    let str = lazy(str).delimited_by(matches("\""), matches("\""));

    let token = |s: &'a str| matches(s).then_ignore(lazy(space));
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

fn main() {
    //let input = std::fs::read_to_string("canada.json").unwrap();
    /*
    let bla = "y̆es";
    let input = r#"[[1,true  ,   "bla" , 1  , []  ]] []2"#;
    */
    let input = many(r#"{"key": 12345}"#, 10_000_000);
    println!("{}", input.len());
    let out = space().ignore_then(json()).parse(&input, &mut ());
    //println!("{:?}", out);
    if let Some((_out, rest)) = out {
        println!("{:?}", rest);
    }
    //println!("{:?}", recognize("[").parse(input, &mut ()));
}
