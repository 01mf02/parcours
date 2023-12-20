use parcours::str::{matches, take_while0, take_while1};
use parcours::{any, lazy, separate_by, Parser};

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

fn space<'a, S>() -> impl Parser<&'a str, S, O = &'a str> {
    take_while0(|c| c.is_ascii_whitespace())
}

fn num<'a, S>() -> impl Parser<&'a str, S, O = &'a str> {
    let mut first = true;
    let mut no_dot = true;
    let mut no_exp = true;
    take_while1(move |c| match c {
        b'0'..=b'9' => {
            first = false;
            true
        }
        b'-' if first => core::mem::replace(&mut first, false),
        b'.' if !first && no_dot && no_exp => core::mem::replace(&mut no_dot, false),
        b'e' | b'E' if !first && no_exp => core::mem::replace(&mut no_exp, false),
        _ => false,
    })
}

fn minijson<'a>() -> impl Parser<&'a str, O = JsonVal<&'a str>> {
    let rec = || lazy!(minijson);
    let str_ = || take_while0(|c| *c != b'"').map(|s| s);
    let str_ = move || str_().delimited_by(matches("\""), matches("\""));

    let token = |s: &'a str| matches(s).then_ignore(space());
    let arr = separate_by(rec, move || token(","));
    let arr = arr.delimited_by(token("["), matches("]"));
    let map = move || str_().then_ignore(token(":")).then(rec());
    let map = separate_by(map, move || token(","));
    let map = map.delimited_by(token("{"), matches("}"));

    any((
        arr.map(JsonVal::Arr),
        map.map(JsonVal::Map),
        str_().map(JsonVal::Str),
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
    let input = std::fs::read_to_string("canada.json").unwrap();
    /*
    let bla = "y̆es";
    let input = r#"[[1,true  ,   "bla" , 1  , []  ]] []2"#;
    */
    //let input = many(r#"{"key": 12345}"#, 10_000_000);
    println!("{}", input.len());
    let out = space().ignore_then(minijson()).parse(&input, &mut ());
    //println!("{:?}", out);
    if let Some((out, rest)) = out {
        println!("{:?}", rest);
    }
    //println!("{:?}", recognize("[").parse(input, &mut ()));
}
