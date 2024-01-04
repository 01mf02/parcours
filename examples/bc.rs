//! Pocket Calculator.

use core::convert::TryInto;
use parcours::prec_climb::{self, Associativity};
use parcours::str::{matches, take_while, take_while1};
use parcours::{any, from_fn, lazy, select, slice, Combinator, Parser};

#[derive(Debug, PartialEq, Eq)]
enum Token {
    Num(usize),
    LPar,
    RPar,
    Op(Op),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Exp,
}

impl Op {
    fn as_char(&self) -> char {
        match self {
            Op::Add => '+',
            Op::Sub => '-',
            Op::Mul => '*',
            Op::Div => '/',
            Op::Exp => '^',
        }
    }

    fn eval(&self, l: isize, r: isize) -> isize {
        match self {
            Self::Add => l + r,
            Self::Sub => l - r,
            Self::Mul => l * r,
            Self::Div => l / r,
            Self::Exp => l.pow(r.try_into().unwrap()),
        }
    }
}

impl prec_climb::Op for Op {
    fn precedence(&self) -> usize {
        match self {
            Op::Add | Op::Sub => 0,
            Op::Mul | Op::Div => 1,
            Op::Exp => 2,
        }
    }

    fn associativity(&self) -> Associativity {
        match self {
            Op::Exp => Associativity::Right,
            _ => Associativity::Left,
        }
    }
}

#[derive(Debug)]
enum Expr {
    Num(usize),
    Neg(Box<Expr>),
    Comb(Box<Expr>, Op, Box<Expr>),
}

impl Expr {
    fn eval(&self) -> isize {
        match self {
            Self::Num(n) => (*n).try_into().unwrap(),
            Self::Neg(e) => -e.eval(),
            Self::Comb(l, op, r) => op.eval(l.eval(), r.eval()),
        }
    }
}

impl prec_climb::Expr<Op> for Expr {
    fn from_op(lhs: Self, op: Op, rhs: Self) -> Self {
        Self::Comb(Box::new(lhs), op, Box::new(rhs))
    }
}

fn token<'a>() -> impl Parser<&'a str, O = Token> + Clone {
    let match_op = |op: Op| {
        from_fn(move |input: &str, _| Some((Token::Op(op), input.strip_prefix(op.as_char())?)))
    };
    any((
        take_while1(|c, _| c.is_ascii_digit()).map(|n| Token::Num(n.parse().unwrap())),
        matches("(").map(|_| Token::LPar),
        matches(")").map(|_| Token::RPar),
        any([Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Exp].map(match_op)),
    ))
}

fn space<'a>() -> impl Parser<&'a str, O = &'a str> + Clone {
    take_while(|c, _| c.is_ascii_whitespace())
}

fn tokens<'a>() -> impl Parser<&'a str, O = Vec<Token>> + Clone {
    space().ignore_then(token().then_ignore(space()).repeated())
}

fn atomic<'a>() -> impl Parser<&'a [Token], O = Expr> {
    let eq = |tk| slice::first_filter(move |t, _| *t == tk);
    let par = lazy!(expr).delimited_by(eq(Token::LPar), eq(Token::RPar));
    let num = slice::first_filter_map(select!(Token::Num(n) => Expr::Num(*n)));
    let neg = lazy!(|| slice::first_filter(|t, _| *t == Token::Op(Op::Sub)));
    let negs = neg.repeated::<Vec<_>>();
    negs.then(par.or(num))
        .map(|(negs, atom)| negs.iter().fold(atom, |acc, _x| Expr::Neg(Box::new(acc))))
}

fn expr<'a>() -> impl Parser<&'a [Token], O = Expr> {
    let op = || slice::first_filter_map(select!(Token::Op(op) => *op));
    atomic()
        .then(lazy(op).then(lazy!(atomic)).repeated::<Vec<_>>())
        .map(|(head, tail)| prec_climb::climb(head, tail))
}

fn main() {
    for line in std::io::stdin().lines() {
        let line = line.unwrap();
        let lexed = tokens().parse(&line, &mut ());
        println!("{lexed:?}");
        let tokens = lexed.unwrap().0;
        let parsed = expr().parse(&tokens, &mut ());
        println!("{parsed:?}");
        let expr = parsed.unwrap().0;
        println!("{}", expr.eval());
    }
}
