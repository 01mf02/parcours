//! Pocket Calculator on integers.
//!
//! This example implements an interactive calculator à la `bc`.
//! Its aim is to show the separation of lexing and parsing phases
//! as well as precedence climbing.
//!
//! You can try it with:
//!
//!     cargo run --example bc
//!
//! Example inputs:
//! * 1+1        -> 2
//! * 1 + 2 + 3  -> 6
//! * 1+5*2      -> 11
//! * (1+5)*2    -> 12
//! * 2^2^3      -> 256
//! * (2^2)^3    -> 64
//! * 1+?        -> lex error
//! * 1+         -> parse error
//!
//! To keep this example focused, error reporting is minimal,
//! but could be implemented following the `lambda` example.
use core::convert::TryInto;
use parcours::prec_climb::{self, Associativity};
use parcours::{any, from_fn, lazy, select, slice, str, Combinator, Parser};

// First, we will define the lexer.
// A lexer operators an a string and yields a sequence of tokens.

/// A token as returned by the lexer.
#[derive(Debug, PartialEq, Eq)]
enum Token {
    /// Number
    ///
    /// Negative integers are represented by combinations of `Token::Op(Op::Sub)` and `Token::Num`.
    Num(usize),
    /// Opening parenthesis
    LPar,
    /// Closing parenthesis
    RPar,
    /// Binary operator
    Op(Op),
}

/// Binary operator.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Op {
    /// Addition (+)
    Add,
    /// Subtraction (-)
    Sub,
    /// Multiplication (*)
    Mul,
    /// Division (/)
    Div,
    /// Exponentiation (^)
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

/// Lex a token.
///
/// Here, we can see that conceptually, a lexer is also just a parser.
fn token<'a>() -> impl Parser<&'a str, O = Token> + Clone {
    // try to match a given binary operator and return it if it is present
    let match_op = |op: Op| {
        from_fn(move |input: &str, _| Some((Token::Op(op), input.strip_prefix(op.as_char())?)))
    };
    any((
        // nonempty sequence of digits
        str::take_while1(|c, _| c.is_ascii_digit()).map(|n| Token::Num(n.parse().unwrap())),
        str::matches("(").map(|_| Token::LPar),
        str::matches(")").map(|_| Token::RPar),
        // for every operator, try to match it
        any([Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Exp].map(match_op)),
    ))
}

/// Parse whitespace.
fn space<'a>() -> impl Parser<&'a str, O = &'a str> + Clone {
    str::take_while(|c, _| c.is_ascii_whitespace())
}

/// Lex.
fn tokens<'a>() -> impl Parser<&'a str, O = Vec<Token>> + Clone {
    space().ignore_then(token().then_ignore(space()).repeated())
}

// We are now done with the lexer.
// Next up: the parser.

/// Expression.
#[derive(Debug)]
enum Expr {
    /// Number
    Num(usize),
    /// Negation
    Neg(Box<Expr>),
    /// Combination of two expressions with a binary operator
    Comb(Box<Expr>, Op, Box<Expr>),
}

impl Expr {
    /// Evaluate an expression.
    fn eval(&self) -> isize {
        match self {
            Self::Num(n) => (*n).try_into().unwrap(),
            Self::Neg(e) => -e.eval(),
            Self::Comb(l, op, r) => op.eval(l.eval(), r.eval()),
        }
    }
}

/// Parse an atomic expression.
///
/// An atomic expression is a (possibly empty) sequence of negations,
/// followed by a number or a parenthesised expression.
///
/// Where the lexer had `&str` as input type,
/// the parser has the output of the lexer as input type, namely `&[Token]`.
/// That means that we use
/// `parcours::slice` functions here instead of
/// `parcours::str`   functions.
fn atomic<'a>() -> impl Parser<&'a [Token], O = Expr> {
    // succeed if the first element in the slice is the token `tk`
    let eq = |tk| slice::first_filter(move |t, _| *t == tk);
    // parentheses
    let par = lazy!(expr).delimited_by(eq(Token::LPar), eq(Token::RPar));
    // if the first token is a number, return a number expression, else fail
    let num = slice::first_filter_map(select!(Token::Num(n) => Expr::Num(*n)));
    let neg = slice::first_filter(|t, _| *t == Token::Op(Op::Sub));
    let negs = neg.repeated::<Vec<_>>();
    negs.then(par.or(num))
        .map(|(negs, atom)| negs.iter().fold(atom, |acc, _x| Expr::Neg(Box::new(acc))))
}

/// Parse an expression from a token slice.
///
/// An expression is an atomic term followed by
/// a (possibly empty) sequence of operator-atomic term pairs.
///
/// This uses precedence climbing to respect operator precedences.
fn expr<'a>() -> impl Parser<&'a [Token], O = Expr> {
    let op = slice::first_filter_map(select!(Token::Op(op) => *op));
    atomic()
        .then(op.then(lazy!(atomic)).repeated::<Vec<_>>())
        // for precedence climbing to work, we have to implement
        // a few traits for operators and expressions, see below
        .map(|(head, tail)| prec_climb::climb(head, tail))
}

impl prec_climb::Op for Op {
    fn precedence(&self) -> usize {
        match self {
            Op::Add | Op::Sub => 0,
            Op::Mul | Op::Div => 1,
            Op::Exp => 2,
        }
    }

    /// All operators are left-associative, except for exponentiation.
    fn associativity(&self) -> Associativity {
        match self {
            Op::Exp => Associativity::Right,
            _ => Associativity::Left,
        }
    }
}

impl prec_climb::Expr<Op> for Expr {
    fn from_op(lhs: Self, op: Op, rhs: Self) -> Self {
        Self::Comb(Box::new(lhs), op, Box::new(rhs))
    }
}

fn main() -> std::io::Result<()> {
    for line in std::io::stdin().lines() {
        let line = line?;
        let lexed = tokens().parse(&line, &mut ());
        println!("Lexer output: {lexed:?}");
        let (tokens, rest) = lexed.unwrap();
        assert!(rest.is_empty(), "lex error");
        let parsed = expr().parse(&tokens, &mut ());
        println!("Parser output: {parsed:?}");
        let (expr, rest) = parsed.unwrap();
        assert!(rest.is_empty(), "parse error");
        println!("Result: {}", expr.eval());
    }
    Ok(())
}
