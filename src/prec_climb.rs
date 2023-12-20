//! Precedence climbing for parsing expressions with binary operators.
//!
//! This was adapted from
//! <https://ycpcs.github.io/cs340-fall2017/lectures/lecture06.html#implementation>.
//!
//! ~~~
//! use parcours::prec_climb::{self, Associativity, Expr};
//!
//! enum Op {
//!     Add,
//!     Sub,
//!     Mul,
//!     Div,
//! }
//!
//! impl prec_climb::Op for Op {
//!     fn precedence(&self) -> usize {
//!         match self {
//!             Op::Add | Op::Sub => 0,
//!             Op::Mul | Op::Div => 1,
//!         }
//!     }
//!
//!     fn associativity(&self) -> Associativity {
//!         Associativity::Right
//!     }
//! }
//!
//! impl Expr<Op> for isize {
//!     fn from_op(lhs: Self, op: Op, rhs: Self) -> Self {
//!         match op {
//!             Op::Add => lhs + rhs,
//!             Op::Sub => lhs - rhs,
//!             Op::Mul => lhs * rhs,
//!             Op::Div => lhs / rhs,
//!         }
//!     }
//! }
//!
//! # fn test() {
//! use Op::{Add, Div, Mul, Sub};
//! // 1 + 2 * 3 - 6 / 2 =
//! // 1 +   6   -   3   = 4
//! let head: isize = 1;
//! let tail = [(Add, 2), (Mul, 3), (Sub, 6), (Div, 2)];
//! let out = prec_climb::climb(head, tail);
//! assert_eq!(out, 4);
//! # }
//! ~~~

use core::iter::Peekable;

pub enum Associativity {
    Left,
    Right,
}

pub trait Op {
    fn precedence(&self) -> usize;
    fn associativity(&self) -> Associativity;
}

pub trait Expr<O: Op> {
    fn from_op(lhs: Self, op: O, rhs: Self) -> Self;
}

//
pub fn climb<O: Op, T: Expr<O>>(head: T, iter: impl IntoIterator<Item = (O, T)>) -> T {
    climb1(head, &mut iter.into_iter().peekable(), 0)
}

fn climb1<O: Op, T: Expr<O>, I>(mut x: T, iter: &mut Peekable<I>, min_prec: usize) -> T
where
    I: Iterator<Item = (O, T)>,
{
    while let Some((op, mut rhs)) = iter.next_if(|(op, _)| op.precedence() >= min_prec) {
        let right_assoc = matches!(op.associativity(), Associativity::Right);
        let this_prec = op.precedence();

        while let Some(next) = iter.peek() {
            let next_prec = next.0.precedence();

            if next_prec > this_prec || (right_assoc && next_prec == this_prec) {
                rhs = climb1(rhs, iter, next_prec)
            } else {
                break;
            }
        }
        x = T::from_op(x, op, rhs);
    }
    x
}
