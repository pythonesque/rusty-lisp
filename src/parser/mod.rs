mod gram;

use std::collections::VecDeque;
use std::iter::once;
use std::str::SplitWhitespace;
use super::Checkable::*;
use super::{Bindings, Checkable, Context, Inferable, Name, Value};
use self::Stmt::*;

fn de_bruijn_up(i: Name, r: usize, term: Inferable) -> Inferable {
    use super::Inferable::*;
    match term {
        Ann(e, t) => Ann(de_bruijn_down(i.clone(), r, e), de_bruijn_down(i, r, t)),
        Star => Star,
        Pi(t, t_) => Pi(de_bruijn_down(i.clone(), r, t), de_bruijn_down(i, r + 1, t_)),
        Bound(j) => Bound(j),
        Free(y) => if i == y { Bound(r) } else { Free(y) },
        App(box e, e_) => {
            let term = de_bruijn_down(i.clone(), r, e_);
            App(Box::new(de_bruijn_up(i, r, e)), term)
        },
        Nat => Nat,
        Zero => Zero,
        Succ(k) => Succ(de_bruijn_down(i, r, k)),
        NatElim(m, mz, ms, k) =>
            NatElim(de_bruijn_down(i.clone(), r, m), de_bruijn_down(i.clone(), r, mz),
                    de_bruijn_down(i.clone(), r, ms), de_bruijn_down(i, r, k)),
        Vec(a, n) => Vec(de_bruijn_down(i.clone(), r, a), de_bruijn_down(i, r, n)),
        Nil(a) => Nil(de_bruijn_down(i, r, a)),
        Cons(a, k, x, xs) =>
            Cons(de_bruijn_down(i.clone(), r, a), de_bruijn_down(i.clone(), r, k),
                 de_bruijn_down(i.clone(), r, x), de_bruijn_down(i, r, xs)),
        VecElim(a, m, mn, mc, k, vs) =>
            VecElim(de_bruijn_down(i.clone(), r, a), de_bruijn_down(i.clone(), r, m),
                    de_bruijn_down(i.clone(), r, mn), de_bruijn_down(i.clone(), r, mc),
                    de_bruijn_down(i.clone(), r, k), de_bruijn_down(i, r, vs)),
    }
}

fn de_bruijn_down(i: Name, r: usize, term: Checkable) -> Checkable {
    match term {
        Inf(box e) => Inf(Box::new(de_bruijn_up(i, r, e))),
        Lam(box e) => Lam(Box::new(de_bruijn_down(i, r + 1, e))),
    }
}

struct Ctx<'a> { tok: SplitWhitespace<'a>, cur: Option<&'a str> }

fn token(ctx: &mut Ctx) -> Option<Tok> {
    use self::Tok::*;
    ctx.cur
        .and_then( |cur| if cur.is_empty() { ctx.tok.next() } else { Some(cur) } )
        .map( |cur| {
            let (ch, cur_) = cur.slice_shift_char().unwrap();
            ctx.cur = Some(cur_);
            match ch {
                '(' => LParen,
                ')' => RParen,
                ':' => Colon,
                '*' => Star,
                '=' => Eq,
                'λ' => Lambda,
                'Π' => Pi,
                '→' => Arrow,
                '-' => match cur_.slice_shift_char() {
                    Some(('>', cur_)) => {
                        ctx.cur = Some(cur_);
                        Arrow
                    },
                    _ => Error
                },
                '0' => Usize(0),
                '1'...'9' => {
                    let (end, lch) = cur
                        .char_indices()
                        .take_while( |&(_, ch)| ch.is_digit(10) )
                        .last().unwrap();
                    let end = end + lch.len_utf8();
                    ctx.cur = Some(&cur[end ..]);
                    cur[..end].parse().map(Usize).unwrap_or(Error)
                },
                ch if ch.is_alphabetic() => {
                    let (end, lch) = cur
                        .char_indices()
                        .take_while( |&(_, ch)| ch.is_alphanumeric() )
                        .last().unwrap();
                    let end = end + lch.len_utf8();
                    ctx.cur = Some(&cur[end ..]);
                    match &cur[.. end] {
                        "fn" => Lambda,
                        "pi" => Pi,
                        "let" => Let,
                        "Zero" => Zero,
                        "Nat" => Nat,
                        //"ℕ" => Nat,
                        "Succ" => Succ,
                        "natElim" => NatElim,
                        "Vec" => Vec,
                        "Nil" => Nil,
                        "Cons" => Cons,
                        "vecElim" => VecElim,
                        i => Ident(i.into())
                    }
                },
                _ => Error
            }
        })
}

#[derive(Debug)]
pub enum Tok {
    Assume,
    LParen,
    RParen,
    Arrow,
    Colon,
    Lambda,
    Error,
    Ident(String),
    Star,
    Pi,
    Let,
    Eq,
    Usize(usize), // Max is higher than max representable as linked list.
    Zero,
    Nat,
    Succ,
    NatElim,
    Vec,
    Nil,
    Cons,
    VecElim,
}

pub enum Stmt {
    Decl(VecDeque<(Name, Checkable)>),
    Expr(Inferable),
    Bind(String, Inferable),
}

impl Tok {
    fn as_ident(self) -> String {
        match self {
            Tok::Ident(i) => i,
            _ => panic!("as_ident() invoked with a non-identifier"),
        }
    }

    fn as_usize(self) -> usize {
        match self {
            Tok::Usize(i) => i,
            _ => panic!("as_usize() invoked with a non-usize"),
        }
    }
}

impl<'a> Iterator for Ctx<'a> {
    type Item = Tok;

    fn next(&mut self) -> Option<Tok> {
        token(self)
    }
}

pub fn parse(s: &str, ctx: &mut Context, bindings: &mut Bindings) -> Result<Option<Inferable>, ()> {
    let s = s.trim_left();
    let mut tokens = s.split_whitespace();
    match tokens.next() {
        Some("assume") => {
            let cur = tokens.next();
            self::gram::parse_S(once(Tok::Assume).chain(Ctx { tok: tokens, cur: cur }))
        },
        None => return Ok(None),
        cur => self::gram::parse_S(Ctx { tok: tokens, cur: cur })
    }.or(Err(())).map( |(_, inf)| match inf {
        Decl(d) => {
            for (v, c) in d {
                let c = ::global_sub_down(bindings, c);
                if ::type_down(0, ctx.clone(), c.clone(), Value::Star).is_ok() {
                    ctx.push_front((v, ::eval_down(c, VecDeque::new())));
                }
            }
            None
        },
        Expr(e) => {
            let e = ::global_sub_up(bindings, e);
            Some(e)
        },
        Bind(v, e) => {
            let e = ::global_sub_up(bindings, e);
            Some(match ::type_up_0(ctx.clone(), e.clone()) {
                Ok(ty) => {
                    bindings.insert(v.clone(), e.clone());
                    ctx.push_front((Name::Global(v.clone()), ty));
                    Inferable::Free(Name::Global(v))
                },
                Err(_) => e
            })
        }
    })
}
