mod gram;

use std::str::SplitWhitespace;
use std::iter::once;
use super::Inferable::*;
use super::Checkable::*;
use super::{Checkable, Context, Inferable, Name};
use self::Stmt::*;
use self::Tok::*;

fn de_bruijn_up(i: Name, r: usize, term: Inferable) -> Inferable {
    match term {
        Ann(e, t) => Ann(de_bruijn_down(i, r, e), t),
        Bound(j) => Bound(j),
        Free(y) => if i == y { Bound(r) } else { Free(y) },
        App(box e, e_) => {
            let term = de_bruijn_down(i.clone(), r, e_);
            App(Box::new(de_bruijn_up(i, r, e)), term)
        },
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
                '-' => match cur_.slice_shift_char() {
                    Some(('>', cur_)) => {
                        ctx.cur = Some(cur_);
                        Arrow
                    },
                    _ => Error
                },
                ch if ch.is_alphabetic() => {
                    let end = cur
                        .char_indices()
                        .take_while( |&(_, ch)| ch.is_alphanumeric() )
                        .last().unwrap().0 + ch.len_utf8();
                    ctx.cur = Some(&cur[end ..]);
                    match &cur[.. end] {
                        "fn" => Lambda,
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
}

pub enum Stmt {
    Decl(Context),
    Expr(Inferable),
}

impl Tok {
    fn as_ident(self) -> String {
        match self {
            Ident(i) => i,
            _ => panic!("as_ident() invoked with a non-identifier"),
        }
    }
}

impl<'a> Iterator for Ctx<'a> {
    type Item = Tok;

    fn next(&mut self) -> Option<Tok> {
        token(self)
    }
}

pub fn parse(s: &str, ctx: &mut Context) -> Result<Option<Inferable>, ()> {
    let s = s.trim_left();
    let mut tokens = s.split_whitespace();
    match tokens.next() {
        Some("assume") => {
            let cur = tokens.next();
            self::gram::parse_S(once(Assume).chain(Ctx { tok: tokens, cur: cur }))
        },
        cur => self::gram::parse_S(Ctx { tok: tokens, cur: cur })
    }.or(Err(())).map( |(_, inf)| match inf {
        Decl(d) => {
            ctx.extend(d);
            None
        },
        Expr(e) => Some(e),
    })
}
