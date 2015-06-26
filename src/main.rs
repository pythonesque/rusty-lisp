#![feature(box_patterns)]
#![feature(str_char)]

//extern crate rusty_lisp;

mod parser;

use std::collections::VecDeque;
use std::rc::Rc;

#[derive(Clone,PartialEq,Debug)]
pub enum Inferable {
    Ann(Checkable, Type),
    Bound(usize),
    Free(Name),
    App(Box<Inferable>, Checkable),
}

#[derive(Clone,PartialEq,Debug)]
pub enum Checkable {
    Inf(Box<Inferable>),
    Lam(Box<Checkable>),
}

#[derive(PartialEq,Clone,Debug)]
pub enum Name {
    Global(String),
    Local(usize),
    Quote(usize),
}

#[derive(Clone,PartialEq,Debug)]
pub enum Type {
    Free(Name),
    Fun(Box<Type>, Box<Type>),
}

#[derive(Clone)]
enum Value {
    Lam(Rc<Fn(Value) -> Value>),
    Neutral(Neutral),
}

#[derive(Clone)]
enum Neutral {
    Free(Name),
    App(Box<Neutral>, Box<Value>),
}

fn vfree(name: Name) -> Value {
    Value::Neutral(Neutral::Free(name))
}

type Env = VecDeque<Value>;

fn eval_up(term: Inferable, d: Env) -> Value {
    use self::Inferable::*;
    match term {
        Ann(e, _) => eval_down(e, d),
        Free(x) => vfree(x),
        Bound(i) => d[i].clone(),
        App(box e, e_) => {
            let e = eval_up(e, d.clone());
            let e_ = eval_down(e_, d);
            vapp(e, e_)
        }
    }
}

fn vapp(value: Value, v: Value) -> Value {
    match value {
        Value::Lam(f) => f(v),
        Value::Neutral(n) => Value::Neutral(Neutral::App(Box::new(n), Box::new(v))),
    }
}

fn eval_down(term: Checkable, d: Env) -> Value {
    use self::Checkable::*;
    match term {
        Inf(box i) => eval_up(i, d),
        Lam(box e) => {
            Value::Lam(Rc::new(move |x| {
                let mut d = d.clone();
                d.push_front(x);
                eval_down(e.clone(), d)
            }))
        },
    }
}

macro_rules! throw_error ( ($s:expr) => {{ return Err($s.into()) }} );

fn kind_down(ctx: Context, ty: Type, k: Kind) -> Result<()> {
    match (ty, k) {
        (Type::Free(ref x), Kind::Star) => match ctx.into_iter().find(|&(ref name, ref i)| name == x && if let Info::HasKind(_) = *i { true} else { false }) {
            Some((_, Info::HasKind(Kind::Star))) => Ok(()),
            None => throw_error!("unknown identifier"),
            _ => panic!("Free variable should not have a type"),
        },
        (Type::Fun(box k, box k_), Kind::Star) => {
            try!(kind_down(ctx.clone(), k, Kind::Star));
            kind_down(ctx, k_, Kind::Star)
        }
    }
}

fn type_up_0(ctx: Context, term: Inferable) -> Result<Type> {
    type_up(0, ctx, term)
}

fn type_up(i: usize, ctx: Context, term: Inferable) -> Result<Type> {
    use self::Inferable::*;
    match term {
        Ann(e, t) => {
            try!(kind_down(ctx.clone(), t.clone(), Kind::Star));
            try!(type_down(i, ctx, e, t.clone()));
            Ok(t)
        },
        Free(ref x) => match ctx.into_iter().find(|&(ref name, ref i)| name == x && if let Info::HasType(_) = *i { true } else { false }) {
            Some((_, Info::HasType(t))) => Ok(t),
            None => throw_error!("unknown identifier"),
            _ => panic!("Free variable should not have a kind"),
        },
        App(box e, e_) => {
            let o = try!(type_up(i, ctx.clone(), e));
            match o {
                Type::Fun(box t, box t_) => {
                    try!(type_down(i, ctx, e_, t));
                    Ok(t_)
                },
                _ => throw_error!("illegal application")
            }
        },
        Bound(_) => panic!("Should never see a bound variable here, as this should be taken care of in the type rule for lambda abstraction."),
    }
}

fn type_down(i: usize, mut ctx: Context, term: Checkable, ty: Type) -> Result<()> {
    use self::Checkable::*;
    match (term, ty) {
        (Inf(box e), t) => {
            let t_ = try!(type_up(i, ctx.clone(), e));
            if t != t_ { throw_error!("type mismatch"); }
            Ok(())
        },
        (Lam(box e), Type::Fun(box t, box t_)) => {
            //let mut ctx = ctx.clone();
            ctx.push_front((Name::Local(i), Info::HasType(t)));
            type_down(i + 1, ctx, subst_down(0, Inferable::Free(Name::Local(i)), e), t_)
        },
        _ => throw_error!("type mismatch")
    }
}

fn subst_up(i: usize, r: Inferable, term: Inferable) -> Inferable {
    use self::Inferable::*;
    match term {
        Ann(e, t) => Ann(subst_down(i, r, e), t),
        Bound(j) => if i == j { r } else { Bound(j) },
        Free(y) => Free(y),
        App(box e, e_) => {
            let term = subst_down(i, r.clone(), e_);
            App(Box::new(subst_up(i, r, e)), term)
        },
    }
}

fn subst_down(i: usize, r: Inferable, term: Checkable) -> Checkable {
    use self::Checkable::*;
    match term {
        Inf(box e) => Inf(Box::new(subst_up(i, r, e))),
        Lam(box e) => Lam(Box::new(subst_down(i + 1, r, e))),
    }
}

fn quote_0(value: Value) -> Checkable {
    quote(0, value)
}

fn quote(i: usize, value: Value) -> Checkable {
    match value {
        Value::Lam(f) => Checkable::Lam(Box::new(quote(i + 1, f(vfree(Name::Quote(i)))))),
        Value::Neutral(n) => Checkable::Inf(Box::new(neutral_quote(i, n))),
    }
}

fn neutral_quote(i: usize, neutral: Neutral) -> Inferable {
    match neutral {
        Neutral::Free(x) => boundfree(i, x),
        Neutral::App(box n, box v) => Inferable::App(Box::new(neutral_quote(i, n)), quote(i, v)),
    }
}

fn boundfree(i: usize, name: Name) -> Inferable {
    match name {
        Name::Quote(k) => Inferable::Bound(i - k - 1),
        x => Inferable::Free(x),
    }
}

#[derive(Clone,Debug)]
pub enum Kind {
    Star,
}

#[derive(Clone,Debug)]
pub enum Info {
    HasKind(Kind),
    HasType(Type),
}

pub type Context = VecDeque<(Name, Info)>;

type Result<A> = ::std::result::Result<A, String>;

fn main() {
    use std::io::{self, BufRead, Write};
    /*use self::Inferable::*;
    use self::Checkable::*;
    use self::Name::*;
    use self::Info::*;
    use self::Kind::*;
    let id_ = Lam(Box::new(Inf(Box::new(Bound(0)))));
    let const_ = Lam(Box::new(Lam(Box::new(Inf(Box::new(Bound(1)))))));
    let tfree = |a: &str| Type::Free(Global(a.into()));
    let free = |x: &str| Inf(Box::new(Free(Global(x.into()))));
    let term_1 = App(Box::new(Ann(id_.clone(), Type::Fun(Box::new(tfree("a")), Box::new(tfree("a"))))), free("y"));
    let term_2 = App(Box::new(App(Box::new(Ann(const_, Type::Fun(Box::new(Type::Fun(Box::new(tfree("b")), Box::new(tfree("b")))),
                                                                 Box::new(Type::Fun(Box::new(tfree("a")),
                                                                                    Box::new(Type::Fun(Box::new(tfree("b")), Box::new(tfree("b"))))))))),
                                  id_)),
                     free("y"));
    let mut env_1 = VecDeque::new();
    env_1.push_back((Global("y".into()), HasType(tfree("a"))));
    env_1.push_back((Global("a".into()), HasKind(Star)));
    let mut env_2 = env_1.clone();
    env_2.push_front((Global("b".into()), HasKind(Star)));
    println!("{:?}", quote_0(eval_up(term_1.clone(), VecDeque::new())));
    println!("{:?}", quote_0(eval_up(term_2.clone(), VecDeque::new())));
    println!("{:?}", type_up_0(env_1, term_1));
    println!("{:?}", type_up_0(env_2, term_2));
    //eval_up(Inferable::Free(Name::Global("foo".to_string())), Env::new());

    //println!("{:?}", parse::parse("x : y"));
    //println!("{:?}", parse::parse("x : ( ( y -> y ) ) -> y"));
    //println!("{:?}", parse::parse("fn x -> y : ( ( y -> y ) ) -> y"));
    //println!("{:?}", parse::parse("x y z"));
    //println!("{:?}", parse::parse("( x : ( y -> y ) ) -> y"));
    //println!("{:?}", parser::parse("x y z : y -> y -> y"));
    let mut env = VecDeque::new();
    println!("{:?}", parser::parse("assume (x:y)(z:*)", &mut env));
    println!("{:?}", env);*/
    let mut env = VecDeque::new();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let _ = write!(stdout, "> ");
    stdout.flush();
    for line in stdin.lock().lines() {
        match line {
            Ok(line) => match parser::parse(&line, &mut env) {
                Ok(Some(term)) => {
                    /*match type_up_0(env.clone(), term.clone()) {
                        Ok(ty) => println!("{:?} : {:?}", quote_0(eval_up(term, Env::new())), ty),
                        Err(e) => println!("Type error: {:?} {}", term, e)
                    }*/
                    print!("{:?} : ", quote_0(eval_up(term.clone(), Env::new())));
                    match type_up_0(env.clone(), term) {
                        Ok(ty) => println!("{:?}", ty),
                        Err(e) => println!("Type error: {}", e)
                    }
                },
                Ok(None) => (),
                Err(()) => println!("Parse error.")
            },
            Err(e) => println!("I/O error: {}", e),
        }
        write!(stdout, "> ");
        let _ = stdout.flush();
    }
}
