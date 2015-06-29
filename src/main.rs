#![feature(box_patterns)]
#![feature(str_char)]

//extern crate rusty_lisp;

mod parser;

use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

#[derive(Clone,PartialEq,Debug)]
pub enum Inferable {
    Ann(Checkable, Type),
    Star,
    Pi(Type, Checkable),
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

pub type Type = Checkable;

#[derive(Clone)]
enum Value {
    Lam(Rc<Fn(Value) -> Value>),
    Star,
    Pi(Box<Info>, Rc<Fn(Value) -> Value>),
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
        Star => Value::Star,
        Pi(t, t_) => {
            Value::Pi(Box::new(eval_down(t, d.clone())), Rc::new(move |x| {
                let mut d = d.clone();
                d.push_front(x);
                eval_down(t_.clone(), d)
            }))
        },
        Free(x) => vfree(x),
        Bound(i) => d[i].clone(),
        App(box e, e_) => {
            let e = eval_up(e, d.clone());
            let e_ = eval_down(e_, d);
            vapp(e, e_)
        },
    }
}

fn vapp(value: Value, v: Value) -> Value {
    match value {
        Value::Lam(f) => f(v),
        Value::Neutral(n) => Value::Neutral(Neutral::App(Box::new(n), Box::new(v))),
        _ => panic!("Should only apply Lam and Neutral values!")
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

fn type_up_0(ctx: Context, term: Inferable) -> Result<Info> {
    type_up(0, ctx, term)
}

fn type_up(i: usize, mut ctx: Context, term: Inferable) -> Result<Info> {
    use self::Inferable::*;
    match term {
        Ann(e, p) => {
            try!(type_down(i, ctx.clone(), p.clone(), Value::Star));
            let t = eval_down(p, Env::new());
            try!(type_down(i, ctx, e, t.clone()));
            Ok(t)
        },
        Star => Ok(Value::Star),
        Pi(p, p_) => {
            try!(type_down(i, ctx.clone(), p.clone(), Value::Star));
            let t = eval_down(p, Env::new());
            ctx.push_front((Name::Local(i), t));
            try!(type_down(i + 1, ctx, subst_down(0, Inferable::Free(Name::Local(i)), p_), Value::Star));
            Ok(Value::Star)
        },
        Free(ref x) => match ctx.into_iter().find(|&(ref name, _)| name == x) {
            Some((_, t)) => Ok(t),
            None => throw_error!("unknown identifier"),
        },
        App(box e, e_) => {
            let o = try!(type_up(i, ctx.clone(), e));
            match o {
                Value::Pi(box t, t_) => {
                    try!(type_down(i, ctx, e_.clone(), t));
                    Ok(t_(eval_down(e_, Env::new())))
                },
                _ => throw_error!("illegal application")
            }
        },
        Bound(_) => panic!("Should never see a bound variable here, as this should be taken care of in the type rule for lambda abstraction."),
    }
}

fn type_down(i: usize, mut ctx: Context, term: Checkable, ty: Info) -> Result<()> {
    use self::Checkable::*;
    match (term, ty) {
        (Inf(box e), v) => {
            let v_ = try!(type_up(i, ctx.clone(), e));
            if quote_0(v) != quote_0(v_) { throw_error!("type mismatch"); }
            Ok(())
        },
        (Lam(box e), Value::Pi(box t, t_)) => {
            //let mut ctx = ctx.clone();
            ctx.push_front((Name::Local(i), t));
            type_down(i + 1, ctx, subst_down(0, Inferable::Free(Name::Local(i)), e), t_(vfree(Name::Local(i))))
        },
        _ => throw_error!("type mismatch")
    }
}

fn subst_up(i: usize, r: Inferable, term: Inferable) -> Inferable {
    use self::Inferable::*;
    match term {
        Ann(e, t) => Ann(subst_down(i, r.clone(), e), subst_down(i, r, t)),
        Star => Star,
        Pi(t, t_) => Pi(subst_down(i, r.clone(), t), subst_down(i + 1, r, t_)),
        Bound(j) => if i == j { r } else { Bound(j) },
        Free(y) => Free(y),
        App(box e, e_) => {
            let term = subst_down(i, r.clone(), e_);
            App(Box::new(subst_up(i, r.clone(), e)), term)
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
        Value::Star => Checkable::Inf(Box::new(Inferable::Star)),
        Value::Pi(box v, f) => Checkable::Inf(Box::new(Inferable::Pi(quote(i, v), quote(i + 1, f(vfree(Name::Quote(i))))))),
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

fn global_sub_up(r: &Bindings, term: Inferable) -> Inferable {
    use self::Inferable::*;
    match term {
        Ann(e, t) => Ann(global_sub_down(r, e), global_sub_down(r, t)),
        Star => Star,
        Pi(t, t_) => Pi(global_sub_down(r, t), global_sub_down(r, t_)),
        Bound(j) => Bound(j),
        Free(Name::Global(y)) => match r.get(&y) {
            Some(term) => term.clone(),
            None => Free(Name::Global(y))
        },
        Free(n) => Free(n),
        App(box e, e_) => {
            let term = global_sub_down(r, e_);
            App(Box::new(global_sub_up(r, e)), term)
        },
    }
}

fn global_sub_down(r: &Bindings, term: Checkable) -> Checkable {
    use self::Checkable::*;
    match term {
        Inf(box e) => Inf(Box::new(global_sub_up(r, e))),
        Lam(box e) => Lam(Box::new(global_sub_down(r, e))),
    }
}

fn find_up(i: &Name, term: &Inferable) -> bool {
    use self::Inferable::*;
    match *term {
        Ann(ref e, ref t) => find_down(i, e) || find_down(i, t),
        Star => false,
        Pi(ref t, ref t_) => find_down(i, t) || find_down(i, t_),
        Bound(j) => false,
        Free(ref y) => y == i,
        App(box ref e, ref e_) => find_down(i, e_) || find_up(i, e),
    }
}

fn find_down(i: &Name, term: &Checkable) -> bool {
    use self::Checkable::*;
    match *term {
        Inf(box ref e) => find_up(i, e),
        Lam(box ref e) => find_down(i, e),
    }
}

fn bound_name(term: &Checkable, d: &mut VecDeque<usize>) -> usize {
   let mut x = d.iter().rev().next().map(|&x|x).unwrap_or(d.len()) + 1;
   while find_down(&Name::Global(format!("v{}", x)), term) { x = x + 1; }
   d.push_front(x);
   x
}

#[derive(Clone,Copy)] enum Assoc { Left, Right, }

fn print_up(term: Inferable, mut d: VecDeque<usize>, assoc: Assoc) -> String {
    use self::Inferable::*;
    match term {
        Ann(e, t) => format!("{} : {}", print_down(e, d.clone(), Assoc::Left), print_down(t, d, Assoc::Right)),
        Star => "*".into(),
        Pi(t, t_) => {
            let t = print_down(t, d.clone(), Assoc::Right);
            let x = bound_name(&t_, &mut d);
            match assoc {
                Assoc::Left => format!("(Π (v{} : {}) → {})", x, t, print_down(t_, d, Assoc::Right)),
                Assoc::Right => format!("Π (v{} : {}) → {}", x, t, print_down(t_, d, Assoc::Right)),
            }
        },
        Free(Name::Global(x)) => x,
        Free(n) => panic!("Did not expect {:?} during print_up", n),
        Bound(i) => format!("v{}", d[i]),
        App(box e, e_) => match assoc {
            Assoc::Left => format!("{} {}", print_up(e, d.clone(), Assoc::Left), print_down(e_, d, Assoc::Right)),
            Assoc::Right => format!("({} {})", print_up(e, d.clone(), Assoc::Left), print_down(e_, d, Assoc::Right)),
        },
    }
}

fn print_down(term: Checkable, mut d: VecDeque<usize>, assoc:Assoc) -> String {
    use self::Checkable::*;
    match term {
        Inf(box i) => format!("{}", print_up(i, d, assoc)),
        Lam(box e) => {
            let x = bound_name(&e, &mut d);
            match assoc {
                Assoc::Right => format!("λ v{} → {}", x, print_down(e, d, Assoc::Right)),
                Assoc::Left => format!("(λ v{} → {})", x, print_down(e, d, Assoc::Right)),
            }
        },
    }
}

pub type Info = Value;

pub type Context = VecDeque<(Name, Info)>;

pub type Bindings = HashMap<String, Inferable>;

type Result<A> = ::std::result::Result<A, String>;

fn main() {
    use std::collections::HashMap;
    use std::io::{self, BufRead, Write};
    let mut env = VecDeque::new();

    let mut bindings = HashMap::new();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let _ = write!(stdout, "≫ ");
    let _ = stdout.flush();
    for line in stdin.lock().lines() {
        match line {
            Ok(line) => match parser::parse(&line, &mut env, &mut bindings) {
                Ok(Some(term)) => {
                    match type_up_0(env.clone(), term.clone()) {
                        Ok(ty) => println!("{}", print_up(Inferable::Ann(quote_0(eval_up(term, Env::new())), quote_0(ty)), VecDeque::new(), Assoc::Right)),
                        Err(e) => println!("Type error: {} {}", print_up(term, VecDeque::new(), Assoc::Left), e)
                    }
                },
                Ok(None) => (),
                Err(()) => println!("Parse error.")
            },
            Err(e) => println!("I/O error: {}", e),
        }
        let _ = write!(stdout, "≫ ");
        let _ = stdout.flush();
    }
}
