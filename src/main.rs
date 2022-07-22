use chumsky::prelude::*;
use std::{fmt, rc::Rc};

type Var = String;

#[derive(PartialEq, Eq, Clone)]
enum Term {
    Var(Var),
    Let {
        var: Var,
        term: Rc<Term>,
        body: Rc<Term>,
    },
    Fun {
        var: Var,
        body: Rc<Term>,
    },
    App {
        fun: Rc<Term>,
        val: Rc<Term>,
    },
}

impl Term {
    fn subst(&self, var: &Var, term: Rc<Term>) -> Rc<Term> {
        match self {
            Term::Var(x) => {
                if x == var {
                    term
                } else {
                    Rc::new(self.clone())
                }
            }
            Term::Let {
                var: v,
                term: t,
                body: b,
            } => Rc::new(Term::Let {
                var: v.clone(),
                term: t.subst(var, term.clone()),
                body: b.subst(var, term),
            }),
            Term::Fun { var: v, body: b } => Rc::new(Term::Fun {
                var: v.clone(),
                body: b.subst(var, term),
            }),
            Term::App { fun, val } => Rc::new(Term::App {
                fun: fun.subst(var, term.clone()),
                val: val.subst(var, term),
            }),
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(n) => write!(f, "{n}"),
            Term::Let { var, term, body } => write!(f, "let {var} := {term:?};\n{body:?})"),
            Term::Fun { var, body } => write!(f, "(fun {var}. {body:?})"),
            Term::App { fun, val } => write!(f, "{fun:?} {val:?}"),
        }
    }
}

fn parser() -> impl Parser<char, Term, Error = Simple<char>> {
    recursive(|term| {
        let t = term.clone().padded().map(Rc::new);

        let var = text::ident();
        let fun = just("fun")
            .ignore_then(var.padded())
            .then_ignore(just("."))
            .then(t.clone())
            .map(|(var, body)| Term::Fun { var, body });
        let let_ = just("let")
            .ignore_then(var.padded())
            .then_ignore(just(":="))
            .then(t.clone())
            .then_ignore(just(";"))
            .then(t.clone())
            .map(|((var, term), body)| Term::Let { var, term, body });
        let no_app_term = choice((
            fun,
            let_,
            var.map(Term::Var),
            term.delimited_by(just('('), just(')')),
        ));
        no_app_term
            .repeated()
            .at_least(1)
            .map(|mut v| (v.remove(0), v))
            .foldl(|f, v| Term::App {
                fun: Rc::new(f),
                val: Rc::new(v),
            })
    })
    .padded()
}

fn main() {
    let parser = parser();
    println!("{:?}", parser.parse("fun x. x"))
}
