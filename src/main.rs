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
            // inner variables shadow outer ones
            let_ @ Term::Let { var: v, .. } if var == v => Rc::new(let_.clone()),
            Term::Let {
                var: v,
                term: t,
                body: b,
            } => Rc::new(Term::Let {
                var: v.clone(),
                term: t.subst(var, term.clone()),
                body: b.subst(var, term),
            }),
            // inner variables shadow outer ones
            fun @ Term::Fun { var: v, .. } if var == v => Rc::new(fun.clone()),
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

    fn reduce_once(&self) -> Option<Rc<Term>> {
        match self {
            Term::Var(_) => None,
            Term::Let { var, term, body } => Some(body.subst(var, term.clone())),
            Term::Fun { var, body } => Some(Rc::new(Term::Fun {
                var: var.clone(),
                body: body.reduce_once()?,
            })),
            Term::App { fun, val } => {
                if let Term::Fun { var, body } = fun.as_ref() {
                    Some(body.subst(var, val.clone()))
                } else {
                    (|| {
                        Some(Rc::new(Term::App {
                            fun: fun.reduce_once()?,
                            val: val.clone(),
                        }))
                    })()
                    .or_else(|| {
                        Some(Rc::new(Term::App {
                            fun: fun.clone(),
                            val: val.reduce_once()?,
                        }))
                    })
                }
            }
        }
    }

    fn is_app(&self) -> bool {
        matches!(self, Term::App { .. })
    }

    fn prec(&self) -> u32 {
        // max: 10
        // arg: 9
        // lead: 8
        // min/default: 0
        match self {
            Term::Var(_) => 10,
            Term::Let { .. } => 8,
            Term::Fun { .. } => 8,
            Term::App { .. } => 8,
        }
    }

    fn fmt_pretty(&self, f: &mut fmt::Formatter<'_>, prec: u32) -> fmt::Result {
        if self.prec() < prec {
            write!(f, "(")?
        }
        match self {
            Term::Var(n) => write!(f, "{n}")?,
            Term::Let { var, term, body } => write!(f, "let {var} := {term:?};\n{body:?}")?,
            Term::Fun { var, body } => write!(f, "fun {var}. {body:?}")?,
            Term::App { fun, val } => {
                let fun_prec = if fun.is_app() { 8 } else { 9 };
                fun.fmt_pretty(f, fun_prec)?;
                write!(f, " ")?;
                val.fmt_pretty(f, 9)?
            }
        };
        if self.prec() < prec {
            write!(f, ")")?
        }
        Ok(())
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_pretty(f, 0)
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
            .padded()
            .repeated()
            .at_least(1)
            .map(|mut v| (v.remove(0), v))
            .foldl(|f, v| Term::App {
                fun: Rc::new(f),
                val: Rc::new(v),
            })
    })
    .then_ignore(end())
}

fn main() {
    let parser = parser();
    // let term = parser.parse("(fun f. f f) fun f. f f");
    let term = parser.parse(
        "
        let zero := fun s. fun z. z;
        let succ := fun n. fun s. fun z. s (n s z);
        let add := fun n. fun m. fun s. fun z. n s (m s z);
        add (succ (succ zero)) (zero)
        ",
    );
    println!("{:?}", term);
    let mut term = Rc::new(term.unwrap());
    while let Some(t) = term.reduce_once() {
        term = t;
        println!("reduced:\n{:?}", term)
    }
}
