use chumsky::prelude::*;
use std::{collections::HashMap, fmt, rc::Rc};

#[derive(PartialEq, Eq, Clone)]
enum Term<V> {
    Var(V),
    Let {
        var: V,
        term: Rc<Term<V>>,
        body: Rc<Term<V>>,
    },
    Fun {
        var: V,
        body: Rc<Term<V>>,
    },
    App {
        fun: Rc<Term<V>>,
        val: Rc<Term<V>>,
    },
}

impl<V: Clone + Eq> Term<V> {
    fn subst(&self, var: &V, term: Rc<Term<V>>) -> Rc<Term<V>> {
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

    fn reduce(&self) -> Rc<Self> {
        match self {
            var @ Term::Var(_) => Rc::new(var.clone()),
            Term::Let { var, term, body } => body.subst(var, term.reduce()).reduce(),
            Term::Fun { var, body } => Rc::new(Term::Fun {
                var: var.clone(),
                body: body.reduce(),
            }),
            Term::App { fun, val } => {
                let fun = fun.reduce();
                let val = val.reduce();
                if let Term::Fun { var, body } = fun.as_ref() {
                    body.subst(var, val).reduce()
                } else {
                    Rc::new(Term::App { fun, val })
                }
            }
        }
    }

    fn reduce_once(&self) -> Option<Rc<Self>> {
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
}

impl<V> Term<V> {
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
}

impl<V: fmt::Display> Term<V> {
    fn fmt_pretty(&self, f: &mut fmt::Formatter<'_>, prec: u32) -> fmt::Result {
        if self.prec() < prec {
            write!(f, "(")?
        }
        match self {
            Term::Var(n) => write!(f, "{n}")?,
            Term::Let { var, term, body } => write!(f, "let {var} := {term};\n{body}")?,
            Term::Fun { var, body } => write!(f, "fun {var}. {body}")?,
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

#[derive(PartialEq, Eq, Clone)]
struct Var {
    name: String,
    /// discriminant
    discr: u32,
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.discr == 0 {
            self.name.fmt(f)
        } else {
            write!(f, "{}_{}", self.name, self.discr)
        }
    }
}

impl Term<String> {
    /// returns the name of the variable if it is undefined
    fn make_vars_unique(self) -> Result<Term<Var>, String> {
        fn inner(
            this: Rc<Term<String>>,
            ids: &mut HashMap<String, u32>,
            mut context: HashMap<String, u32>,
        ) -> Result<Rc<Term<Var>>, String> {
            match this.as_ref() {
                Term::Var(name) => Ok(Rc::new(Term::Var(Var {
                    discr: *context.get(name).ok_or(name)?,
                    name: name.clone(),
                }))),
                Term::Let {
                    var: name,
                    term,
                    body,
                } => {
                    let term = inner(term.clone(), ids, context.clone())?;
                    let discr = *ids
                        .entry(name.clone())
                        .and_modify(|id| *id += 1)
                        .or_insert(0);
                    context.insert(name.clone(), discr);
                    Ok(Rc::new(Term::Let {
                        var: Var {
                            name: name.clone(),
                            discr,
                        },
                        term,
                        body: inner(body.clone(), ids, context)?,
                    }))
                }
                Term::Fun { var: name, body } => {
                    let discr = *ids
                        .entry(name.clone())
                        .and_modify(|id| *id += 1)
                        .or_insert(0);
                    context.insert(name.clone(), discr);
                    Ok(Rc::new(Term::Fun {
                        var: Var {
                            name: name.clone(),
                            discr,
                        },
                        body: inner(body.clone(), ids, context)?,
                    }))
                }
                Term::App { fun, val } => Ok(Rc::new(Term::App {
                    fun: inner(fun.clone(), ids, context.clone())?,
                    val: inner(val.clone(), ids, context)?,
                })),
            }
        }
        let mut ids = HashMap::new();
        let context = HashMap::new();
        inner(Rc::new(self), &mut ids, context).map(|t| (*t).clone())
    }
}

impl<V: fmt::Display> fmt::Display for Term<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_pretty(f, 0)
    }
}

fn parser() -> impl Parser<char, Term<String>, Error = Simple<char>> {
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
        let pred := fun n. fun s. fun z. n (fun g. fun h. h (g s)) (fun u. z) fun x. x;
        let add := fun n. fun m. fun s. fun z. n s (m s z);
        let sub := fun n. fun m. m pred n;
        sub ((succ zero)) (succ zero)
        ",
    );
    let term = term.unwrap().make_vars_unique().unwrap();
    println!("{}", term);
    println!("reduced: {}", term.reduce());
    // let mut term = Rc::new(term.unwrap());
    // while let Some(t) = term.reduce_once() {
    //     term = t;
    //     println!("step:\n{:?}", term)
    // }
}
