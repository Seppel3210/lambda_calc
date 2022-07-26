use chumsky::prelude::*;
use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    rc::Rc,
};

#[derive(PartialEq, Clone)]
enum Term<V> {
    Var(V),
    Let {
        var: V,
        term: Rc<Self>,
        body: Rc<Self>,
    },
    Fun {
        var: V,
        var_type: Rc<Self>,
        body: Rc<Self>,
    },
    App {
        fun: Rc<Self>,
        val: Rc<Self>,
    },
    Forall {
        var: Option<V>,
        var_type: Rc<Self>,
        ret_type: Rc<Self>,
    },
    Type,
}

enum TypeError<V> {
    VarNotFound(V),
    Mismatch(Term<V>, Term<V>),
    TypeUntypable,
    NoFunction(Term<V>),
}

impl<V: fmt::Display> fmt::Debug for TypeError<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::VarNotFound(var) => write!(f, "VarNotFound({var})"),
            TypeError::Mismatch(a, b) => f.debug_tuple("Mismatch").field(a).field(b).finish(),
            TypeError::TypeUntypable => write!(f, "TypeUntypable"),
            TypeError::NoFunction(fun) => f.debug_tuple("NoFunction").field(fun).finish(),
        }
    }
}

impl<V: Clone + Eq + Hash> Term<V> {
    fn subst(&self, var: &V, term: Rc<Self>) -> Rc<Self> {
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
            Term::Fun {
                var: v,
                var_type,
                body,
            } => Rc::new(Term::Fun {
                var: v.clone(),
                var_type: var_type.subst(var, term.clone()),
                body: body.subst(var, term),
            }),
            Term::App { fun, val } => Rc::new(Term::App {
                fun: fun.subst(var, term.clone()),
                val: val.subst(var, term),
            }),
            Term::Forall {
                var: v,
                var_type,
                ret_type,
            } => Rc::new(Term::Forall {
                var: v.clone(),
                var_type: var_type.subst(var, term.clone()),
                ret_type: ret_type.subst(var, term),
            }),
            Term::Type => Rc::new(Term::Type),
        }
    }

    fn reduce(&self) -> Rc<Self> {
        match self {
            var @ Term::Var(_) => Rc::new(var.clone()),
            Term::Let { var, term, body } => body.subst(var, term.reduce()).reduce(),
            Term::Fun {
                var,
                var_type,
                body,
            } => Rc::new(Term::Fun {
                var: var.clone(),
                var_type: var_type.clone(),
                body: body.reduce(),
            }),
            Term::App { fun, val } => {
                let fun = fun.reduce();
                let val = val.reduce();
                if let Term::Fun {
                    var,
                    var_type: _,
                    body,
                } = fun.as_ref()
                {
                    body.subst(var, val).reduce()
                } else {
                    Rc::new(Term::App { fun, val })
                }
            }
            Term::Forall {
                var,
                var_type,
                ret_type,
            } => Rc::new(Term::Forall {
                var: var.clone(),
                var_type: var_type.clone(),
                ret_type: ret_type.reduce(),
            }),
            Term::Type => Rc::new(Term::Type),
        }
    }

    fn reduce_once(&self) -> Option<Rc<Self>> {
        match self {
            Term::Var(_) => None,
            Term::Let { var, term, body } => Some(body.subst(var, term.clone())),
            Term::Fun {
                var,
                var_type,
                body,
            } => Some(Rc::new(Term::Fun {
                var: var.clone(),
                var_type: var_type.clone(),
                body: body.reduce_once()?,
            })),
            Term::App { fun, val } => {
                if let Term::Fun {
                    var,
                    var_type: _,
                    body,
                } = fun.as_ref()
                {
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
            Term::Forall {
                var,
                var_type,
                ret_type,
            } => Some(Rc::new(Term::Forall {
                var: var.clone(),
                var_type: var_type.clone(),
                ret_type: ret_type.reduce_once()?,
            })),
            Term::Type => None,
        }
    }

    /// Checks if this `Term` is well typed in the given `context` and returns its type.
    /// The `Term`s in the `context` HashMap have to be types.
    /// Returns `Ok(None)` for the term `Type`
    fn type_(&self, mut context: HashMap<V, Self>) -> Result<Option<Self>, TypeError<V>> {
        match self {
            Term::Var(var) => Ok(Some(
                context
                    .get(var)
                    .ok_or(TypeError::VarNotFound(var.clone()))?
                    .clone(),
            )),
            Term::Let { var, term, body } => {
                context.insert(
                    var.clone(),
                    term.type_(context.clone())?
                        .ok_or(TypeError::TypeUntypable)?,
                );
                body.type_(context)
            }
            Term::Fun {
                var,
                var_type,
                body,
            } => {
                var_type.type_(context.clone())?;
                context.insert(var.clone(), (**var_type).clone());
                Ok(Some(Term::Forall {
                    var: Some(var.clone()),
                    var_type: var_type.clone(),
                    ret_type: Rc::new(body.type_(context)?.ok_or(TypeError::TypeUntypable)?),
                }))
            }

            Term::App { fun, val } => {
                let fun_type = fun
                    .type_(context.clone())?
                    .ok_or(TypeError::NoFunction(Term::Type))?;
                let val_type = val
                    .type_(context.clone())?
                    .ok_or(TypeError::TypeUntypable)?;
                if let Term::Forall {
                    var: _,
                    var_type,
                    ret_type,
                } = fun_type
                {
                    var_type.equiv(&val_type, &mut HashMap::new())?;
                    Ok(Some((*ret_type).clone()))
                } else {
                    Err(TypeError::NoFunction((**fun).clone()))
                }
            }
            Term::Forall {
                var,
                var_type,
                ret_type,
            } => {
                var_type.type_(context.clone())?;
                if let Some(var) = var {
                    context.insert(var.clone(), (**var_type).clone());
                }
                ret_type.type_(context)?;
                Ok(Some(Term::Type))
            }
            Term::Type => Ok(None),
        }
    }

    // check for alpha equivalence
    fn equiv(
        &self,
        other_term: &Self,
        name_mapping: &mut HashMap<V, V>,
    ) -> Result<(), TypeError<V>> {
        let this = self.reduce();
        let other = other_term.reduce();
        let eq = match (self, other.as_ref()) {
            (Term::Var(var_a), Term::Var(var_b)) => {
                let mapped = name_mapping.entry(var_a.clone()).or_insert(var_b.clone());
                mapped == var_b
            }
            (Term::Let { .. }, Term::Let { .. }) => unreachable!("let can always be reduced"),
            (
                Term::Fun {
                    var: var_a,
                    var_type: type_a,
                    body: body_a,
                },
                Term::Fun {
                    var: var_b,
                    var_type: type_b,
                    body: body_b,
                },
            ) => {
                type_a.equiv(type_b, name_mapping).is_ok() && {
                    name_mapping.insert(var_a.clone(), var_b.clone());
                    body_a.equiv(body_b, name_mapping).is_ok()
                }
            }
            (
                Term::App {
                    fun: fun_a,
                    val: val_a,
                },
                Term::App {
                    fun: fun_b,
                    val: val_b,
                },
            ) => {
                fun_a.equiv(fun_b, name_mapping).is_ok() && val_a.equiv(val_b, name_mapping).is_ok()
            }
            (
                Term::Forall {
                    var: var_a,
                    var_type: var_type_a,
                    ret_type: ret_type_a,
                },
                Term::Forall {
                    var: var_b,
                    var_type: var_type_b,
                    ret_type: ret_type_b,
                },
            ) => {
                var_type_a.equiv(var_type_b, name_mapping).is_ok() && {
                    if let (Some(var_a), Some(var_b)) = (var_a, var_b) {
                        name_mapping.insert(var_a.clone(), var_b.clone());
                    }
                    ret_type_a.equiv(ret_type_b, name_mapping).is_ok()
                }
            }
            (Term::Type, Term::Type) => true,
            _ => false,
        };
        if eq {
            Ok(())
        } else {
            Err(TypeError::Mismatch(self.clone(), other_term.clone()))
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
            Term::Forall { .. } => 8,
            Term::Type => 10,
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
            Term::Fun {
                var,
                var_type,
                body,
            } => write!(f, "λ {var} : {var_type}. {body}")?,
            Term::App { fun, val } => {
                let fun_prec = if fun.is_app() { 8 } else { 9 };
                fun.fmt_pretty(f, fun_prec)?;
                write!(f, " ")?;
                val.fmt_pretty(f, 9)?
            }
            Term::Forall {
                var,
                var_type,
                ret_type,
            } => {
                if let Some(var) = var {
                    write!(f, "∀ {var} : {var_type}. {ret_type}")?
                } else {
                    write!(f, "{var_type} -> {ret_type}")?
                }
            }
            Term::Type => write!(f, "Type")?,
        };
        if self.prec() < prec {
            write!(f, ")")?
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
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
    fn make_vars_unique(self, extern_vars: HashSet<String>) -> Result<Term<Var>, String> {
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
                Term::Fun {
                    var: name,
                    var_type,
                    body,
                } => {
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
                        var_type: inner(var_type.clone(), ids, context.clone())?,
                        body: inner(body.clone(), ids, context)?,
                    }))
                }
                Term::App { fun, val } => Ok(Rc::new(Term::App {
                    fun: inner(fun.clone(), ids, context.clone())?,
                    val: inner(val.clone(), ids, context)?,
                })),
                Term::Forall {
                    var,
                    var_type,
                    ret_type,
                } => {
                    if let Some(name) = var {
                        let discr = *ids
                            .entry(name.clone())
                            .and_modify(|id| *id += 1)
                            .or_insert(0);
                        context.insert(name.clone(), discr);
                        Ok(Rc::new(Term::Forall {
                            var: Some(Var {
                                name: name.clone(),
                                discr,
                            }),
                            var_type: inner(var_type.clone(), ids, context.clone())?,
                            ret_type: inner(ret_type.clone(), ids, context)?,
                        }))
                    } else {
                        Ok(Rc::new(Term::Forall {
                            var: None,
                            var_type: inner(var_type.clone(), ids, context.clone())?,
                            ret_type: inner(ret_type.clone(), ids, context)?,
                        }))
                    }
                }
                Term::Type => Ok(Rc::new(Term::Type)),
            }
        }
        let mut ids = HashMap::new();
        let context = extern_vars.into_iter().map(|var| (var, 0)).collect();
        inner(Rc::new(self), &mut ids, context).map(|t| (*t).clone())
    }
}

impl<V: fmt::Display> fmt::Display for Term<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_pretty(f, 0)
    }
}

impl<V: fmt::Display> fmt::Debug for Term<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

fn parser() -> impl Parser<char, Term<String>, Error = Simple<char>> {
    recursive(|term| {
        let t = term.clone().padded().map(Rc::new);

        let var = text::ident();
        let fun = just("fun")
            .ignore_then(var.padded())
            .then_ignore(just(":"))
            .then(t.clone())
            .then_ignore(just("."))
            .then(t.clone())
            .map(|((var, var_type), body)| Term::Fun {
                var,
                var_type,
                body,
            });
        let forall = just("forall")
            .ignore_then(var.padded())
            .then_ignore(just(":"))
            .then(t.clone())
            .then_ignore(just("."))
            .then(t.clone())
            .map(|((var, var_type), ret_type)| Term::Forall {
                var: Some(var),
                var_type,
                ret_type,
            });
        let let_ = just("let")
            .ignore_then(var.padded())
            .then_ignore(just(":="))
            .then(t.clone())
            .then_ignore(just(";"))
            .then(t.clone())
            .map(|((var, term), body)| Term::Let { var, term, body });
        let no_app_term = choice((
            just("Type").to(Term::Type),
            fun,
            forall,
            let_,
            var.map(Term::Var),
            term.delimited_by(just('('), just(')')),
        ));
        let app = no_app_term
            .padded()
            .repeated()
            .at_least(1)
            .map(|mut v| (v.remove(0), v))
            .foldl(|f, v| Term::App {
                fun: Rc::new(f),
                val: Rc::new(v),
            });
        let arrow = app
            .clone()
            .map(Rc::new)
            .then_ignore(just("->"))
            .then(t.clone())
            .map(|(var_type, ret_type)| Term::Forall {
                var: None,
                var_type,
                ret_type,
            });
        arrow.or(app)
    })
    .then_ignore(end())
}

fn main() {
    let parser = parser();
    // impossible to make this term type-check
    //let term = parser.parse("(fun f : Type -> Type. f f) fun f: Type. f f");
    let term = parser.parse(
        "
        forall T : Type. T -> T
        ",
    );
    let term = term.unwrap().make_vars_unique([].into()).unwrap();
    println!("{}", term);
    if let Err(err) = term.type_(HashMap::new()) {
        println!("Error: {err:?}");
    } else {
        println!("reduced: {}", term.reduce());
    }
    // let mut term = Rc::new(term.unwrap());
    // while let Some(t) = term.reduce_once() {
    //     term = t;
    //     println!("step:\n{:?}", term)
    // }
}
