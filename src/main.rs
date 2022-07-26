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
        var_type: Option<Rc<Self>>,
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
    /// reduce a term in a given value context
    /// assumes well-typed term
    fn reduce(&self, mut context: HashMap<V, Rc<Self>>) -> Rc<Self> {
        match self {
            var @ Term::Var(id) => context
                .get(id)
                .cloned()
                .unwrap_or_else(|| Rc::new(var.clone())),
            Term::Let {
                var,
                var_type: _,
                term,
                body,
            } => {
                context.insert(var.clone(), term.reduce(context.clone()));
                body.reduce(context)
            }
            Term::Fun {
                var,
                var_type,
                body,
            } => Rc::new(Term::Fun {
                var: var.clone(),
                var_type: var_type.reduce(context.clone()),
                body: body.reduce(context),
            }),
            Term::App { fun, val } => {
                let fun = fun.reduce(context.clone());
                let val = val.reduce(context.clone());
                if let Term::Fun {
                    var,
                    var_type: _,
                    body,
                } = fun.as_ref()
                {
                    context.insert(var.clone(), val);
                    body.reduce(context)
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
                var_type: var_type.reduce(context.clone()),
                ret_type: ret_type.reduce(context),
            }),
            Term::Type => Rc::new(Term::Type),
        }
    }

    /// Checks if this `Term` is well typed in the given `context` and returns its type.
    /// The `Term`s in the `context` HashMap have to be types.
    /// Returns `Ok(None)` for the term `Type`
    fn type_(&self, type_context: HashMap<V, Self>) -> Result<Option<Self>, TypeError<V>> {
        fn type_<V: Clone + Eq + Hash>(
            this: &Term<V>,
            mut type_context: HashMap<V, Term<V>>,
            mut value_context: HashMap<V, Rc<Term<V>>>,
        ) -> Result<Option<Term<V>>, TypeError<V>> {
            match this {
                Term::Var(var) => Ok(Some(
                    type_context
                        .get(var)
                        .ok_or(TypeError::VarNotFound(var.clone()))?
                        .clone(),
                )),
                Term::Let {
                    var,
                    var_type,
                    term,
                    body,
                } => {
                    let term_type = type_(&term, type_context.clone(), value_context.clone())?
                        .ok_or(TypeError::TypeUntypable)?;
                    if let Some(var_type) = var_type {
                        type_(&var_type, type_context.clone(), value_context.clone())?;
                        term_type.equiv(var_type, value_context.clone())?;
                    }

                    type_context.insert(var.clone(), term_type);
                    value_context.insert(var.clone(), term.clone());
                    type_(&body, type_context, value_context)
                }
                Term::Fun {
                    var,
                    var_type,
                    body,
                } => {
                    type_(&var_type, type_context.clone(), value_context.clone())?;
                    type_context.insert(var.clone(), (**var_type).clone());
                    Ok(Some(Term::Forall {
                        var: Some(var.clone()),
                        var_type: var_type.clone(),
                        ret_type: Rc::new(
                            type_(&body, type_context, value_context)?
                                .ok_or(TypeError::TypeUntypable)?,
                        ),
                    }))
                }

                Term::App { fun, val } => {
                    let fun_type = type_(&fun, type_context.clone(), value_context.clone())?
                        .ok_or(TypeError::NoFunction(Term::Type))?;
                    let val_type = type_(&val, type_context.clone(), value_context.clone())?
                        .ok_or(TypeError::TypeUntypable)?;
                    if let Term::Forall {
                        var,
                        var_type,
                        ret_type,
                    } = fun_type
                    {
                        var_type.equiv(&val_type, value_context.clone())?;
                        if let Some(var) = var {
                            let reduce_ctx = HashMap::from([(var, val.clone())]);
                            Ok(Some((*ret_type.reduce(reduce_ctx)).clone()))
                        } else {
                            Ok(Some((*ret_type).clone()))
                        }
                    } else {
                        Err(TypeError::NoFunction((**fun).clone()))
                    }
                }
                Term::Forall {
                    var,
                    var_type,
                    ret_type,
                } => {
                    type_(&var_type, type_context.clone(), value_context.clone())?;
                    if let Some(var) = var {
                        type_context.insert(var.clone(), (**var_type).clone());
                    }
                    type_(&ret_type, type_context, value_context)?;
                    Ok(Some(Term::Type))
                }
                Term::Type => Ok(None),
            }
        }
        type_(self, type_context, HashMap::new())
    }

    // check for alpha equivalence in a given Context
    fn equiv(&self, other_term: &Self, context: HashMap<V, Rc<Self>>) -> Result<(), TypeError<V>> {
        fn equiv<V: Clone + Eq + Hash>(
            this_term: &Term<V>,
            other_term: &Term<V>,
            context: HashMap<V, Rc<Term<V>>>,
            name_mapping: &mut HashMap<V, V>,
        ) -> Result<(), TypeError<V>> {
            let this = this_term.reduce(context.clone());
            let other = other_term.reduce(context.clone());
            let eq = match (this.as_ref(), other.as_ref()) {
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
                    equiv(&type_a, type_b, context.clone(), name_mapping).is_ok() && {
                        name_mapping.insert(var_a.clone(), var_b.clone());
                        equiv(&body_a, body_b, context, name_mapping).is_ok()
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
                    equiv(&fun_a, fun_b, context.clone(), name_mapping).is_ok()
                        && equiv(&val_a, val_b, context, name_mapping).is_ok()
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
                    equiv(&var_type_a, var_type_b, context.clone(), name_mapping).is_ok() && {
                        if let (Some(var_a), Some(var_b)) = (var_a, var_b) {
                            name_mapping.insert(var_a.clone(), var_b.clone());
                        }
                        equiv(&ret_type_a, ret_type_b, context, name_mapping).is_ok()
                    }
                }
                (Term::Type, Term::Type) => true,
                _ => false,
            };
            if eq {
                Ok(())
            } else {
                Err(TypeError::Mismatch(this_term.clone(), other_term.clone()))
            }
        }
        equiv(self, other_term, context, &mut HashMap::new())
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
            Term::Let {
                var,
                var_type,
                term,
                body,
            } => {
                if let Some(var_type) = var_type {
                    write!(f, "let {var} : {var_type} :=\n\t{term};\n{body}")?
                } else {
                    write!(f, "let {var} := {term};\n{body}")?
                }
            }
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
                    var_type.fmt_pretty(f, 9)?;
                    write!(f, " -> {ret_type}")?
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

const SHOW_DISCRIMINANT: bool = false;

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if SHOW_DISCRIMINANT && self.discr != 0 {
            write!(f, "{}_{}", self.name, self.discr)
        } else {
            self.name.fmt(f)
        }
    }
}

impl Term<String> {
    /// returns the name of the variable if it is undefined
    fn make_vars_unique(self, extern_vars: HashSet<String>) -> Result<Term<Var>, String> {
        fn mk_unique(
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
                    var_type,
                    term,
                    body,
                } => {
                    let term = mk_unique(term.clone(), ids, context.clone())?;
                    let var_type = match var_type {
                        Some(var_type) => Some(mk_unique(var_type.clone(), ids, context.clone())?),
                        None => None,
                    };
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
                        var_type,
                        term,
                        body: mk_unique(body.clone(), ids, context)?,
                    }))
                }
                Term::Fun {
                    var: name,
                    var_type,
                    body,
                } => {
                    let var_type = mk_unique(var_type.clone(), ids, context.clone())?;
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
                        var_type,
                        body: mk_unique(body.clone(), ids, context)?,
                    }))
                }
                Term::App { fun, val } => Ok(Rc::new(Term::App {
                    fun: mk_unique(fun.clone(), ids, context.clone())?,
                    val: mk_unique(val.clone(), ids, context)?,
                })),
                Term::Forall {
                    var,
                    var_type,
                    ret_type,
                } => {
                    if let Some(name) = var {
                        let var_type = mk_unique(var_type.clone(), ids, context.clone())?;
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
                            var_type,
                            ret_type: mk_unique(ret_type.clone(), ids, context)?,
                        }))
                    } else {
                        Ok(Rc::new(Term::Forall {
                            var: None,
                            var_type: mk_unique(var_type.clone(), ids, context.clone())?,
                            ret_type: mk_unique(ret_type.clone(), ids, context)?,
                        }))
                    }
                }
                Term::Type => Ok(Rc::new(Term::Type)),
            }
        }
        let mut ids = HashMap::new();
        let context = extern_vars.into_iter().map(|var| (var, 0)).collect();
        mk_unique(Rc::new(self), &mut ids, context).map(|t| (*t).clone())
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
            .then(just(":").ignore_then(t.clone()).or_not())
            .then_ignore(just(":="))
            .then(t.clone())
            .then_ignore(just(";"))
            .then(t.clone())
            .map(|(((var, var_type), term), body)| Term::Let {
                var,
                var_type,
                term,
                body,
            });
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
        let id : forall T : Type. T -> T := fun T : Type. fun x : T. x;
        let and : forall A : Type. forall B : Type. Type :=
            fun A : Type. fun B : Type. forall X : Type. (A -> B -> X) -> X;
        let mk_and := fun A : Type. fun B : Type. fun a : A. fun b : B.
            fun X : Type. fun f : A -> B -> X. f a b;
        let iff : forall A : Type. forall B : Type. Type :=
            fun A : Type. fun B : Type. and (A -> B) (B -> A);
        let iff_refl : forall A : Type. iff A A := fun A : Type. mk_and (A -> A) (A -> A) (id A) (id A);
        iff_refl
        ",
    );
    let term = term.unwrap().make_vars_unique([].into()).unwrap();
    println!("{}", term);
    match term.type_(HashMap::new()) {
        Err(err) => println!("Error: {err:?}"),
        Ok(type_) => {
            println!("reduced: {}", term.reduce([].into()));
            println!("type: {type_:?}");
        }
    }
    // let mut term = Rc::new(term.unwrap());
    // while let Some(t) = term.reduce_once() {
    //     term = t;
    //     println!("step:\n{:?}", term)
    // }
}
