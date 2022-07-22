use std::rc::Rc;

type Var = u32;

#[derive(PartialEq, Eq)]
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
    fn subst(self: Rc<Self>, var: &Var, term: Rc<Term>) -> Rc<Term> {
        match self.as_ref() {
            Term::Var(x) => {
                if x == var {
                    term
                } else {
                    self
                }
            }
            Term::Let {
                var: v,
                term: t,
                body: b,
            } => Rc::new(Term::Let {
                var: v.clone(),
                term: t.clone().subst(var, term.clone()),
                body: b.clone().subst(var, term),
            }),
            Term::Fun { var: v, body: b } => Rc::new(Term::Fun {
                var: v.clone(),
                body: b.clone().subst(var, term),
            }),
            Term::App { fun, val } => Rc::new(Term::App {
                fun: fun.clone().subst(var, term.clone()),
                val: val.clone().subst(var, term),
            }),
        }
    }
}

fn main() {
    println!("Hello, world!");
}
