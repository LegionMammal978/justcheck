//! Parse trees of math strings, built from `metamath-rs` formulas.

use metamath_rs::{Formula, Label, Symbol};

/// A parse tree. Variables are identified by the label of their `$f`
/// statement, constructors by the label of their syntax axiom.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(Label),
    App(Label, Vec<Expr>),
}

impl Expr {
    /// Converts a formula, given the arity of each syntax axiom. Returns `None`
    /// if a label has no known arity or the formula is malformed.
    pub fn from_formula(f: &Formula, arity: &impl Fn(Label) -> Option<usize>) -> Option<Expr> {
        fn build(
            it: &mut impl Iterator<Item = (Label, bool)>,
            arity: &impl Fn(Label) -> Option<usize>,
        ) -> Option<Expr> {
            let (label, is_var) = it.next()?;
            if is_var {
                return Some(Expr::Var(label));
            }
            let args = (0..arity(label)?)
                .map(|_| build(it, arity))
                .collect::<Option<_>>()?;
            Some(Expr::App(label, args))
        }
        let mut it = f.labels_iter();
        let e = build(&mut it, arity)?;
        it.next().is_none().then_some(e)
    }

    /// Calls `f` on every constructor application, in pre-order.
    pub fn for_each_app<'a>(&'a self, f: &mut impl FnMut(Label, &'a [Expr])) {
        if let Expr::App(label, args) = self {
            f(*label, args);
            for arg in args {
                arg.for_each_app(f);
            }
        }
    }

    /// Calls `f` on every variable occurrence.
    pub fn for_each_var(&self, f: &mut impl FnMut(Label)) {
        match self {
            Expr::Var(label) => f(*label),
            Expr::App(_, args) => args.iter().for_each(|arg| arg.for_each_var(f)),
        }
    }
}

/// A token of a flattened math string. A `Hole` stands for a variable that is
/// not yet known.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tok {
    Sym(Symbol),
    Hole(usize),
}

/// A token of a syntax axiom's math string, after the typecode.
#[derive(Clone, Copy, Debug)]
pub enum TemplateTok {
    Const(Symbol),
    /// The n-th distinct variable of the syntax axiom, in order of appearance,
    /// which is also the n-th argument of the parse tree node.
    Arg(usize),
}
