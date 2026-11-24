//! Parse trees of math strings.

use std::collections::HashMap;

use metamath_rs::{Label, Symbol};

/// A parse tree. Variables are identified by the label of their `$f`
/// statement, constructors by the label of their syntax axiom. The arguments
/// of a constructor are in the order its variables first appear in the
/// syntax axiom.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(Label),
    App(Label, Vec<Expr>),
}

impl Expr {
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

/// A parse tree in which some variables are holes, to be matched against a
/// tree.
#[derive(Clone, Debug)]
pub enum Pattern {
    Var(Label),
    Hole(usize),
    App(Label, Vec<Pattern>),
}

impl Pattern {
    /// Matches a tree against the pattern. Every occurrence of a hole must
    /// match the same subtree, which is recorded in `holes`.
    pub fn matches<'a>(&self, e: &'a Expr, holes: &mut [Option<&'a Expr>]) -> bool {
        match (self, e) {
            (Pattern::Hole(h), _) => match holes[*h] {
                Some(prev) => prev == e,
                None => {
                    holes[*h] = Some(e);
                    true
                }
            },
            (Pattern::Var(a), Expr::Var(b)) => a == b,
            (Pattern::App(a, ps), Expr::App(b, es)) => {
                a == b && ps.len() == es.len() && ps.iter().zip(es).all(|(p, e)| p.matches(e, holes))
            }
            _ => false,
        }
    }
}

/// A token of a syntax axiom's math string, after the typecode.
#[derive(Clone, Copy, Debug)]
pub enum TemplateTok {
    Const(Symbol),
    /// The n-th distinct variable of the syntax axiom, in order of appearance,
    /// which is also the n-th argument of the parse tree node.
    Arg(usize),
}

/// A term of a `Store`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TermId(u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    Var(Label),
    App(Label, Box<[TermId]>),
}

/// A store of parse trees in which equal trees are the same term, so that
/// the trees of a proof's steps can share their subtrees and be compared in
/// constant time.
#[derive(Debug, Default)]
pub struct Store {
    nodes: Vec<Node>,
    index: HashMap<Node, TermId>,
}

impl Store {
    fn intern(&mut self, node: Node) -> TermId {
        if let Some(&id) = self.index.get(&node) {
            return id;
        }
        let id = TermId(self.nodes.len() as u32);
        self.nodes.push(node.clone());
        self.index.insert(node, id);
        id
    }

    pub fn var(&mut self, label: Label) -> TermId {
        self.intern(Node::Var(label))
    }

    pub fn app(&mut self, label: Label, args: Vec<TermId>) -> TermId {
        self.intern(Node::App(label, args.into_boxed_slice()))
    }

    pub fn add(&mut self, e: &Expr) -> TermId {
        match e {
            Expr::Var(label) => self.var(*label),
            Expr::App(label, args) => {
                let args = args.iter().map(|a| self.add(a)).collect();
                self.app(*label, args)
            }
        }
    }

    pub fn expr(&self, t: TermId) -> Expr {
        match &self.nodes[t.0 as usize] {
            Node::Var(label) => Expr::Var(*label),
            Node::App(label, args) => Expr::App(*label, args.iter().map(|&a| self.expr(a)).collect()),
        }
    }

    /// Replaces the variables of a term. Variables missing from the
    /// substitution are kept.
    pub fn subst(&mut self, t: TermId, subst: &HashMap<Label, TermId>) -> TermId {
        match self.nodes[t.0 as usize].clone() {
            Node::Var(label) => subst.get(&label).copied().unwrap_or(t),
            Node::App(label, args) => {
                let args = args.iter().map(|&a| self.subst(a, subst)).collect();
                self.app(label, args)
            }
        }
    }

    /// A point to which the store can be rolled back.
    pub fn mark(&self) -> usize {
        self.nodes.len()
    }

    /// Forgets every term added since the mark was taken.
    pub fn reset(&mut self, mark: usize) {
        for node in self.nodes.drain(mark..) {
            self.index.remove(&node);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use metamath_rs::database::{Database, DbOptions};

    /// Labels to build trees from.
    fn labels<const N: usize>(names: [&str; N]) -> [Label; N] {
        let text: String = names.iter().map(|n| format!("{n} $a c $.\n")).collect();
        // Atoms are only assigned in incremental mode.
        let mut db = Database::new(DbOptions { incremental: true, ..DbOptions::default() });
        db.parse("test.mm".into(), vec![("test.mm".into(), format!("$c c $.\n{text}").into_bytes())]);
        let nset = db.name_pass().clone();
        names.map(|n| nset.lookup_label(n.as_bytes()).unwrap().atom)
    }

    fn app(label: Label, args: &[Expr]) -> Expr {
        Expr::App(label, args.to_vec())
    }

    #[test]
    fn store_shares_equal_terms() {
        let [f, g, x, y] = labels(["f", "g", "x", "y"]);
        let mut store = Store::default();
        let e = app(f, &[app(g, &[Expr::Var(x)]), Expr::Var(y)]);
        let a = store.add(&e);
        let b = store.add(&e);
        assert_eq!(a, b);
        assert_eq!(store.expr(a), e);
        let vx = store.var(x);
        let gx = store.app(g, vec![vx]);
        assert_eq!(gx, store.add(&app(g, &[Expr::Var(x)])));
        assert_ne!(gx, store.add(&app(g, &[Expr::Var(y)])));
        assert_ne!(gx, store.add(&app(f, &[Expr::Var(x)])));
        // A constructor with no arguments is not a variable.
        assert_ne!(store.var(x), store.app(x, vec![]));
    }

    #[test]
    fn store_substitutes() {
        let [f, g, x, y, z] = labels(["f", "g", "x", "y", "z"]);
        let mut store = Store::default();
        let t = store.add(&app(f, &[Expr::Var(x), app(g, &[Expr::Var(x), Expr::Var(y)])]));
        let gz = store.add(&app(g, &[Expr::Var(z)]));
        // Simultaneous: the `x` substituted for `y` is not replaced again.
        let vx = store.var(x);
        let subst = HashMap::from([(x, gz), (y, vx)]);
        let r = store.subst(t, &subst);
        let gz = app(g, &[Expr::Var(z)]);
        assert_eq!(store.expr(r), app(f, &[gz.clone(), app(g, &[gz, Expr::Var(x)])]));
        // Variables that are not substituted are kept.
        assert_eq!(store.subst(t, &HashMap::new()), t);
    }

    #[test]
    fn store_resets() {
        let [f, x, y] = labels(["f", "x", "y"]);
        let mut store = Store::default();
        let kept = store.add(&app(f, &[Expr::Var(x)]));
        let mark = store.mark();
        let dropped = store.add(&app(f, &[Expr::Var(y)]));
        store.reset(mark);
        assert_eq!(store.mark(), mark);
        assert_eq!(store.add(&app(f, &[Expr::Var(x)])), kept);
        // The dropped term is built again, in the same place.
        assert_eq!(store.add(&app(f, &[Expr::Var(y)])), dropped);
        assert_eq!(store.expr(dropped), app(f, &[Expr::Var(y)]));
    }

    #[test]
    fn pattern_matches() {
        let [f, g, x, y, z] = labels(["f", "g", "x", "y", "z"]);
        // f(?0, g(?0, ?1), x)
        let p = Pattern::App(
            f,
            vec![
                Pattern::Hole(0),
                Pattern::App(g, vec![Pattern::Hole(0), Pattern::Hole(1)]),
                Pattern::Var(x),
            ],
        );
        let e = |a: Expr, b: Expr, c: Expr, d: Expr| app(f, &[a, app(g, &[b, c]), d]);
        let (vx, vy, vz) = (Expr::Var(x), Expr::Var(y), Expr::Var(z));

        let t = e(vy.clone(), vy.clone(), vz.clone(), vx.clone());
        let mut holes = [None, None];
        assert!(p.matches(&t, &mut holes));
        assert_eq!(holes, [Some(&vy), Some(&vz)]);

        // A hole can match any subtree, and two holes the same one.
        let gy = app(g, std::slice::from_ref(&vy));
        let t = e(gy.clone(), gy.clone(), gy.clone(), vx.clone());
        let mut holes = [None, None];
        assert!(p.matches(&t, &mut holes));
        assert_eq!(holes, [Some(&gy), Some(&gy)]);

        // The occurrences of a hole must agree.
        assert!(!p.matches(&e(vy.clone(), vz.clone(), vz.clone(), vx.clone()), &mut [None, None]));
        // Variables and constructors must be the same.
        assert!(!p.matches(&e(vy.clone(), vy.clone(), vz.clone(), vy.clone()), &mut [None, None]));
        assert!(!p.matches(&app(g, &[vy.clone(), vy.clone(), vx.clone()]), &mut [None, None]));
        assert!(!p.matches(&vx, &mut [None, None]));
    }
}
