//! An Earley parser for the grammar of syntax constructors.
//!
//! The grammar has one nonterminal per syntactic type and one production per
//! syntax axiom. A variable in the input is a leaf of its own type. The
//! parser needs no hints and no restriction on the grammar, and it reports
//! an ambiguity as soon as any partial parse can be derived in two ways, so
//! it never does more work than for an unambiguous grammar.
//!
//! That ambiguity test is deliberately loose. Two derivations of a partial
//! parse always witness an ambiguity of the grammar, but not always one of
//! the string being parsed, and an ambiguous grammar is only noticed when
//! some parsed string runs into it.

use std::cell::RefCell;
use std::hash::Hash;
use std::rc::Rc;

use crate::{HashMap, HashSet};

/// A nonterminal, numbered from zero.
pub type Nt = u32;

/// A symbol on the right-hand side of a production.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Sym<T> {
    Const(T),
    Nt(Nt),
}

/// A token of the input: a constant, or a variable of some type with a
/// payload identifying it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token<T, L> {
    Const(T),
    Var(Nt, L),
}

/// A parse tree. The children of a `Node` are the subtrees for the
/// nonterminals on the production's right-hand side, in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tree<L> {
    Leaf(L),
    Node(usize, Vec<Tree<L>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// No parse exists. Parsing got stuck at the token with this index, which
    /// is the number of tokens if the input ended too early.
    NoParse { at: usize },
    /// The tokens in `start..end` begin a parse in more than one way.
    Ambiguous { start: usize, end: usize },
}

#[derive(Debug)]
struct Prod<T> {
    lhs: Nt,
    rhs: Vec<Sym<T>>,
}

/// What the next token can be, for choosing the productions to predict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Look<T> {
    Const(T),
    Var(Nt),
    End,
}

type Predictions<T> = HashMap<(Nt, Look<T>), Rc<[u32]>>;

#[derive(Debug)]
pub struct Grammar<T> {
    prods: Vec<Prod<T>>,
    by_lhs: Vec<Vec<u32>>,
    /// Whether each nonterminal derives the empty string.
    nullable: Vec<bool>,
    /// The tokens each nonterminal can start with.
    first: Vec<HashSet<Look<T>>>,
    /// Productions worth predicting for a nonterminal and a next token.
    predict: RefCell<Predictions<T>>,
}

/// How an item was derived from the item before it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Back<L> {
    /// The dot is at the start.
    Start,
    /// Scanned a constant; the predecessor is in the previous set.
    Scan { pred: u32 },
    /// Scanned a variable; the predecessor is in the previous set.
    Var { pred: u32, leaf: L },
    /// Stepped over a nonterminal completed by item `child` of this set. The
    /// predecessor is item `pred` of set `pset`.
    Complete { pset: u32, pred: u32, child: u32 },
}

#[derive(Clone, Copy, Debug)]
struct Item<L> {
    prod: u32,
    dot: u32,
    origin: u32,
    back: Back<L>,
}

/// The items that end at one position of the input.
struct Set<L> {
    items: Vec<Item<L>>,
    /// Items whose next symbol is a nonterminal, with that nonterminal.
    waiting: Vec<(Nt, u32)>,
    /// Completed items that span no tokens, with their nonterminal.
    empty: Vec<(Nt, u32)>,
    predicted: Vec<Nt>,
}

impl<L: Copy> Set<L> {
    fn new() -> Self {
        Set {
            items: Vec::new(),
            waiting: Vec::new(),
            empty: Vec::new(),
            predicted: Vec::new(),
        }
    }

    /// The items waiting for a nonterminal.
    fn waiting(&self, nt: Nt) -> impl Iterator<Item = (u32, Item<L>)> + '_ {
        self.waiting
            .iter()
            .filter(move |&&(n, _)| n == nt)
            .map(|&(_, w)| (w, self.items[w as usize]))
    }
}

/// How many items to expect in a set. Most sets of a typical grammar are
/// smaller.
const ITEMS_PER_SET: usize = 32;

/// The sets for the positions reached so far.
struct Chart<L> {
    sets: Vec<Set<L>>,
    /// Where each item is in its set, by set, production, dot and origin.
    index: HashMap<(u32, u32, u32, u32), u32>,
}

impl<L: Copy + PartialEq> Chart<L> {
    /// Adds an item to the set numbered `end`. A second, different
    /// derivation of an item is an ambiguity.
    fn add(&mut self, end: usize, item: Item<L>) -> Result<(), ParseError> {
        let set = &mut self.sets[end];
        match self.index.get(&(end as u32, item.prod, item.dot, item.origin)) {
            Some(&i) if set.items[i as usize].back == item.back => Ok(()),
            Some(_) => Err(ParseError::Ambiguous {
                start: item.origin as usize,
                end,
            }),
            None => {
                self.index.insert(
                    (end as u32, item.prod, item.dot, item.origin),
                    set.items.len() as u32,
                );
                set.items.push(item);
                Ok(())
            }
        }
    }
}

impl<T: Copy + Eq + Hash> Grammar<T> {
    /// Builds a grammar with `types` nonterminals from its productions, each
    /// a left-hand side and a right-hand side. Productions are identified by
    /// their index.
    pub fn new(types: usize, productions: Vec<(Nt, Vec<Sym<T>>)>) -> Self {
        let prods: Vec<Prod<T>> = productions
            .into_iter()
            .map(|(lhs, rhs)| Prod { lhs, rhs })
            .collect();
        let mut by_lhs = vec![Vec::new(); types];
        for (i, p) in prods.iter().enumerate() {
            by_lhs[p.lhs as usize].push(i as u32);
        }

        let mut nullable = vec![false; types];
        let mut changed = true;
        while changed {
            changed = false;
            for p in &prods {
                if !nullable[p.lhs as usize]
                    && p.rhs
                        .iter()
                        .all(|s| matches!(*s, Sym::Nt(n) if nullable[n as usize]))
                {
                    nullable[p.lhs as usize] = true;
                    changed = true;
                }
            }
        }

        let mut first: Vec<HashSet<Look<T>>> = (0..types)
            .map(|n| HashSet::from_iter([Look::Var(n as Nt)]))
            .collect();
        changed = true;
        while changed {
            changed = false;
            for p in &prods {
                for s in &p.rhs {
                    match *s {
                        Sym::Const(c) => {
                            changed |= first[p.lhs as usize].insert(Look::Const(c));
                            break;
                        }
                        Sym::Nt(n) => {
                            if n != p.lhs {
                                let add: Vec<Look<T>> = first[n as usize]
                                    .difference(&first[p.lhs as usize])
                                    .copied()
                                    .collect();
                                changed |= !add.is_empty();
                                first[p.lhs as usize].extend(add);
                            }
                            if !nullable[n as usize] {
                                break;
                            }
                        }
                    }
                }
            }
        }

        Grammar {
            prods,
            by_lhs,
            nullable,
            first,
            predict: RefCell::new(HashMap::default()),
        }
    }

    /// Whether a production can derive a string starting with the given
    /// token, or the empty string.
    fn can_start(&self, prod: u32, look: Look<T>) -> bool {
        for s in &self.prods[prod as usize].rhs {
            match *s {
                Sym::Const(c) => return look == Look::Const(c),
                Sym::Nt(n) => {
                    if self.first[n as usize].contains(&look) {
                        return true;
                    }
                    if !self.nullable[n as usize] {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn predictions(&self, nt: Nt, look: Look<T>) -> Rc<[u32]> {
        if let Some(ps) = self.predict.borrow().get(&(nt, look)) {
            return ps.clone();
        }
        let ps: Rc<[u32]> = self.by_lhs[nt as usize]
            .iter()
            .copied()
            .filter(|&p| self.can_start(p, look))
            .collect();
        self.predict.borrow_mut().insert((nt, look), ps.clone());
        ps
    }

    /// Parses the tokens as the nonterminal `start`.
    pub fn parse<L: Copy + PartialEq>(
        &self,
        start: Nt,
        tokens: &[Token<T, L>],
    ) -> Result<Tree<L>, ParseError> {
        // The start production, `START -> start`, has this index.
        let start_prod = self.prods.len() as u32;
        let start_rhs = [Sym::Nt(start)];
        let rhs = |p: u32| -> &[Sym<T>] {
            if p == start_prod {
                &start_rhs
            } else {
                &self.prods[p as usize].rhs
            }
        };

        let n = tokens.len();
        let mut chart = Chart {
            sets: vec![Set::new()],
            // Sized in advance, as growing it costs more than filling it.
            index: HashMap::with_capacity_and_hasher(ITEMS_PER_SET * (n + 1), Default::default()),
        };
        chart.add(
            0,
            Item {
                prod: start_prod,
                dot: 0,
                origin: 0,
                back: Back::Start,
            },
        )?;

        let mut waiting: Vec<(u32, Item<L>)> = Vec::new();
        for j in 0..=n {
            let look = match tokens.get(j) {
                Some(&Token::Const(c)) => Look::Const(c),
                Some(&Token::Var(nt, _)) => Look::Var(nt),
                None => Look::End,
            };
            let mut q = 0;
            while q < chart.sets[j].items.len() {
                let item = chart.sets[j].items[q];
                let r = rhs(item.prod);
                if item.dot as usize == r.len() {
                    // Complete: step every item waiting for this nonterminal
                    // at the origin over it.
                    if item.prod != start_prod {
                        let lhs = self.prods[item.prod as usize].lhs;
                        let k = item.origin as usize;
                        if k == j {
                            // Items that start waiting later find this one
                            // through `empty`.
                            chart.sets[j].empty.push((lhs, q as u32));
                        }
                        waiting.clear();
                        waiting.extend(chart.sets[k].waiting(lhs));
                        for &(w, wi) in &waiting {
                            chart.add(
                                j,
                                Item {
                                    prod: wi.prod,
                                    dot: wi.dot + 1,
                                    origin: wi.origin,
                                    back: Back::Complete {
                                        pset: k as u32,
                                        pred: w,
                                        child: q as u32,
                                    },
                                },
                            )?;
                        }
                    }
                } else if let Sym::Nt(nt) = r[item.dot as usize] {
                    chart.sets[j].waiting.push((nt, q as u32));
                    let mut e = 0;
                    while e < chart.sets[j].empty.len() {
                        let (empty_nt, child) = chart.sets[j].empty[e];
                        e += 1;
                        if empty_nt != nt {
                            continue;
                        }
                        chart.add(
                            j,
                            Item {
                                prod: item.prod,
                                dot: item.dot + 1,
                                origin: item.origin,
                                back: Back::Complete {
                                    pset: j as u32,
                                    pred: q as u32,
                                    child,
                                },
                            },
                        )?;
                    }
                    if !chart.sets[j].predicted.contains(&nt) {
                        chart.sets[j].predicted.push(nt);
                        for &p in self.predictions(nt, look).iter() {
                            chart.add(
                                j,
                                Item {
                                    prod: p,
                                    dot: 0,
                                    origin: j as u32,
                                    back: Back::Start,
                                },
                            )?;
                        }
                    }
                }
                q += 1;
            }

            // Scan.
            let Some(token) = tokens.get(j) else { break };
            chart.sets.push(Set::new());
            for i in 0..chart.sets[j].items.len() {
                let item = chart.sets[j].items[i];
                let Some(sym) = rhs(item.prod).get(item.dot as usize) else {
                    continue;
                };
                let back = match (*sym, *token) {
                    (Sym::Const(a), Token::Const(b)) if a == b => Back::Scan { pred: i as u32 },
                    (Sym::Nt(a), Token::Var(b, leaf)) if a == b => Back::Var {
                        pred: i as u32,
                        leaf,
                    },
                    _ => continue,
                };
                chart.add(
                    j + 1,
                    Item {
                        prod: item.prod,
                        dot: item.dot + 1,
                        origin: item.origin,
                        back,
                    },
                )?;
            }
            if chart.sets[j + 1].items.is_empty() {
                return Err(ParseError::NoParse { at: j });
            }
        }

        match chart.index.get(&(n as u32, start_prod, 1, 0)) {
            Some(&accept) => {
                let Tree::Node(_, mut children) = Self::build(&chart.sets, n, accept as usize)
                else {
                    unreachable!()
                };
                Ok(children.pop().unwrap())
            }
            None => Err(ParseError::NoParse { at: n }),
        }
    }

    /// The tree of the completed item `idx` of set `end`.
    fn build<L: Copy>(sets: &[Set<L>], end: usize, idx: usize) -> Tree<L> {
        let prod = sets[end].items[idx].prod as usize;
        let mut children = Vec::new();
        let (mut j, mut i) = (end, idx);
        loop {
            match sets[j].items[i].back {
                Back::Start => break,
                Back::Scan { pred } => {
                    j -= 1;
                    i = pred as usize;
                }
                Back::Var { pred, leaf } => {
                    children.push(Tree::Leaf(leaf));
                    j -= 1;
                    i = pred as usize;
                }
                Back::Complete { pset, pred, child } => {
                    children.push(Self::build(sets, j, child as usize));
                    j = pset as usize;
                    i = pred as usize;
                }
            }
        }
        children.reverse();
        Tree::Node(prod, children)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type G = Grammar<&'static str>;
    type Tok = Token<&'static str, &'static str>;

    /// Builds a grammar from lines like `class -> suc class`, where the
    /// nonterminals are the names in `types`.
    fn grammar(types: &[&str], prods: &[&'static str]) -> G {
        let nt = |s: &str| types.iter().position(|t| *t == s).map(|i| i as Nt);
        let productions = prods
            .iter()
            .map(|line| {
                let (lhs, rhs) = line.split_once("->").unwrap();
                let rhs = rhs
                    .split_whitespace()
                    .map(|s| nt(s).map_or(Sym::Const(s), Sym::Nt))
                    .collect();
                (nt(lhs.trim()).unwrap(), rhs)
            })
            .collect();
        Grammar::new(types.len(), productions)
    }

    /// Tokenizes a string, where `vars` gives the type of each variable.
    fn tokens(types: &[&str], vars: &[(&'static str, &str)], s: &'static str) -> Vec<Tok> {
        s.split_whitespace()
            .map(|t| match vars.iter().find(|(v, _)| *v == t) {
                Some((v, ty)) => {
                    Token::Var(types.iter().position(|x| x == ty).unwrap() as Nt, *v)
                }
                None => Token::Const(t),
            })
            .collect()
    }

    fn show(t: &Tree<&str>) -> String {
        match t {
            Tree::Leaf(l) => (*l).to_owned(),
            Tree::Node(p, cs) if cs.is_empty() => format!("{p}"),
            Tree::Node(p, cs) => {
                let cs: Vec<String> = cs.iter().map(show).collect();
                format!("({p} {})", cs.join(" "))
            }
        }
    }

    const TYPES: &[&str] = &["wff", "class", "setvar"];
    const VARS: &[(&str, &str)] = &[
        ("ph", "wff"),
        ("ps", "wff"),
        ("A", "class"),
        ("B", "class"),
        ("x", "setvar"),
        ("y", "setvar"),
        ("z", "setvar"),
    ];

    /// A fragment of the grammar of set.mm, with its garden paths.
    const SET: &[&str] = &[
        "wff -> -. wff",                                // 0
        "wff -> ( wff -> wff )",                        // 1
        "wff -> ( wff /\\ wff )",                       // 2
        "wff -> class = class",                         // 3
        "wff -> class e. class",                        // 4
        "wff -> class class class",                     // 5
        "class -> setvar",                              // 6
        "class -> { class }",                           // 7
        "class -> <. class , class >.",                 // 8
        "class -> <. class , class , class >.",         // 9
        "class -> { <. setvar , setvar >. | wff }",     // 10
        "class -> { <. <. setvar , setvar >. , setvar >. | wff }", // 11
        "class -> ( setvar e. class |-> class )",       // 12
        "class -> ( class X. class )",                  // 13
        "class -> ( class class class )",               // 14
        "class -> (/)",                                 // 15
        "class -> suc class",                           // 16
        "wff -> A. setvar wff",                         // 17
    ];

    fn parse(g: &G, start: &str, s: &'static str) -> Result<String, ParseError> {
        let start = TYPES.iter().position(|t| *t == start).unwrap() as Nt;
        g.parse(start, &tokens(TYPES, VARS, s)).map(|t| show(&t))
    }

    #[test]
    fn simple() {
        let g = grammar(TYPES, SET);
        assert_eq!(parse(&g, "wff", "ph").unwrap(), "ph");
        assert_eq!(parse(&g, "wff", "-. ph").unwrap(), "(0 ph)");
        assert_eq!(parse(&g, "wff", "( ph -> -. ps )").unwrap(), "(1 ph (0 ps))");
        assert_eq!(parse(&g, "class", "(/)").unwrap(), "15");
        assert_eq!(parse(&g, "wff", "A = B").unwrap(), "(3 A B)");
    }

    #[test]
    fn type_conversion() {
        let g = grammar(TYPES, SET);
        assert_eq!(parse(&g, "setvar", "x").unwrap(), "x");
        assert_eq!(parse(&g, "class", "x").unwrap(), "(6 x)");
        assert_eq!(parse(&g, "wff", "x = y").unwrap(), "(3 (6 x) (6 y))");
        assert_eq!(parse(&g, "wff", "-. suc suc x e. A").unwrap(), "(0 (4 (16 (16 (6 x))) A))");
        // A class is not a setvar.
        assert_eq!(parse(&g, "wff", "A. A ph"), Err(ParseError::NoParse { at: 1 }));
    }

    #[test]
    fn garden_paths() {
        let g = grammar(TYPES, SET);
        assert_eq!(parse(&g, "class", "( x e. A |-> B )").unwrap(), "(12 x A B)");
        assert_eq!(parse(&g, "wff", "( x e. A /\\ ph )").unwrap(), "(2 (4 (6 x) A) ph)");
        assert_eq!(parse(&g, "class", "( x X. A )").unwrap(), "(13 (6 x) A)");
        assert_eq!(parse(&g, "class", "( x y z )").unwrap(), "(14 (6 x) (6 y) (6 z))");
        assert_eq!(parse(&g, "wff", "( x y z -> ph )").unwrap(), "(1 (5 (6 x) (6 y) (6 z)) ph)");
        assert_eq!(parse(&g, "class", "{ <. x , y >. | ph }").unwrap(), "(10 x y ph)");
        assert_eq!(parse(&g, "class", "{ <. x , y >. }").unwrap(), "(7 (8 (6 x) (6 y)))");
        assert_eq!(parse(&g, "class", "{ <. x , y , z >. }").unwrap(), "(7 (9 (6 x) (6 y) (6 z)))");
        assert_eq!(
            parse(&g, "class", "{ <. <. x , y >. , z >. | ph }").unwrap(),
            "(11 x y z ph)"
        );
        assert_eq!(
            parse(&g, "class", "{ <. <. x , y >. , z >. }").unwrap(),
            "(7 (8 (8 (6 x) (6 y)) (6 z)))"
        );
    }

    /// The shapes that `metamath-rs` gets wrong.
    #[test]
    fn nested_pairs() {
        let g = grammar(TYPES, SET);
        assert_eq!(
            parse(&g, "class", "{ <. <. x , B >. , A >. }").unwrap(),
            "(7 (8 (8 (6 x) B) A))"
        );
        assert_eq!(
            parse(&g, "wff", "A = { <. <. x , B >. , A >. }").unwrap(),
            "(3 A (7 (8 (8 (6 x) B) A)))"
        );
        assert_eq!(
            parse(&g, "class", "{ <. <. x , y , z >. , A >. }").unwrap(),
            "(7 (8 (9 (6 x) (6 y) (6 z)) A))"
        );
        assert_eq!(
            parse(&g, "class", "{ <. <. x , <. y , z >. >. , x >. }").unwrap(),
            "(7 (8 (8 (6 x) (8 (6 y) (6 z))) (6 x)))"
        );
    }

    #[test]
    fn no_parse() {
        let g = grammar(TYPES, SET);
        assert_eq!(parse(&g, "wff", "( ph -> ps"), Err(ParseError::NoParse { at: 4 }));
        assert_eq!(parse(&g, "wff", "( ph -> ps ) )"), Err(ParseError::NoParse { at: 5 }));
        assert_eq!(parse(&g, "wff", ""), Err(ParseError::NoParse { at: 0 }));
        assert_eq!(parse(&g, "wff", "A"), Err(ParseError::NoParse { at: 1 }));
        assert_eq!(parse(&g, "class", "ph"), Err(ParseError::NoParse { at: 0 }));
        assert_eq!(parse(&g, "wff", "( ph \\/ ps )"), Err(ParseError::NoParse { at: 2 }));
        assert_eq!(parse(&g, "wff", "{ <. x , y >. | ph"), Err(ParseError::NoParse { at: 8 }));
        // A wff where a class is needed.
        assert_eq!(parse(&g, "class", "{ x e. A }"), Err(ParseError::NoParse { at: 2 }));
    }

    /// A postfix operator makes `suc (/) !!` ambiguous.
    #[test]
    fn ambiguous_postfix() {
        let mut prods = SET.to_vec();
        prods.push("class -> class !!");
        let g = grammar(TYPES, &prods);
        assert_eq!(parse(&g, "class", "A !!").unwrap(), "(18 A)");
        assert_eq!(parse(&g, "class", "suc A").unwrap(), "(16 A)");
        assert_eq!(
            parse(&g, "wff", "suc (/) !! = (/)"),
            Err(ParseError::Ambiguous { start: 0, end: 3 })
        );
        // Brackets hide it.
        assert_eq!(parse(&g, "class", "{ suc (/) } !!").unwrap(), "(18 (7 (16 15)))");
    }

    #[test]
    fn ambiguous_overlap() {
        let mut prods = SET.to_vec();
        prods.push("class -> suc suc class");
        let g = grammar(TYPES, &prods);
        assert_eq!(parse(&g, "class", "suc A").unwrap(), "(16 A)");
        assert!(matches!(
            parse(&g, "wff", "suc suc x = (/)"),
            Err(ParseError::Ambiguous { .. })
        ));
    }

    #[test]
    fn ambiguous_infix() {
        let g = grammar(&["term"], &["term -> term + term", "term -> 0"]);
        let p = |s| g.parse(0, &tokens(&["term"], &[], s)).map(|t| show(&t));
        assert_eq!(p("0 + 0").unwrap(), "(0 1 1)");
        assert!(matches!(p("0 + 0 + 0"), Err(ParseError::Ambiguous { .. })));
    }

    #[test]
    fn ambiguous_duplicate() {
        let g = grammar(&["term"], &["term -> 0", "term -> 0"]);
        let p = |s| g.parse(0, &tokens(&["term"], &[], s));
        assert!(matches!(p("0"), Err(ParseError::Ambiguous { .. })));
    }

    /// Two types that convert to each other have infinitely many parses.
    #[test]
    fn unit_cycle() {
        let types = &["class", "setvar"];
        let g = grammar(types, &["class -> setvar", "setvar -> class", "class -> suc class"]);
        let vars = &[("x", "setvar"), ("A", "class")];
        let p = |start, s| g.parse(start, &tokens(types, vars, s));
        assert!(matches!(p(0, "x"), Err(ParseError::Ambiguous { .. })));
        assert!(matches!(p(1, "A"), Err(ParseError::Ambiguous { .. })));
        assert!(matches!(p(0, "suc x"), Err(ParseError::Ambiguous { .. })));
    }

    #[test]
    fn left_and_right_recursion() {
        let types = &["list", "item"];
        let g = grammar(
            types,
            &["list -> list , item", "list -> item", "item -> a", "item -> [ list ]"],
        );
        let p = |s| g.parse(0, &tokens(types, &[], s)).map(|t| show(&t));
        assert_eq!(p("a").unwrap(), "(1 2)");
        assert_eq!(p("a , a , a").unwrap(), "(0 (0 (1 2) 2) 2)");
        assert_eq!(p("a , [ a , a ]").unwrap(), "(0 (1 2) (3 (0 (1 2) 2)))");

        let g = grammar(types, &["list -> item , list", "list -> item", "item -> a"]);
        let p = |s| g.parse(0, &tokens(types, &[], s)).map(|t| show(&t));
        assert_eq!(p("a , a , a").unwrap(), "(0 2 (0 2 (1 2)))");
    }

    /// The grammar of the MIU system, where a wff is any string of letters.
    #[test]
    fn nullable() {
        let types = &["wff"];
        let g = grammar(types, &["wff ->", "wff -> wff I", "wff -> wff U", "wff -> M wff"]);
        let vars = &[("x", "wff"), ("y", "wff")];
        let p = |s| g.parse(0, &tokens(types, vars, s)).map(|t| show(&t));
        assert_eq!(p("").unwrap(), "0");
        assert_eq!(p("x I U").unwrap(), "(2 (1 x))");
        assert_eq!(p("I U").unwrap(), "(2 (1 0))");
        // `M I` is `M (I)` or `(M) I`.
        assert!(matches!(p("M I"), Err(ParseError::Ambiguous { .. })));
        assert_eq!(p("x y"), Err(ParseError::NoParse { at: 1 }));
    }

    #[test]
    fn nullable_in_the_middle() {
        let types = &["s", "opt"];
        let g = grammar(types, &["s -> [ opt opt ]", "opt ->", "opt -> a"]);
        let p = |s| g.parse(0, &tokens(types, &[], s)).map(|t| show(&t));
        // Either `opt` could be the empty one.
        assert!(matches!(p("[ a ]"), Err(ParseError::Ambiguous { .. })));
        // The test is loose: this string has one parse, but its prefix `[ a`
        // already has two partial ones, which shows the grammar is ambiguous.
        assert_eq!(p("[ a a ]"), Err(ParseError::Ambiguous { start: 0, end: 2 }));
        assert_eq!(p("[ ]").unwrap(), "(0 1 1)");

        let g = grammar(types, &["s -> [ opt , opt ]", "opt ->", "opt -> a"]);
        let p = |s| g.parse(0, &tokens(types, &[], s)).map(|t| show(&t));
        assert_eq!(p("[ , a ]").unwrap(), "(0 1 2)");
        assert_eq!(p("[ a , ]").unwrap(), "(0 2 1)");
    }

    /// A type with no productions and no variables derives nothing.
    #[test]
    fn empty_type() {
        let types = &["wff", "class"];
        let g = grammar(types, &["wff -> class = class"]);
        let p = |s| g.parse(0, &tokens(types, &[("A", "class")], s)).map(|t| show(&t));
        assert_eq!(p("A = A").unwrap(), "(0 A A)");
        assert_eq!(p("= A"), Err(ParseError::NoParse { at: 0 }));
    }

    /// Deep and long inputs stay fast.
    #[test]
    fn long_input() {
        // The tree is deep, so parse on a thread with a large stack.
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let g = grammar(TYPES, SET);
                let depth = 2000;
                let mut toks: Vec<Tok> = Vec::new();
                for _ in 0..depth {
                    toks.extend(tokens(TYPES, VARS, "( ph ->"));
                }
                toks.extend(tokens(TYPES, VARS, "ps"));
                for _ in 0..depth {
                    toks.extend(tokens(TYPES, VARS, ")"));
                }
                let tree = g.parse(0, &toks).unwrap();
                let mut t = &tree;
                let mut n = 0;
                while let Tree::Node(1, cs) = t {
                    t = &cs[1];
                    n += 1;
                }
                assert_eq!(n, depth);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
