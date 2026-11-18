//! The definition rules of `README.md`.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use metamath_rs::nameck::Nameset;
use metamath_rs::proof::ProofTreeArray;
use metamath_rs::scopeck::{Frame, Hyp};
use metamath_rs::statement::{CommandToken, StatementAddress, SymbolType};
use metamath_rs::{Database, Formula, Label, StatementRef, StatementType, Symbol, as_str};

use crate::expr::{Expr, TemplateTok, Tok};
use crate::pattern::Pattern;

/// A problem found by the checker.
#[derive(Debug)]
pub struct Diag {
    /// Database position of the statement the problem is reported on.
    pub pos: u32,
    /// Label of that statement, or a description if it has none.
    pub label: String,
    /// The rule violated, if any.
    pub rule: Option<u8>,
    pub msg: String,
    pub warning: bool,
}

#[derive(Debug)]
struct SyntaxAxiom {
    addr: StatementAddress,
    name: String,
    typecode: Symbol,
    template: Vec<TemplateTok>,
    arity: usize,
    /// Variables that occur more than once in the math string.
    repeated_vars: Vec<String>,
}

#[derive(Debug)]
struct Expansion {
    /// `$f` labels of the LHS variables, in argument order.
    lhs_vars: Vec<Label>,
    rhs: Expr,
    /// `$f` labels of the hidden variables.
    hidden: Vec<Label>,
}

/// Everything learned from a definition axiom that later checks need.
#[derive(Debug, Clone, Copy)]
struct DefAxiom {
    /// Index of the associated constructor in `Checker::syntax`.
    constructor: Option<usize>,
    /// Whether the rules are enforced for this axiom and its justified
    /// theorems.
    enforced: bool,
}

pub struct Checker<'a> {
    db: &'a Database,
    nset: &'a Nameset,
    /// Position of every statement in database order.
    pos: HashMap<StatementAddress, u32>,
    var_types: HashSet<Symbol>,
    bound_types: HashSet<Symbol>,
    /// `$f` label to (variable, typecode).
    floats: HashMap<Label, (Symbol, Symbol)>,
    /// Syntax axioms in database order.
    syntax: Vec<SyntaxAxiom>,
    syntax_index: HashMap<Label, usize>,
    primitive: Vec<bool>,
    /// `$j definition` targets of each syntax axiom, with the position of the
    /// `$j` comment.
    jdefs: Vec<Vec<(u32, Vec<u8>)>>,
    /// Constructors contained in each assertion, sorted.
    contains: HashMap<StatementAddress, Box<[usize]>>,
    unparsed: HashSet<StatementAddress>,
    defs: HashMap<StatementAddress, DefAxiom>,
    expansions: Vec<Option<Expansion>>,
    /// Whether each constructor has exactly one associated definition, and
    /// it is enforced.
    enforced: Vec<bool>,
    /// Position of each constructor's associated definition, which orders
    /// the defined constructors.
    rank: Vec<Option<u32>>,
    diags: Vec<Diag>,
}

impl<'a> Checker<'a> {
    /// Prepares a checker. The database must have run the name, scope, grammar
    /// and statement parse passes.
    pub fn new(db: &'a Database) -> Self {
        let nset = &**db.name_result();
        let mut checker = Checker {
            db,
            nset,
            pos: HashMap::new(),
            var_types: HashSet::new(),
            bound_types: HashSet::new(),
            floats: HashMap::new(),
            syntax: Vec::new(),
            syntax_index: HashMap::new(),
            primitive: Vec::new(),
            jdefs: Vec::new(),
            contains: HashMap::new(),
            unparsed: HashSet::new(),
            defs: HashMap::new(),
            expansions: Vec::new(),
            enforced: Vec::new(),
            rank: Vec::new(),
            diags: Vec::new(),
        };
        for (i, sref) in db.statements().enumerate() {
            checker.pos.insert(sref.address(), i as u32);
            if sref.statement_type() == StatementType::Floating {
                let (Some(tc), Some(var), Some(label)) = (
                    checker.symbol(&sref.math_at(0)),
                    checker.symbol(&sref.math_at(1)),
                    checker.label_atom(sref.label()),
                ) else {
                    continue;
                };
                checker.var_types.insert(tc);
                checker.floats.insert(label, (var, tc));
            }
        }
        checker
    }

    /// Position of a labelled statement, for resolving pattern ranges.
    pub fn label_pos(&self, label: &[u8]) -> Option<u32> {
        let addr = self.nset.lookup_label(label)?.address;
        self.pos.get(&addr).copied()
    }

    /// Runs every check. The definition axioms are the `$a` statements
    /// matched by `defs` and not by `exclude`; the rules specific to a
    /// definition axiom are enforced for those also matched by `include`.
    pub fn run(mut self, defs: &Pattern, include: &Pattern, exclude: &Pattern) -> Vec<Diag> {
        self.collect_syntax();
        self.read_j_commands();
        self.collect_contains();
        self.check_syntax();
        self.check_dv();
        self.check_definitions(defs, include, exclude);
        self.check_expansions();
        self.check_justified();
        if !self.unparsed.is_empty() {
            self.diags.push(Diag {
                pos: 0,
                label: "database".into(),
                rule: Some(4),
                msg: format!(
                    "{} assertions could not be parsed, so the results are incomplete",
                    self.unparsed.len()
                ),
                warning: false,
            });
        }
        self.diags.sort_by_key(|d| (d.pos, d.rule));
        self.diags
    }

    // ---------------------------------------------------------------------
    // Helpers

    fn symbol(&self, tok: &[u8]) -> Option<Symbol> {
        self.nset.lookup_symbol(tok).map(|s| s.atom)
    }

    fn label_atom(&self, label: &[u8]) -> Option<Label> {
        self.nset.lookup_label(label).map(|l| l.atom)
    }

    fn name(&self, atom: Label) -> &'a str {
        as_str(self.nset.atom_name(atom))
    }

    fn stmt(&self, addr: StatementAddress) -> StatementRef<'a> {
        self.db.statement_by_address(addr)
    }

    fn stmt_name(&self, addr: StatementAddress) -> String {
        as_str(self.stmt(addr).label()).to_owned()
    }

    fn frame(&self, sref: StatementRef<'_>) -> Option<&'a Frame> {
        self.db.scope_result().get(sref.label())
    }

    fn formula(&self, sref: &StatementRef<'_>) -> Option<&'a Formula> {
        self.db.stmt_parse_result().get_formula(sref)
    }

    fn is_bound(&self, typecode: Symbol) -> bool {
        self.bound_types.contains(&typecode)
    }

    /// Addresses of the `$e` hypotheses of a frame, in order.
    fn essentials(frame: &Frame) -> impl Iterator<Item = StatementAddress> + '_ {
        frame.hypotheses.iter().filter_map(|h| match h {
            Hyp::Essential(addr, _) => Some(*addr),
            Hyp::Floating(..) => None,
        })
    }

    fn report(&mut self, addr: StatementAddress, rule: Option<u8>, msg: String) {
        self.report_at(self.pos[&addr], self.stmt_name(addr), rule, msg, false);
    }

    fn report_at(&mut self, pos: u32, label: String, rule: Option<u8>, msg: String, warning: bool) {
        self.diags.push(Diag {
            pos,
            label,
            rule,
            msg,
            warning,
        });
    }

    fn arity(&self, label: Label) -> Option<usize> {
        self.syntax_index.get(&label).map(|&i| self.syntax[i].arity)
    }

    fn expr(&self, f: &Formula) -> Option<Expr> {
        Expr::from_formula(f, &|l| self.arity(l))
    }

    fn constructor_name(&self, c: usize) -> &str {
        &self.syntax[c].name
    }

    /// Flattens a parse tree into tokens. `leaf` may handle a subtree itself
    /// by writing its tokens and returning true.
    fn flatten(&self, e: &Expr, out: &mut Vec<Tok>, leaf: &mut dyn FnMut(&Expr, &mut Vec<Tok>) -> bool) {
        if leaf(e, out) {
            return;
        }
        match e {
            Expr::Var(label) => out.push(Tok::Sym(self.floats[label].0)),
            Expr::App(label, args) => {
                let s = &self.syntax[self.syntax_index[label]];
                for &t in &s.template {
                    match t {
                        TemplateTok::Const(sym) => out.push(Tok::Sym(sym)),
                        TemplateTok::Arg(i) => self.flatten(&args[i], out, leaf),
                    }
                }
            }
        }
    }

    fn render_toks(&self, toks: &[Tok], hole_names: &[Label]) -> String {
        let mut s = String::new();
        for (i, t) in toks.iter().enumerate() {
            if i > 0 {
                s.push(' ');
            }
            match *t {
                Tok::Sym(sym) => s.push_str(self.name(sym)),
                Tok::Hole(h) => {
                    let _ = write!(s, "?{}", self.name(self.floats[&hole_names[h]].0));
                }
            }
        }
        s
    }

    /// Variables occurring in the math strings of a statement's conclusion
    /// and `$e` hypotheses, i.e. its variables that are not dummy variables.
    fn statement_vars(&self, sref: StatementRef<'a>, frame: &Frame) -> HashSet<Symbol> {
        let mut vars = HashSet::new();
        let mut add = |sref: StatementRef<'a>| {
            for tok in sref.math_iter().skip(1) {
                if let Some(s) = self.nset.lookup_symbol(&tok)
                    && s.stype == SymbolType::Variable {
                        vars.insert(s.atom);
                    }
            }
        };
        add(sref);
        for addr in Self::essentials(frame) {
            add(self.stmt(addr));
        }
        vars
    }

    // ---------------------------------------------------------------------
    // Collection passes

    fn collect_syntax(&mut self) {
        for sref in self.db.statements() {
            if sref.statement_type() != StatementType::Axiom {
                continue;
            }
            let Some(tc) = self.symbol(&sref.math_at(0)) else { continue };
            if !self.var_types.contains(&tc) {
                continue;
            }
            let Some(label) = self.label_atom(sref.label()) else { continue };
            let mut template = Vec::new();
            let mut seen: Vec<Symbol> = Vec::new();
            let mut repeated_vars = Vec::new();
            for tok in sref.math_iter().skip(1) {
                let Some(s) = self.nset.lookup_symbol(&tok) else { continue };
                if s.stype == SymbolType::Variable {
                    match seen.iter().position(|&v| v == s.atom) {
                        Some(i) => {
                            repeated_vars.push(as_str(&tok).to_owned());
                            template.push(TemplateTok::Arg(i));
                        }
                        None => {
                            template.push(TemplateTok::Arg(seen.len()));
                            seen.push(s.atom);
                        }
                    }
                } else {
                    template.push(TemplateTok::Const(s.atom));
                }
            }
            self.syntax_index.insert(label, self.syntax.len());
            self.syntax.push(SyntaxAxiom {
                addr: sref.address(),
                name: as_str(sref.label()).to_owned(),
                typecode: tc,
                template,
                arity: seen.len(),
                repeated_vars,
            });
        }
        self.primitive = vec![false; self.syntax.len()];
        self.jdefs = vec![Vec::new(); self.syntax.len()];
        self.expansions = (0..self.syntax.len()).map(|_| None).collect();
    }

    fn read_j_commands(&mut self) {
        let db = self.db;
        for sref in db.statements() {
            if sref.statement_type() != StatementType::AdditionalInfoComment {
                continue;
            }
            let pos = self.pos[&sref.address()];
            let segment = sref.segment().segment;
            let buf: &[u8] = &segment.buffer;
            for (ix, (_, toks)) in &segment.j_commands {
                if *ix != sref.index() {
                    continue;
                }
                let Some((CommandToken::Keyword(kw), rest)) = toks.split_first() else {
                    continue;
                };
                let values = || rest.iter().map(|t| t.value(buf).into_owned());
                match kw.as_ref(buf) {
                    b"bound" => {
                        for tc in values() {
                            match self.nset.lookup_symbol(&tc) {
                                // Rule 1. A constant that is not a variable
                                // type is allowed, but is not a bound type.
                                Some(s) if s.stype == SymbolType::Constant => {
                                    if self.var_types.contains(&s.atom) {
                                        self.bound_types.insert(s.atom);
                                    }
                                }
                                _ => self.report_at(
                                    pos,
                                    "$j bound".into(),
                                    Some(1),
                                    format!("'{}' is not a math constant", as_str(&tc)),
                                    false,
                                ),
                            }
                        }
                    }
                    b"primitive" => {
                        for label in values() {
                            let atom = self.label_atom(&label);
                            match atom.and_then(|a| self.syntax_index.get(&a)) {
                                Some(&i) => self.primitive[i] = true,
                                // Rule 2.
                                None => self.report_at(
                                    pos,
                                    "$j primitive".into(),
                                    Some(2),
                                    match atom {
                                        Some(_) => format!("'{}' is not a syntax axiom", as_str(&label)),
                                        None => format!("unknown label '{}'", as_str(&label)),
                                    },
                                    false,
                                ),
                            }
                        }
                    }
                    b"definition" => match rest {
                        [target, CommandToken::Keyword(for_), constructor]
                            if for_.as_ref(buf) == b"for" =>
                        {
                            let target = target.value(buf).into_owned();
                            let constructor = constructor.value(buf);
                            let i = self
                                .label_atom(&constructor)
                                .and_then(|a| self.syntax_index.get(&a).copied());
                            match i {
                                Some(i) => self.jdefs[i].push((pos, target)),
                                None => self.report_at(
                                    pos,
                                    "$j definition".into(),
                                    Some(3),
                                    format!(
                                        "'{}' is not a syntax axiom",
                                        as_str(&constructor)
                                    ),
                                    false,
                                ),
                            }
                        }
                        _ => self.report_at(
                            pos,
                            "$j definition".into(),
                            Some(3),
                            "malformed command, expected `definition 'label' for 'label';`".into(),
                            false,
                        ),
                    },
                    _ => {}
                }
            }
        }
    }

    fn formula_constructors(&self, f: &Formula, out: &mut Vec<usize>) {
        for (label, is_var) in f.labels_iter() {
            if !is_var
                && let Some(&i) = self.syntax_index.get(&label) {
                    out.push(i);
                }
        }
    }

    fn collect_contains(&mut self) {
        let db = self.db;
        for sref in db.statements() {
            if !sref.is_assertion() {
                continue;
            }
            let addr = sref.address();
            let mut cs = Vec::new();
            if let Some(&i) = self.label_atom(sref.label()).and_then(|a| self.syntax_index.get(&a)) {
                cs.push(i);
            } else {
                let mut parsed = true;
                match self.formula(&sref) {
                    Some(f) => self.formula_constructors(f, &mut cs),
                    None => parsed = false,
                }
                if let Some(frame) = self.frame(sref) {
                    for hyp in Self::essentials(frame) {
                        match self.formula(&self.stmt(hyp)) {
                            Some(f) => self.formula_constructors(f, &mut cs),
                            None => parsed = false,
                        }
                    }
                }
                if !parsed {
                    self.unparsed.insert(addr);
                }
                cs.sort_unstable();
                cs.dedup();
            }
            self.contains.insert(addr, cs.into_boxed_slice());
        }
    }

    fn contains(&self, addr: StatementAddress, c: usize) -> bool {
        self.contains.get(&addr).is_some_and(|cs| cs.binary_search(&c).is_ok())
    }

    /// Whether constructor `d` is defined later than constructor `c`. Only
    /// defined constructors with an associated definition are ordered.
    fn is_later(&self, d: usize, c: usize) -> bool {
        matches!((self.rank[d], self.rank[c]), (Some(a), Some(b)) if a > b)
    }

    /// The latest-defined constructor contained in an assertion that is
    /// defined later than `c`, if any.
    fn later_in(&self, addr: StatementAddress, c: usize) -> Option<usize> {
        let cs = self.contains.get(&addr)?;
        cs.iter().copied().filter(|&d| self.is_later(d, c)).max_by_key(|&d| self.rank[d])
    }

    // ---------------------------------------------------------------------
    // Syntax and types: rules 5 and 7

    fn check_syntax(&mut self) {
        for i in 0..self.syntax.len() {
            let s = &self.syntax[i];
            let addr = s.addr;
            let mut msgs = Vec::new();
            if let Some(frame) = self.frame(self.stmt(addr)) {
                if Self::essentials(frame).next().is_some() {
                    msgs.push((7, "syntax axiom has $e hypotheses".to_owned()));
                }
                if !frame.mandatory_dv.is_empty() {
                    msgs.push((7, "syntax axiom has DV restrictions".to_owned()));
                }
            }
            if !s.repeated_vars.is_empty() {
                msgs.push((
                    7,
                    format!("variables occur more than once: {}", s.repeated_vars.join(" ")),
                ));
            }
            if self.is_bound(s.typecode) {
                msgs.push((5, format!("typecode '{}' is bound", self.name(s.typecode))));
            }
            for (rule, msg) in msgs {
                self.report(addr, Some(rule), msg);
            }
        }
    }

    /// Rule 6.
    fn check_dv(&mut self) {
        let db = self.db;
        for sref in db.statements() {
            if !sref.is_assertion() {
                continue;
            }
            let Some(frame) = self.frame(sref) else { continue };
            if frame.mandatory_dv.is_empty() {
                continue;
            }
            let typecodes: HashMap<usize, Symbol> = frame
                .hypotheses
                .iter()
                .filter_map(|h| match *h {
                    Hyp::Floating(_, i, tc) => Some((i, tc)),
                    Hyp::Essential(..) => None,
                })
                .collect();
            let pairs: Vec<String> = frame
                .mandatory_dv
                .iter()
                .filter(|(i, j)| {
                    [i, j]
                        .iter()
                        .all(|v| typecodes.get(v).is_some_and(|&tc| !self.is_bound(tc)))
                })
                .map(|&(i, j)| {
                    format!("{} {}", self.name(frame.var_list[i]), self.name(frame.var_list[j]))
                })
                .collect();
            if !pairs.is_empty() {
                self.report(
                    sref.address(),
                    Some(6),
                    format!(
                        "mandatory DV restriction between variables of non-bound type: {}",
                        pairs.join(", ")
                    ),
                );
            }
        }
    }

    // ---------------------------------------------------------------------
    // Definition axioms: rules 8 and 9

    fn check_definitions(&mut self, defs: &Pattern, include: &Pattern, exclude: &Pattern) {
        let db = self.db;
        let n = self.syntax.len();

        // Definition axioms in database order, with the constructors their
        // conclusions contain.
        let mut def_list: Vec<(StatementAddress, Vec<usize>)> = Vec::new();
        for sref in db.statements() {
            if sref.statement_type() != StatementType::Axiom {
                continue;
            }
            let addr = sref.address();
            let pos = self.pos[&addr];
            let label = sref.label();
            if !defs.matches(label, pos) || exclude.matches(label, pos) {
                continue;
            }
            let enforced = include.matches(label, pos);
            let mut cs = Vec::new();
            match self.formula(&sref) {
                Some(f) => self.formula_constructors(f, &mut cs),
                None => {
                    self.unparsed.insert(addr);
                }
            }
            cs.sort_unstable();
            cs.dedup();
            self.defs.insert(addr, DefAxiom { constructor: None, enforced });
            def_list.push((addr, cs));
        }

        // The associated definition of a defined constructor is the first
        // definition axiom whose conclusion contains it.
        let mut assoc: Vec<Option<StatementAddress>> = vec![None; n];
        let mut defined_by: HashMap<StatementAddress, Vec<usize>> = HashMap::new();
        for (addr, cs) in &def_list {
            for &c in cs {
                if !self.primitive[c] && assoc[c].is_none() {
                    assoc[c] = Some(*addr);
                    defined_by.entry(*addr).or_default().push(c);
                }
            }
        }
        self.rank = assoc.iter().map(|a| a.map(|a| self.pos[&a])).collect();
        self.enforced = vec![false; n];

        // Rules 8 and 9, for the whole database.
        for (c, a) in assoc.iter().enumerate() {
            if !self.primitive[c] && a.is_none() {
                self.report(
                    self.syntax[c].addr,
                    Some(8),
                    "defined constructor has no associated definition".into(),
                );
            }
        }
        for (addr, cs) in &def_list {
            match defined_by.get(addr).map_or(&[][..], Vec::as_slice) {
                [] if self.unparsed.contains(addr) => {}
                [] => {
                    let contained: Vec<String> = cs
                        .iter()
                        .map(|&c| match assoc[c] {
                            None => format!("{} (primitive)", self.constructor_name(c)),
                            Some(d) => format!("{} ({})", self.constructor_name(c), self.stmt_name(d)),
                        })
                        .collect();
                    self.report(
                        *addr,
                        Some(9),
                        format!(
                            "not the associated definition of any defined constructor; its conclusion contains: {}",
                            if contained.is_empty() { "nothing".to_owned() } else { contained.join(", ") }
                        ),
                    );
                }
                &[c] => {
                    let def = self.defs.get_mut(addr).unwrap();
                    def.constructor = Some(c);
                    self.enforced[c] = def.enforced;
                }
                many => {
                    let names: Vec<&str> = many.iter().map(|&c| self.constructor_name(c)).collect();
                    let msg = format!(
                        "associated definition of more than one defined constructor: {}",
                        names.join(" ")
                    );
                    self.report(*addr, Some(9), msg);
                }
            }
        }

        // The expansions of constructors without `$j definition`.
        for (c, a) in assoc.iter().enumerate() {
            let (true, Some(def)) = (self.enforced[c], *a) else {
                continue;
            };
            if self.jdefs[c].is_empty() {
                self.expansions[c] = self.expansion_from(c, def, None);
            }
        }
    }

    // ---------------------------------------------------------------------
    // Expansions: rules 3 and 10 to 13

    fn check_expansions(&mut self) {
        for c in 0..self.syntax.len() {
            let jdefs = std::mem::take(&mut self.jdefs[c]);
            let name = self.constructor_name(c).to_owned();
            let Some((pos, target)) = jdefs.first() else { continue };
            if self.primitive[c] {
                for (pos, _) in &jdefs {
                    self.report_at(
                        *pos,
                        "$j definition".into(),
                        Some(3),
                        format!("primitive constructor '{name}' has a $j definition"),
                        false,
                    );
                }
                continue;
            }
            if jdefs.len() > 1 {
                for (pos, _) in &jdefs[1..] {
                    self.report_at(
                        *pos,
                        "$j definition".into(),
                        Some(3),
                        format!("constructor '{name}' has more than one $j definition"),
                        false,
                    );
                }
            }
            if !self.enforced[c] {
                continue;
            }
            let target_addr = self
                .nset
                .lookup_label(target)
                .map(|l| l.address)
                .filter(|&a| self.stmt(a).is_assertion());
            let Some(target_addr) = target_addr else {
                self.report_at(
                    *pos,
                    "$j definition".into(),
                    Some(3),
                    format!("'{}' is not an $a or $p statement", as_str(target)),
                    false,
                );
                // Don't fall back to the associated definition.
                self.expansions[c] = None;
                continue;
            };
            self.expansions[c] = self.expansion_from(c, target_addr, Some(*pos));
        }
    }

    /// Extracts the expansion of constructor `c` from the given expansion
    /// statement, checking rules 10 to 13. `jpos` is the position of the
    /// `$j definition` that named it, if any.
    fn expansion_from(
        &mut self,
        c: usize,
        addr: StatementAddress,
        jpos: Option<u32>,
    ) -> Option<Expansion> {
        let sref = self.stmt(addr);
        let name = self.constructor_name(c).to_owned();
        let via = match jpos {
            Some(_) => format!("expansion statement of '{name}' (from $j definition)"),
            None => format!("expansion statement of '{name}'"),
        };
        let Some(e) = self.formula(&sref).and_then(|f| self.expr(f)) else {
            self.unparsed.insert(addr);
            return None;
        };
        let (lhs, rhs) = match &e {
            Expr::App(_, args) if args.len() == 2 => (&args[0], &args[1]),
            _ => {
                self.report(
                    addr,
                    Some(10),
                    format!("{via}: root of the conclusion is not a constructor with two arguments"),
                );
                return None;
            }
        };

        // Rule 11.
        let label = self.label_atom(self.stmt(self.syntax[c].addr).label())?;
        let lhs_vars: Option<Vec<Label>> = match lhs {
            Expr::App(l, args) if *l == label => args
                .iter()
                .map(|a| match a {
                    Expr::Var(v) => Some(*v),
                    Expr::App(..) => None,
                })
                .collect(),
            _ => None,
        };
        let lhs_vars = match lhs_vars {
            Some(vs) if (1..vs.len()).all(|i| !vs[..i].contains(&vs[i])) => vs,
            _ => {
                self.report(
                    addr,
                    Some(11),
                    format!("{via}: definiendum (LHS) is not '{name}' applied to distinct variables"),
                );
                return None;
            }
        };
        let mut ok = true;

        // Rule 13.
        if let Some(frame) = self.frame(sref) {
            let lhs_syms: Vec<Symbol> = lhs_vars.iter().map(|v| self.floats[v].0).collect();
            let pairs: Vec<String> = frame
                .mandatory_dv
                .iter()
                .map(|&(i, j)| (frame.var_list[i], frame.var_list[j]))
                .filter(|(a, b)| lhs_syms.contains(a) && lhs_syms.contains(b))
                .map(|(a, b)| format!("{} {}", self.name(a), self.name(b)))
                .collect();
            if !pairs.is_empty() {
                self.report(
                    addr,
                    Some(13),
                    format!(
                        "{via}: DV restriction between definiendum (LHS) variables: {}",
                        pairs.join(", ")
                    ),
                );
                ok = false;
            }
        }

        // Rule 12.
        let mut bad = Vec::new();
        rhs.for_each_app(&mut |l, _| {
            let i = self.syntax_index[&l];
            if (i == c || self.is_later(i, c)) && !bad.contains(&i) {
                bad.push(i);
            }
        });
        if !bad.is_empty() {
            let names: Vec<&str> = bad.iter().map(|&i| self.constructor_name(i)).collect();
            self.report(
                addr,
                Some(12),
                format!(
                    "{via}: definiens (RHS) contains the constructor itself or a later-defined constructor: {}",
                    names.join(" ")
                ),
            );
            ok = false;
        }

        let mut hidden = Vec::new();
        rhs.for_each_var(&mut |v| {
            if !lhs_vars.contains(&v) && !hidden.contains(&v) {
                hidden.push(v);
            }
        });
        ok.then(|| Expansion {
            lhs_vars,
            rhs: rhs.clone(),
            hidden,
        })
    }

    // ---------------------------------------------------------------------
    // Justified theorems: rules 14 to 23

    fn check_justified(&mut self) {
        let db = self.db;
        for sref in db.statements() {
            if sref.statement_type() != StatementType::Provable {
                continue;
            }
            let mut referenced: Vec<StatementAddress> = Vec::new();
            for (_, tok) in sref.use_iter() {
                if let Some(l) = self.nset.lookup_label(tok)
                    && self.defs.contains_key(&l.address) && !referenced.contains(&l.address) {
                        referenced.push(l.address);
                    }
            }
            match referenced[..] {
                [] => {}
                [def] if self.defs[&def].enforced => self.check_justified_theorem(sref, def),
                [_] => {}
                // Like the other rules about a proof, rule 14 is only
                // enforced when it involves a selected definition axiom.
                _ if !referenced.iter().any(|d| self.defs[d].enforced) => {}
                _ => {
                    let names: Vec<String> = referenced.iter().map(|&a| self.stmt_name(a)).collect();
                    self.report(
                        sref.address(),
                        Some(14),
                        format!("proof directly uses more than one definition axiom: {}", names.join(" ")),
                    );
                }
            }
        }
    }

    fn check_justified_theorem(&mut self, sref: StatementRef<'a>, def: StatementAddress) {
        let addr = sref.address();
        let Some(c) = self.defs[&def].constructor else { return };
        let cname = self.constructor_name(c).to_owned();
        let Some(frame) = self.frame(sref) else { return };
        let hyp_addrs: Vec<StatementAddress> = Self::essentials(frame).collect();

        // Rule 16.
        for &h in &hyp_addrs {
            if let Some(f) = self.formula(&self.stmt(h)) {
                let mut cs = Vec::new();
                self.formula_constructors(f, &mut cs);
                if cs.contains(&c) {
                    self.report(
                        addr,
                        Some(16),
                        format!(
                            "$e hypothesis {} contains the associated constructor '{cname}'",
                            self.stmt_name(h)
                        ),
                    );
                }
            }
        }

        // Rule 15.
        if let Some(l) = self.later_in(addr, c) {
            self.report(
                addr,
                Some(15),
                format!(
                    "contains '{}', which is defined later than the associated constructor '{cname}'",
                    self.constructor_name(l)
                ),
            );
        }
        let mut later_uses = Vec::new();
        for (_, tok) in sref.use_iter() {
            let Some(l) = self.nset.lookup_label(tok) else { continue };
            if let Some(latest) = self.later_in(l.address, c) {
                let s = format!("{} ({})", as_str(tok), self.constructor_name(latest));
                if !later_uses.contains(&s) {
                    later_uses.push(s);
                }
            }
        }
        if !later_uses.is_empty() {
            self.report(
                addr,
                Some(15),
                format!(
                    "proof contains syntax defined later than the associated constructor '{cname}': {}",
                    later_uses.join(", ")
                ),
            );
        }

        // Rule 17.
        let Some(concl) = self.formula(&sref).and_then(|f| self.expr(f)) else {
            self.unparsed.insert(addr);
            return;
        };
        let label = self.label_atom(self.stmt(self.syntax[c].addr).label()).unwrap();
        let mut occurrences: Vec<&[Expr]> = Vec::new();
        concl.for_each_app(&mut |l, args| {
            if l == label {
                occurrences.push(args);
            }
        });
        let args: Option<Vec<Expr>> = match occurrences.split_first() {
            Some((first, rest)) if rest.iter().all(|a| a == first) => Some(first.to_vec()),
            _ => {
                self.report(
                    addr,
                    Some(17),
                    format!("occurrences of the associated constructor '{cname}' in the conclusion have different arguments"),
                );
                None
            }
        };

        // The proof itself.
        let mut arr = ProofTreeArray::new(true);
        let qed = match self.db.verify_one(&mut arr, sref) {
            Ok(qed) => qed,
            Err(diag) => {
                self.report(
                    addr,
                    None,
                    format!("justified theorem does not have a complete, valid proof ({diag:?})"),
                );
                return;
            }
        };
        let exprs = arr.exprs().unwrap();
        let toks = |i: usize| -> Vec<&[u8]> {
            exprs[i].split(|&b| b == b' ').filter(|t| !t.is_empty()).collect()
        };
        let typecode = self.symbol(&sref.math_at(0));

        // Rule 18.
        let last = self.stmt(arr.trees[qed].address);
        let last_frame = last.is_assertion().then(|| self.frame(last)).flatten();
        let ess_positions: Vec<usize> = last_frame
            .map(|f| {
                f.hypotheses
                    .iter()
                    .enumerate()
                    .filter(|(_, h)| matches!(h, Hyp::Essential(..)))
                    .map(|(i, _)| i)
                    .collect()
            })
            .unwrap_or_default();
        let (Some(last_frame), &[p1, p2]) = (last_frame, &ess_positions[..]) else {
            self.report(
                addr,
                Some(18),
                format!(
                    "final step uses {}, which is not an assertion with exactly two $e hypotheses",
                    as_str(last.label())
                ),
            );
            return;
        };
        let hyp_tc = |p: usize| Some(last_frame.hypotheses[p].typecode());
        let e1 = arr.trees[qed].children[p1];
        let e2 = arr.trees[qed].children[p2];

        // Rule 19.
        let concl_toks: Vec<&[u8]> = sref.math_iter().skip(1).map(|t| t.slice).collect();
        if toks(e1) != concl_toks || hyp_tc(p1) != typecode {
            self.report(
                addr,
                Some(19),
                format!(
                    "first subproof's conclusion does not match the final step's conclusion; it is '{}'",
                    as_str(&exprs[e1]).trim()
                ),
            );
        }

        // Rule 20.
        let step = &arr.trees[e1];
        if step.address != def {
            self.report(
                addr,
                Some(20),
                format!(
                    "first subproof ends in {}, not in the definition axiom {}",
                    self.stmt_name(step.address),
                    self.stmt_name(def)
                ),
            );
        } else if let Some(def_frame) = self.frame(self.stmt(def)) {
            let direct = def_frame.hypotheses.iter().zip(&step.children).all(|(h, &child)| {
                matches!(h, Hyp::Floating(..))
                    || (hyp_addrs.contains(&arr.trees[child].address)
                        && arr.trees[child].children.is_empty())
            });
            if !direct {
                self.report(
                    addr,
                    Some(20),
                    "$e hypotheses of the definition axiom are not all satisfied directly by $e hypotheses of the justified theorem".into(),
                );
            }
        }

        // Rule 22. The definition axiom contains the associated constructor,
        // so this also catches a use of it.
        let mut stack = vec![e2];
        let mut seen = vec![false; arr.trees.len()];
        let mut bad_uses = Vec::new();
        while let Some(i) = stack.pop() {
            if std::mem::replace(&mut seen[i], true) {
                continue;
            }
            let a = arr.trees[i].address;
            if self.contains(a, c) {
                let name = self.stmt_name(a);
                if !bad_uses.contains(&name) {
                    bad_uses.push(name);
                }
            }
            stack.extend(&arr.trees[i].children);
        }
        if !bad_uses.is_empty() {
            self.report(
                addr,
                Some(22),
                format!(
                    "second subproof contains the associated constructor '{cname}': {}",
                    bad_uses.join(" ")
                ),
            );
        }

        // Rules 21 and 23 need the expansion and consistent arguments.
        let (Some(exp), Some(args)) = (&self.expansions[c], args) else { return };
        let mut expected = Vec::new();
        self.flatten(&concl, &mut expected, &mut |e, out| match e {
            Expr::App(l, _) if *l == label => {
                self.flatten(&exp.rhs, out, &mut |r, out| match r {
                    Expr::Var(v) => {
                        if let Some(i) = exp.lhs_vars.iter().position(|x| x == v) {
                            self.flatten(&args[i], out, &mut |_, _| false);
                        } else {
                            let h = exp.hidden.iter().position(|x| x == v).unwrap();
                            out.push(Tok::Hole(h));
                        }
                        true
                    }
                    Expr::App(..) => false,
                });
                true
            }
            _ => false,
        });

        // Rule 21: match the second subproof's conclusion against the expected
        // string, where each hole is a hidden variable.
        let actual: Vec<Option<Symbol>> = toks(e2).iter().map(|t| self.symbol(t)).collect();
        let mut dummies: Vec<Option<Symbol>> = vec![None; exp.hidden.len()];
        let matched = actual.len() == expected.len()
            && hyp_tc(p2) == typecode
            && expected.iter().zip(&actual).all(|(e, &a)| match *e {
                Tok::Sym(s) => a == Some(s),
                Tok::Hole(h) => match (dummies[h], a) {
                    (Some(d), _) => a == Some(d),
                    (None, Some(a)) => {
                        dummies[h] = Some(a);
                        true
                    }
                    (None, None) => false,
                },
            });
        if !matched {
            self.report(
                addr,
                Some(21),
                format!(
                    "second subproof's conclusion is not the final step's conclusion with the definiens (RHS) substituted\n  expected: {}\n  found:    {}",
                    self.render_toks(&expected, &exp.hidden),
                    as_str(&exprs[e2]).trim()
                ),
            );
            return;
        }

        // Rule 21, continued: the hidden variables must be replaced by
        // distinct fresh dummy variables.
        let hidden: Vec<(Symbol, Symbol)> = exp.hidden.iter().map(|h| self.floats[h]).collect();
        let stmt_vars = self.statement_vars(sref, frame);
        // Types of variables. `metamath-rs` doesn't check that every `$f`
        // statement for a variable has the same type, so take the ones this
        // statement uses: its mandatory `$f` hypotheses, and those its proof
        // uses for dummy variables.
        let mut scoped_types: HashMap<Symbol, Symbol> = frame
            .hypotheses
            .iter()
            .filter_map(|h| match *h {
                Hyp::Floating(_, i, tc) => Some((frame.var_list[i], tc)),
                Hyp::Essential(..) => None,
            })
            .collect();
        for tree in &arr.trees {
            let f = self.stmt(tree.address);
            if f.statement_type() == StatementType::Floating
                && let (Some(tc), Some(var)) = (self.symbol(&f.math_at(0)), self.symbol(&f.math_at(1)))
            {
                scoped_types.entry(var).or_insert(tc);
            }
        }
        let mut fresh: Vec<Symbol> = Vec::new();
        for (h, d) in dummies.iter().enumerate() {
            // A hidden variable that occurs in no hole has nothing to check.
            let Some(d) = *d else { continue };
            let hidden_name = self.name(hidden[h].0);
            let dname = self.name(d);
            let is_var = self
                .nset
                .lookup_symbol(self.nset.atom_name(d))
                .is_some_and(|s| s.stype == SymbolType::Variable);
            let mut problems = Vec::new();
            if !is_var {
                problems.push("is not a variable".to_owned());
            } else if scoped_types.get(&d) != Some(&hidden[h].1) {
                problems.push("has a different type".to_owned());
            }
            if stmt_vars.contains(&d) {
                problems.push("is not a dummy variable (it occurs in the conclusion or $e hypotheses)".to_owned());
            }
            if fresh.contains(&d) {
                problems.push("also replaces another hidden variable".to_owned());
            }
            fresh.push(d);
            if !problems.is_empty() {
                self.report(
                    addr,
                    Some(21),
                    format!(
                        "'{dname}', which replaces hidden variable '{hidden_name}', {}",
                        problems.join(" and ")
                    ),
                );
            }
        }

        // Rule 23.
        let mut arg_vars = HashSet::new();
        for a in &args {
            a.for_each_var(&mut |v| {
                arg_vars.insert(self.floats[&v].0);
            });
        }
        let index = |v: Symbol| frame.var_list.iter().position(|&x| x == v);
        let mut pairs = Vec::new();
        for &d in &fresh {
            let Some(di) = index(d) else { continue };
            let mut outside: Vec<Symbol> = stmt_vars
                .iter()
                .copied()
                .filter(|v| !arg_vars.contains(v))
                .filter(|v| scoped_types.get(v).is_some_and(|&tc| !self.is_bound(tc)))
                .filter(|&v| index(v).is_some_and(|vi| frame.optional_dv[di].has_bit(vi)))
                .collect();
            outside.sort_by_key(|&v| self.name(v));
            for v in outside {
                pairs.push(format!("{} {}", self.name(d), self.name(v)));
            }
        }
        if !pairs.is_empty() {
            self.report(
                addr,
                Some(23),
                format!(
                    "DV restriction between a fresh dummy variable and a non-dummy variable of non-bound type outside the arguments: {}",
                    pairs.join(", ")
                ),
            );
        }
    }
}
