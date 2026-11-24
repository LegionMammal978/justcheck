//! Syntactic and logical types, the grammar of the syntax constructors, and
//! the parse trees of statements: rules 1, 5 and 6.

use std::collections::HashMap;

use metamath_rs::scopeck::Hyp;
use metamath_rs::statement::{CommandToken, StatementAddress, SymbolType};
use metamath_rs::{Label, StatementType, Symbol, as_str};

use super::Checker;
use crate::earley::{Grammar, Nt, ParseError, Sym, Token, Tree};
use crate::expr::{Expr, TemplateTok};

impl<'a> Checker<'a> {
    /// Reads the `$j syntax` commands, which complete the syntactic types
    /// and define the logical types. Rule 1.
    pub(super) fn read_syntax_commands(&mut self) {
        let db = self.db;
        // `syntax 'SYNTAX' as 'TYPECODE';` commands, checked once every
        // syntactic type is known.
        let mut logical: Vec<(u32, Vec<u8>, Vec<u8>)> = Vec::new();
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
                if kw.as_ref(buf) != b"syntax" {
                    continue;
                }
                match rest {
                    [syntax, CommandToken::Keyword(as_), typecode] if as_.as_ref(buf) == b"as" => {
                        logical.push((
                            pos,
                            syntax.value(buf).into_owned(),
                            typecode.value(buf).into_owned(),
                        ));
                    }
                    _ => {
                        for tok in rest {
                            let tc = tok.value(buf);
                            if let Some(tc) = self.syntax_constant(pos, &tc) {
                                self.syntactic.insert(tc);
                            }
                        }
                    }
                }
            }
        }

        for (pos, syntax, typecode) in logical {
            let (syntax_sym, typecode_sym) =
                (self.syntax_constant(pos, &syntax), self.syntax_constant(pos, &typecode));
            let (Some(syntax_sym), Some(typecode_sym)) = (syntax_sym, typecode_sym) else {
                continue;
            };
            let problem = if self.syntactic.contains(&syntax_sym) {
                Some(format!(
                    "'{}' is a syntactic type, so it cannot be a logical type",
                    as_str(&syntax)
                ))
            } else if !self.syntactic.contains(&typecode_sym) {
                Some(format!("'{}' is not a syntactic type", as_str(&typecode)))
            } else if self.logical.contains_key(&syntax_sym) {
                Some(format!(
                    "'{}' has more than one `syntax ... as` command",
                    as_str(&syntax)
                ))
            } else {
                None
            };
            match problem {
                Some(msg) => self.report_at(pos, "$j syntax".into(), Some(1), msg, false),
                None => {
                    self.logical.insert(syntax_sym, typecode_sym);
                }
            }
        }

        let mut types: Vec<Symbol> = self.syntactic.iter().copied().collect();
        types.sort_by_key(|&tc| self.name(tc));
        self.type_index = types.iter().enumerate().map(|(i, &tc)| (tc, i as Nt)).collect();
    }

    /// The math constant named in a `$j syntax` command.
    fn syntax_constant(&mut self, pos: u32, tok: &[u8]) -> Option<Symbol> {
        match self.nset.lookup_symbol(tok) {
            Some(s) if s.stype == SymbolType::Constant => Some(s.atom),
            _ => {
                self.report_at(
                    pos,
                    "$j syntax".into(),
                    Some(1),
                    format!("'{}' is not a math constant", as_str(tok)),
                    false,
                );
                None
            }
        }
    }

    /// Builds the grammar, with a production for each syntax axiom.
    pub(super) fn build_grammar(&mut self) {
        let mut productions = Vec::new();
        let mut axioms = Vec::new();
        for (i, s) in self.syntax.iter().enumerate() {
            // The types of the variables are those of the axiom's own `$f`
            // hypotheses. An axiom with a scope error has no production.
            let Some(frame) = self.frame(self.stmt(s.addr)) else { continue };
            let types: HashMap<Symbol, Symbol> = frame
                .hypotheses
                .iter()
                .filter_map(|h| match *h {
                    Hyp::Floating(_, v, tc) => Some((frame.var_list[v], tc)),
                    Hyp::Essential(..) => None,
                })
                .collect();
            let rhs: Option<Vec<Sym<Symbol>>> = s
                .template
                .iter()
                .map(|t| match *t {
                    TemplateTok::Const(c) => Some(Sym::Const(c)),
                    TemplateTok::Arg(v) => {
                        Some(Sym::Nt(*self.type_index.get(types.get(&s.vars[v])?)?))
                    }
                })
                .collect();
            if let Some(rhs) = rhs {
                productions.push((self.type_index[&s.typecode], rhs));
                axioms.push(i);
            }
        }
        self.grammar = Some((Grammar::new(self.type_index.len(), productions), axioms));
    }

    /// Converts a parse tree of the grammar. A syntax axiom that repeats a
    /// variable (against rule 9) takes the argument from its first
    /// occurrence.
    fn convert(&self, tree: Tree<Label>, axioms: &[usize]) -> Expr {
        match tree {
            Tree::Leaf(label) => Expr::Var(label),
            Tree::Node(prod, children) => {
                let s = &self.syntax[axioms[prod]];
                let label = self.label_atom(self.stmt(s.addr).label()).unwrap();
                let mut args: Vec<Option<Expr>> = vec![None; s.arity];
                let occurrences = s.template.iter().filter_map(|t| match *t {
                    TemplateTok::Arg(v) => Some(v),
                    TemplateTok::Const(_) => None,
                });
                for (v, child) in occurrences.zip(children) {
                    if args[v].is_none() {
                        args[v] = Some(self.convert(child, axioms));
                    }
                }
                Expr::App(label, args.into_iter().map(Option::unwrap).collect())
            }
        }
    }

    /// Parses every `$a`, `$e` and `$p` statement, at its typecode if that
    /// is a syntactic type and at the corresponding type if it is a logical
    /// type (rule 6). Each must have exactly one parse tree (rule 5). The
    /// variables of a statement are those of the `$f` statements in scope.
    pub(super) fn parse_statements(&mut self) {
        let db = self.db;
        let (grammar, axioms) = self.grammar.take().unwrap();
        /// The label and typecode of an `$f` statement.
        type Float = (Label, Symbol);
        // Variable to its active `$f` statement.
        let mut active: HashMap<Symbol, Float> = HashMap::new();
        // For each open block, the previous values of what it changed.
        let mut scopes: Vec<Vec<(Symbol, Option<Float>)>> = Vec::new();
        // Typecodes that are neither syntactic nor logical, with where they
        // are first used and by how many statements.
        let mut bad_types: Vec<(Symbol, StatementAddress, usize)> = Vec::new();

        for sref in db.statements() {
            match sref.statement_type() {
                StatementType::OpenGroup => scopes.push(Vec::new()),
                StatementType::CloseGroup => {
                    for (var, prev) in scopes.pop().into_iter().flatten().rev() {
                        match prev {
                            Some(prev) => active.insert(var, prev),
                            None => active.remove(&var),
                        };
                    }
                }
                StatementType::Floating => {
                    if let Some(label) = self.label_atom(sref.label())
                        && let Some(&(var, tc)) = self.floats.get(&label)
                    {
                        let prev = active.insert(var, (label, tc));
                        if let Some(scope) = scopes.last_mut() {
                            scope.push((var, prev));
                        }
                    }
                }
                StatementType::Axiom | StatementType::Essential | StatementType::Provable => {
                    let addr = sref.address();
                    let Some(tc) = self.symbol(&sref.math_at(0)) else { continue };
                    let target = if self.syntactic.contains(&tc) {
                        tc
                    } else if let Some(&target) = self.logical.get(&tc) {
                        target
                    } else {
                        match bad_types.iter_mut().find(|(t, ..)| *t == tc) {
                            Some((_, _, n)) => *n += 1,
                            None => bad_types.push((tc, addr, 1)),
                        }
                        continue;
                    };
                    // A statement with an undeclared symbol or a variable
                    // with no `$f` in scope already has a scope error.
                    let tokens: Option<Vec<Token<Symbol, Label>>> = sref
                        .math_iter()
                        .skip(1)
                        .map(|tok| {
                            let s = self.nset.lookup_symbol(&tok)?;
                            Some(match s.stype {
                                SymbolType::Constant => Token::Const(s.atom),
                                SymbolType::Variable => {
                                    let &(label, tc) = active.get(&s.atom)?;
                                    Token::Var(self.type_index[&tc], label)
                                }
                            })
                        })
                        .collect();
                    let Some(tokens) = tokens else { continue };
                    let text = |range: std::ops::Range<usize>| -> String {
                        let toks: Vec<&str> = sref
                            .math_iter()
                            .skip(1 + range.start)
                            .take(range.len())
                            .map(|t| as_str(t.slice))
                            .collect();
                        toks.join(" ")
                    };
                    match grammar.parse(self.type_index[&target], &tokens) {
                        Ok(tree) => {
                            let e = self.convert(tree, &axioms);
                            self.terms.insert(addr, self.store.add(&e));
                            self.trees.insert(addr, e);
                        }
                        Err(ParseError::NoParse { at }) => {
                            let found = if at < tokens.len() {
                                format!("unexpected '{}' at token {}", text(at..at + 1), at + 1)
                            } else {
                                "unexpected end of statement".to_owned()
                            };
                            self.report(
                                addr,
                                Some(6),
                                format!("does not parse as '{}': {found}", self.name(target)),
                            );
                        }
                        Err(ParseError::Ambiguous { start, end }) => {
                            let what = if start == end {
                                "the empty string".to_owned()
                            } else {
                                format!("'{}'", text(start..end))
                            };
                            self.report(
                                addr,
                                Some(5),
                                format!("ambiguous syntax: {what} can be parsed in more than one way"),
                            );
                        }
                    }
                }
                _ => {}
            }
        }

        for (tc, addr, n) in bad_types {
            let statements = if n == 1 { "1 statement".to_owned() } else { format!("{n} statements") };
            self.report(
                addr,
                Some(6),
                format!(
                    "typecode '{}' is neither a syntactic nor a logical type (used by {statements})",
                    self.name(tc)
                ),
            );
        }
        self.grammar = Some((grammar, axioms));
    }
}
