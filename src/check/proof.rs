//! Replays proofs on parse trees.
//!
//! A Metamath proof step is valid when each `$e` hypothesis of the assertion
//! it applies, after substitution, equals an earlier step as a string. With
//! an ambiguous grammar, the string may be read as one tree by the
//! hypothesis and as another by the step that proved it, which is how an
//! ambiguity is exploited. So every proof is checked again with the strings
//! replaced by parse trees: those of the `$f` hypotheses come from their
//! subproofs, and those of the assertions from the statement parser.

use std::collections::HashMap;

use metamath_rs::diag::Diagnostic;
use metamath_rs::proof::ProofTreeArray;
use metamath_rs::scopeck::Hyp;
use metamath_rs::statement::StatementAddress;
use metamath_rs::{Label, StatementRef, StatementType};

use super::Checker;
use crate::expr::TermId;

/// A verified proof, with the parse tree of each step's conclusion where it
/// is known.
pub(super) struct Proof {
    pub arr: ProofTreeArray,
    /// The final step.
    pub qed: usize,
    pub terms: Vec<Option<TermId>>,
}

/// A step that agrees with what it uses as a string, but not as a tree.
struct Mismatch {
    /// The assertion applied, or `None` for the theorem's own statement.
    assertion: Option<StatementAddress>,
    /// The `$e` hypothesis or statement that was matched.
    target: StatementAddress,
    expected: TermId,
    found: TermId,
}

impl<'a> Checker<'a> {
    /// Verifies a proof and replays it on parse trees, reporting where the
    /// trees disagree (rule 5). Steps that depend on a statement with no
    /// parse tree have none either; that statement has its own error.
    pub(super) fn replay(&mut self, sref: StatementRef<'a>) -> Result<Proof, Diagnostic> {
        let mut arr = ProofTreeArray::new(false);
        let qed = self.db.verify_one(&mut arr, sref)?;
        let mut terms: Vec<Option<TermId>> = Vec::with_capacity(arr.trees.len());
        let mut mismatches = Vec::new();
        for tree in &arr.trees {
            let step = self.stmt(tree.address);
            let term = match step.statement_type() {
                StatementType::Floating => {
                    self.label_atom(step.label()).map(|l| self.store.var(l))
                }
                StatementType::Essential => self.terms.get(&tree.address).copied(),
                StatementType::Axiom | StatementType::Provable => {
                    self.apply(step, &tree.children, &terms, &mut mismatches)
                }
                _ => None,
            };
            terms.push(term);
        }
        if let (Some(found), Some(&expected)) = (terms[qed], self.terms.get(&sref.address()))
            && found != expected
        {
            mismatches.push(Mismatch {
                assertion: None,
                target: sref.address(),
                expected,
                found,
            });
        }

        // One exploited ambiguity tends to cause several mismatches.
        const SHOWN: usize = 3;
        let more = mismatches.len().saturating_sub(SHOWN);
        for (i, m) in mismatches.iter().take(SHOWN).enumerate() {
            let expected = self.store.expr(m.expected);
            let found = self.store.expr(m.found);
            let what = match m.assertion {
                Some(a) => format!(
                    "proof step using {} satisfies hypothesis {}",
                    self.stmt_name(a),
                    self.stmt_name(m.target)
                ),
                None => "proof's final step matches the statement".to_owned(),
            };
            let mut msg = format!(
                "{what} as a string but not as a parse tree, so the proof relies on an ambiguity\n  string:   {}\n  expected: {}\n  found:    {}",
                self.render(&expected),
                self.sexpr(&expected),
                self.sexpr(&found)
            );
            if i + 1 == SHOWN && more > 0 {
                msg.push_str(&format!("\n  (and {more} more in this proof)"));
            }
            self.report(sref.address(), Some(5), msg);
        }
        Ok(Proof { arr, qed, terms })
    }

    /// The parse tree of the conclusion of a step that applies an assertion
    /// to the given earlier steps.
    fn apply(
        &mut self,
        step: StatementRef<'a>,
        children: &[usize],
        terms: &[Option<TermId>],
        mismatches: &mut Vec<Mismatch>,
    ) -> Option<TermId> {
        let frame = self.frame(step)?;
        let label = self.label_atom(step.label())?;
        let child = |i: usize| terms.get(*children.get(i)?).copied().flatten();

        // A syntax axiom builds a node from its arguments.
        if let Some(&c) = self.syntax_index.get(&label) {
            let mut args = Vec::with_capacity(self.syntax[c].arity);
            for &var in &self.syntax[c].vars {
                let hyp = frame.hypotheses.iter().position(
                    |h| matches!(*h, Hyp::Floating(_, i, _) if frame.var_list[i] == var),
                )?;
                args.push(child(hyp)?);
            }
            return Some(self.store.app(label, args));
        }

        // Any other assertion substitutes for the variables of its statement.
        let mut subst: HashMap<Label, TermId> = HashMap::new();
        for (i, hyp) in frame.hypotheses.iter().enumerate() {
            if let Hyp::Floating(addr, ..) = *hyp {
                let float = self.label_atom(self.stmt(addr).label())?;
                subst.insert(float, child(i)?);
            }
        }
        for (i, hyp) in frame.hypotheses.iter().enumerate() {
            if let Hyp::Essential(addr, _) = *hyp
                && let (Some(&pattern), Some(found)) = (self.terms.get(&addr), child(i))
            {
                let expected = self.store.subst(pattern, &subst);
                if expected != found {
                    mismatches.push(Mismatch {
                        assertion: Some(step.address()),
                        target: addr,
                        expected,
                        found,
                    });
                }
            }
        }
        let pattern = *self.terms.get(&step.address())?;
        Some(self.store.subst(pattern, &subst))
    }
}
