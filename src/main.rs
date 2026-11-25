mod check;
mod earley;
mod expr;
mod pattern;

use std::io::{IsTerminal, Write};
use std::process::ExitCode;

use annotate_snippets::Renderer;
use clap::Parser;
use metamath_rs::database::{Database, DbOptions};

use crate::check::{Checker, Diag};
use crate::pattern::Pattern;

/// The hash tables used throughout the crate. Their keys are atoms, addresses
/// and other small integers, which a fast hash function suits best.
pub(crate) use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// Checks that the definitions of a Metamath database are conservative and
/// eliminable, following the rules for definitions with justified theorems in `README.md`.
#[derive(Parser)]
#[command(version)]
struct Cli {
    /// The database file to check.
    database: String,
    /// The definition axioms to enforce the rules for, among those selected
    /// by `--defs`. A comma-separated list of labels, where `*` matches any
    /// sequence of characters, `?` matches any single character, and `a~b`
    /// matches every statement from `a` to `b`.
    #[arg(value_name = "TARGETS", default_value = "*")]
    targets: String,
    /// The axioms that are definition axioms, in the same syntax. The first
    /// of them containing a defined constructor is its associated definition.
    #[arg(long, value_name = "PATTERN", default_value = "df-*")]
    defs: String,
    /// Axioms that are not definition axioms even if `--defs` matches them,
    /// in the same syntax.
    #[arg(long, value_name = "PATTERN")]
    exclude: Option<String>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let mut db = Database::new(DbOptions {
        autosplit: false,
        incremental: true,
        ..DbOptions::default()
    });
    db.parse(cli.database, vec![]);
    db.verify_pass();

    let mut out = std::io::stdout().lock();
    let renderer = if out.is_terminal() {
        Renderer::styled()
    } else {
        Renderer::plain()
    };
    let db_diags = db.render_diags(db.diag_notations(), |msg| renderer.render(msg).to_string());

    let checker = Checker::new(&db);
    let parse = |s: &str| Pattern::parse(s, |label| checker.label_pos(label));
    let patterns = (|| {
        let defs = parse(&cli.defs)?;
        let include = parse(&cli.targets)?;
        let exclude = cli.exclude.as_deref().map(parse).transpose()?.unwrap_or_default();
        Ok::<_, String>((defs, include, exclude))
    })();
    let (defs, include, exclude) = match patterns {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    let diags = checker.run(&defs, &include, &exclude);

    let errors = diags.iter().filter(|d| !d.warning).count();
    let warnings = diags.len() - errors;
    // Stop quietly if stdout is closed, as when piped into `head`.
    let _ = write_report(&mut out, &db_diags, &diags, errors, warnings);
    if errors == 0 && db_diags.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn write_report(
    out: &mut impl Write,
    db_diags: &[String],
    diags: &[Diag],
    errors: usize,
    warnings: usize,
) -> std::io::Result<()> {
    for d in db_diags {
        writeln!(out, "{d}")?;
    }
    for d in diags {
        let kind = if d.warning { "warning" } else { "error" };
        match d.rule {
            Some(rule) => writeln!(out, "{kind}[rule {rule}]: {}: {}", d.label, d.msg)?,
            None => writeln!(out, "{kind}: {}: {}", d.label, d.msg)?,
        }
    }
    writeln!(
        out,
        "{errors} errors, {warnings} warnings, {} database diagnostics",
        db_diags.len()
    )
}
