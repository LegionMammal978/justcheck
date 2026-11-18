//! Runs the checker on the test databases and compares its output with the
//! expected output. Set `UPDATE_EXPECT=1` to rewrite the expected files.

use std::path::Path;
use std::process::Command;

fn check(name: &str, expected: &str, args: &[&str]) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let output = Command::new(env!("CARGO_BIN_EXE_justcheck"))
        .current_dir(&dir)
        .arg(format!("{name}.mm"))
        .args(args)
        .output()
        .unwrap();
    let actual = String::from_utf8(output.stdout).unwrap();
    let expected_path = dir.join(format!("{expected}.expected"));
    if std::env::var_os("UPDATE_EXPECT").is_some() {
        std::fs::write(&expected_path, &actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&expected_path).unwrap();
    assert_eq!(actual, expected, "output for {name}.mm differs");
}

#[test]
fn basic() {
    check("basic", "basic", &[]);
}

#[test]
fn defs() {
    check("defs", "defs", &[]);
}

/// Rules specific to a definition axiom are only enforced for those selected,
/// but rules 8 and 9 still cover the whole database.
#[test]
fn defs_subset() {
    check("defs", "defs-subset", &["df-an,df-tru", "--exclude", "df-two2"]);
}

/// `metamath-rs` doesn't check that every `$f` statement for a variable has
/// the same type, so a variable's type must come from the `$f` the statement
/// uses, not the first one in the database.
#[test]
fn scope() {
    check("scope", "scope", &[]);
}
