//! `let` checking: the body of a `let` is checked with a free variable that has a value. The
//! exports in `test_resources/Let` are generated from small Lean theorems in which type-checking
//! the proof needs the value of a let-bound variable; each ill-typed export changes one value.
use crate::tests::util::{test_export_file, test_export_file_should_panic};
use std::path::Path;

fn check_all(config: &str) {
    test_export_file_should_panic(Some(Path::new(config)), |export| {
        for declar in export.declars.values() {
            export.check_declar(declar);
        }
    })
}

/// Siblings and shadowing lets with the same name and type, and two declarations with the same
/// let shape, all well-typed.
#[test]
fn let_positive() {
    test_export_file(Some(Path::new("test_resources/Let/positive.json")), |export| {
        for declar in export.declars.values() {
            export.check_declar(declar);
        }
    })
    .unwrap();
}

/// The second of two sibling lets of the same name and type has the wrong value.
#[test]
#[should_panic(expected = "assertion failed")]
fn let_siblings() { check_all("test_resources/Let/siblings.json") }

/// The inner of two shadowing lets of the same name and type has the wrong value.
#[test]
#[should_panic(expected = "assertion failed")]
fn let_shadow() { check_all("test_resources/Let/shadow.json") }

/// The second of two declarations with the same let shape has the wrong value.
#[test]
#[should_panic(expected = "assertion failed")]
fn let_decls() { check_all("test_resources/Let/decls.json") }

/// A let whose value does not have the annotated type, in a body that never uses it. The official
/// kernel rejects this too; substituting the value would remove the mismatch, so this checks that
/// the value is still checked against the annotation.
#[test]
#[should_panic(expected = "assertion failed")]
fn let_value_type() { check_all("test_resources/Let/value_type.json") }
