use std::process::Command;

fn run(config: &str) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_nanoda_bin"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg(config)
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "{stderr}");
    assert_eq!(stderr, "");
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn success_message_with_default_options() {
    assert_eq!(run("test_resources/Empty/config.json"), "Checked 0 declarations with no errors\n");
}

#[test]
fn skipped_axioms_without_destination() {
    assert_eq!(
        run("test_resources/SkippedAxioms/no_destination.json"),
        "Checked 1 declarations with no errors, skipping exported but unpermitted axioms [\"bar\", \"baz\"]\n"
    );
}

#[test]
fn skipped_axioms_with_pretty_printer_errors() {
    assert_eq!(
        run("test_resources/SkippedAxioms/pp_error.json"),
        "axiom foo : Prop\n\nChecked 1 declarations with no typechecker errors, \
         skipping exported but unpermitted axioms [\"bar\", \"baz\"], \
         1 pretty printer errors: [\n    \"declaration missing not found during pretty printing\",\n]\n"
    );
}

#[test]
fn skipped_axioms_without_success_message() {
    assert_eq!(
        run("test_resources/SkippedAxioms/no_success_message.json"),
        "axiom foo : Prop\n\nSkipped exported but unpermitted axioms [\"bar\", \"baz\"]\n"
    );
}

#[test]
fn no_output_without_success_message() {
    assert_eq!(run("test_resources/Empty/silent.json"), "");
}

#[test]
fn print_axioms_off_with_destination() {
    assert_eq!(
        run("test_resources/SkippedAxioms/print_axioms_off.json"),
        "Checked 1 declarations with no errors, skipping exported but unpermitted axioms [\"bar\", \"baz\"]\n"
    );
}
