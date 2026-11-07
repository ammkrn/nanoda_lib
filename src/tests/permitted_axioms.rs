use crate::env::Declar;
use crate::util::Config;
use std::error::Error;
use std::path::Path;

// The export declares `Quot.sound` and `propext` from Lean's prelude and the axioms `«Quot.sound»`
// (one component), `«».propext` (an empty component followed by `propext`), `propext.1` (a numeric
// component) and `propext.«1»` (the string component "1").
fn config(permitted_axioms: &[&str]) -> Config {
    serde_json::from_value(serde_json::json!({
        "export_file_path": "test_resources/PermittedAxioms/export",
        "permitted_axioms": permitted_axioms,
    }))
    .unwrap()
}

fn skipped_axioms(permitted_axioms: &[&str]) -> Result<Vec<String>, Box<dyn Error>> {
    let mut config = config(permitted_axioms);
    config.unpermitted_axiom_hard_error = false;
    Ok(config.to_export_file()?.1)
}

#[test]
fn permitted_axioms_are_compared_by_component() -> Result<(), Box<dyn Error>> {
    assert_eq!(skipped_axioms(&["Quot.sound", "propext", "propext.1"])?, ["«Quot.sound»", "«».propext", "propext.«1»"]);
    assert_eq!(skipped_axioms(&["«Quot.sound»", "«».propext", "propext.«1»"])?, ["Quot.sound", "propext", "propext.1"]);
    assert_eq!(
        skipped_axioms(&["«Quot».«sound»", "«propext»", "propext.01"])?,
        ["«Quot.sound»", "«».propext", "propext.«1»"]
    );
    Ok(())
}

#[test]
fn unpermitted_axiom_error_escapes_name() {
    match config(&["Quot.sound", "propext"]).to_export_file() {
        Ok(..) => panic!("unpermitted axiom was accepted"),
        Err(e) => assert_eq!(e.to_string(), "export file declares unpermitted axiom \"«Quot.sound»\""),
    }
}

#[test]
fn unsafe_permit_all_axioms_permits_every_axiom() -> Result<(), Box<dyn Error>> {
    let mut config = config(&[]);
    config.permitted_axioms = None;
    config.unsafe_permit_all_axioms = true;
    config.unpermitted_axiom_hard_error = false;
    let (export, skipped) = config.to_export_file()?;
    assert!(skipped.is_empty());
    assert_eq!(export.declars.values().filter(|d| matches!(d, Declar::Axiom { .. })).count(), 6);
    Ok(())
}

#[test]
fn permitted_axioms_in_config_file() -> Result<(), Box<dyn Error>> {
    let config = Config::try_from(Path::new("test_resources/PermittedAxioms/config.json"))?;
    assert_eq!(config.to_export_file()?.1, ["propext", "«Quot.sound»", "propext.1"]);
    Ok(())
}

#[test]
fn invalid_permitted_axiom_is_rejected() {
    let e = Config::try_from(Path::new("test_resources/PermittedAxioms/invalid_config.json")).unwrap_err();
    assert_eq!(e.to_string(), "invalid name in permitted_axioms: \"Quot..sound\"");
}
