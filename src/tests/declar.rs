use crate::tests::util::{test_export_file, test_export_file_should_panic};
use std::error::Error;
use std::path::Path;

#[test]
#[should_panic]
fn aesop_goal_unsafe() {
    test_export_file_should_panic(Some(&Path::new("test_resources/AesopGoalUnsafe/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
#[should_panic]
fn nonpositive1() {
    test_export_file_should_panic(Some(&Path::new("test_resources/Nonpositive1/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
#[should_panic]
fn nonpositive2() {
    test_export_file_should_panic(Some(&Path::new("test_resources/Nonpositive2/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
fn check_sexpr_0() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Sexpr/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
fn check_sexpr_1() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Sexpr1/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
fn check_sexpr_2() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Sexpr2/config.json")), |export| {
        export.check_all_declars_serial();
    })
}
#[test]
fn check_sexpr_3() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Sexpr3/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
#[should_panic]
fn cycle1() {
    test_export_file_should_panic(Some(&Path::new("test_resources/Cycle1/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
#[should_panic]
fn cycle_mutual1() {
    test_export_file_should_panic(Some(&Path::new("test_resources/CycleMutual1/config.json")), |export| {
        export.check_all_declars_serial();
    })
}
#[test]
#[should_panic]
fn cycle_opaque1() {
    test_export_file_should_panic(Some(&Path::new("test_resources/CycleOpaque1/config.json")), |export| {
        export.check_all_declars_serial();
    })
}
#[test]
#[should_panic]
fn cycle_opaque2() {
    test_export_file_should_panic(Some(&Path::new("test_resources/CycleOpaque2/config.json")), |export| {
        export.check_all_declars_serial();
    })
}
#[test]
#[should_panic]
fn cycle_opaque3() {
    test_export_file_should_panic(Some(&Path::new("test_resources/CycleOpaque3/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
#[should_panic]
fn axiom_not_allowed0() {
    test_export_file_should_panic(Some(&Path::new("test_resources/AxiomNotAllowed0/config.json")), |export| {
        export.check_all_declars_serial();
    })
}
/*
Does not panic because the axiom is never used.
*/
#[test]
fn axiom_not_allowed1() {
    test_export_file(Some(&Path::new("test_resources/AxiomNotAllowed1/config.json")), |export| {
        export.check_all_declars_serial();
        assert!(export.declars.values().all(|d| !matches!(d, crate::env::Declar::Axiom { .. })))
    })
    .unwrap()
}

#[test]
#[should_panic]
fn axiom_not_allowed2() {
    test_export_file_should_panic(Some(&Path::new("test_resources/AxiomNotAllowed2/config.json")), |export| {
        export.check_all_declars_serial();
    })
}

#[test]
fn mutual_def() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/MutualDef/config.json")), |export| {
        export.check_all_declars_serial();
    })
}
