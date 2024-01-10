use crate::tests::util::test_export_file;
use std::error::Error;
use std::path::Path;

#[test]
fn pp_prelude() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Init/config.json")), |export| {
        for declar in export.declars.values() {
            export.with_pp(|pp| pp.pp_declar(declar.info().name).unwrap());
        }
    })
}

#[test]
fn pp_double_french() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/PpDoubleFrench0/config.json")), |export| {
        for declar in export.declars.values() {
            let _s = export.with_pp(|pp| pp.pp_declar(declar.info().name).unwrap());
        }
    })
}

#[test]
fn pp_let0() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/PpLet0/config.json")), |export| {
        let mut pp_output = export.config.get_pp_destination().unwrap();
        let v = export.pp_selected_declars(pp_output.as_mut());
        assert!(v.is_empty())
    })
}
