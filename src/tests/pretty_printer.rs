use crate::tests::util::test_export_file;
use std::error::Error;
use std::path::Path;

#[test]
fn pp_double_french() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/PpDoubleFrench0/config.json")), |export| {
        for declar in export.declars.values() {
            let _s = export.with_pp(|pp| pp.pp_declar(declar.info().name).unwrap());
        }
    })
}
