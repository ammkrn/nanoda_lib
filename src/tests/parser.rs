use crate::tests::util::test_export_file;
use std::path::Path;

#[test]
fn hex_parser_test0() {
    let hex_pairs = "50 61 72 73 65 72";
    match crate::parser::parse_hex_string(&mut hex_pairs.split_whitespace()) {
        Some(s) => assert_eq!(s.as_str(), "Parser"),
        None => panic!(),
    }
}

#[test]
fn bad_semver() {
    let r = test_export_file(Some(&Path::new("test_resources/BadSemver/config.json")), |export| {
        export.check_all_declars_serial();
    });
    match r {
        Err(e) => assert_eq!(
            e.to_string(),
            "parsed semver is less than the minimum supported export version. Found Semver(0, 1, 2), min supported is Semver(2, 0, 0)"
        ),
        _ => panic!()
    }
}
