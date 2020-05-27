
use std::path::PathBuf;
use std::fs::read_to_string;

use nanoda_lib::env::Env;
use nanoda_lib::serial_parser::LineParser;

fn main() {
    //let export_file_path = PathBuf::from("examples/short_lean_export.out");
    let export_file_path = PathBuf::from("/home/hkse/vmShared/mathlib_export.out");
    let export_file_string = match read_to_string(&export_file_path) {
        Ok(s) => s,
        Err(e) => {
            println!("example failed to open the Lean export file \
                      it was supposed to read. Please check that the file \
                      nanoda_lib/examples/short_lean_export.out exists, and that \
                      you run the example from the directory nanoda_lib/. \
                      error details : {}", e);
            std::process::exit(-1)
        }
    };

    let env = Env::new_arc_env(Some(1000));


    if let Err(e) =  LineParser::parse_check_all(export_file_string, env.clone()) {
        println!("Sorry, the example failed with the following error : {}\n", e)
    }

    let _n = env.read().num_items();
    println!("Example executed successfully! {} items were checked!", _n);
}
