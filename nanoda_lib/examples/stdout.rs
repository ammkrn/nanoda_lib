fn main() {
    use nanoda_lib::parser::Parser;
    use nanoda_lib::trace::StdoutTracer;
    use std::time::Instant;
    use std::io::BufReader;
    use std::path::PathBuf;

    let mut args = std::env::args();
    let _ = args.next();

    let export_path = match args.next() {
        None => panic!("The second argument to the example must be \
        an absolute path to the export file. Please see the readme for \
        an example"),
        Some(p) => PathBuf::from(p)
    };

    let open_options = std::fs::OpenOptions::new()
                       .read(true)
                       .truncate(false)
                       .open(&export_path);

    let buf_reader : BufReader<std::fs::File> = match open_options {
        Ok(s) => std::io::BufReader::new(s),
        Err(e) => {
            panic!("Failed to open export file {:#?}\n Err : {}", export_path, e)
        }
    };

    let start = Instant::now();
    let mut parser = Parser::new(buf_reader);
    let num_declars_checked = parser.parse(StdoutTracer::new());
    let time = start.elapsed();
    println!("Checked {} declarations in {:#?}\n", num_declars_checked, time)
}
