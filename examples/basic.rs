
use nanoda_lib::parser::Parser;


fn main() {
    use std::time::Instant;
    use std::io::BufReader;
    use std::path::PathBuf;

    let mut args = std::env::args();
    let _ = args.next();
    let num_threads = match args.next() {
        None => panic!("The first argument to the example must be \
        the number of threads. Please see the readme for an example"),
        Some(n) => match n.parse::<usize>() {
            Err(e) => panic!("Error parsing number of threads : {}", e),
            Ok(n) => n
        }
    };

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
    let mut parser = Parser::new(num_threads, buf_reader);
    let num_declars = parser.parser_loop();
    let time = start.elapsed();
    println!("Checked {} declarations in {:#?}\n", num_declars, time)
}
