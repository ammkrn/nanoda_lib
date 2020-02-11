
use std::path::PathBuf;
use std::fs::{ File, OpenOptions, read_to_string };
use std::io::{ BufWriter, Result as IoResult, Write };

use nanoda_lib::env::Env;
use nanoda_lib::serial_parser::LineParser;
use nanoda_lib::trace::{ Tracer, Step };

use TracerEnum::*;

#[derive(Debug)]
pub enum TracerEnum {
    Standard(BufWriter<File>),
    Noop,
}

impl TracerEnum {
    fn new(writer : Option<BufWriter<File>>) -> Self {
        match writer {
            Some(w) => Standard(w),
            None => Noop
        }
    }
}

impl Tracer for TracerEnum {
    fn write_to(&mut self, buf : &[u8]) -> IoResult<usize> {
        match self {
            Standard(w) => w.write(buf),
            Noop => Ok(0usize)
        }
    }

    fn get_new(&self) -> Self {
        match self {
            Standard(w) => match w.get_ref().try_clone() {
                Ok(x) => Standard(BufWriter::new(x)),
                Err(e) => panic!("Failed to duplicate writer when forking Tracer : {}", e)
            },
            Noop => Noop
        }
    }


    fn trace_step(&mut self, this_step : &Step) -> IoResult<usize> {
        let mut wrote = 0usize;

        match this_step.get_self_idx() {
            Some(idx) => wrote += self.write_to(idx.to_string().as_bytes())?,
            None => panic!("this_step_idx should never be `None` in trace_step")
        }
        wrote += self.write_to(b".")?;
        wrote += self.write_to(this_step.get_step_name_string().as_bytes())?;
        wrote += self.write_to(b".")?;

        let step_args = this_step.iter_uniques();
        if step_args.is_empty() {
            wrote += self.write_to(b"_")?;
        } else {
            for arg in step_args {
                wrote += self.write_to(arg.to_string().as_bytes())?;
            }
        }

        wrote += self.write_to(b".")?;
        wrote += self.write_to(this_step.get_result().unwrap().to_string().as_bytes())?;

        let references = this_step.get_references();
        if !(references.is_empty()) {
            wrote += self.write_to(b".")?;
            for child in this_step.get_references() {
                wrote += self.write_to(child.to_string().as_bytes())?;
            }
        }

        wrote += self.write_to(b"\n")?;

        Ok(wrote)
    }

    fn trace_info(&mut self, s : String) -> IoResult<usize> {
        match self {
            Noop => Ok(0usize),
            Standard(w) => {
                w.write(s.as_bytes())?;
                w.write(b"\n")
            }
        }
    }

}




fn main() {
    let export_file_path = PathBuf::from("examples/short_lean_export.out");
    let export_file_string = match read_to_string(&export_file_path) {
        Ok(s) => s,
        Err(e) => {
            println!("example failed to open the Lean export file \
                      it was supposed to read. Please check that the file \
                      nanoda_lib/examples/lean_export.out exists, and that \
                      you run the example from the directory nanoda_lib/. \
                      error details : {}", e);
            std::process::exit(-1)
        }
    };

    let trace_output_path = PathBuf::from("examples/example_trace");
    let base_tracer = match OpenOptions::new()
                                        .write(true)
                                        .truncate(true)
                                        .create(true)
                                        .open(&trace_output_path) {
        Ok(h) => TracerEnum::new(Some(BufWriter::new(h))),
        Err(e) => {
            println!("example failed to open the output sink file with write \
                      permissions. Please check that the file \
                      nanoda_lib/examples/trace_output \
                      exists, and allows the example to open it with write permissions.\
                      error details : {}", e);
            std::process::exit(-1);
        }
    };

    let env = Env::new_arc_env(Some(1000));


    if let Err(e) =  LineParser::parse_check_all(export_file_string, env.clone(), &base_tracer) {
        println!("Sorry, the example failed with the following error : {}\n", e)
    }

    let _n = env.read().num_items();
    println!("Example executed successfully! The trace output should be in \
              nanoda_lib/examples/example_trace");
}