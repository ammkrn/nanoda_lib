use nanoda_lib::util::Config;
use std::error::Error;
use std::path::Path;

fn main() -> Result<(), MainError> {
    let mut args = std::env::args();
    let _ = args.next();
    let out = match args.next().as_ref() {
        None => Err(Box::from("This program expects a path to a configuration file.".to_string())),
        Some(p) if p == "-h" || p == "--help" => return Ok(println!("{}", HELP_LONG)),
        Some(p) => use_config(&Path::new(p)),
    }
    .map_err(|e| MainError(e))?;

    if let Some(msg) = out {
        println!("{}", msg);
    }
    Ok(())
}

// Returns an optional success message.
fn use_config(config_path: &Path) -> Result<Option<String>, Box<dyn Error>> {
    let cfg = Config::try_from(config_path)?;
    // Make sure the target pretty printer destination is accessible before doing any real work.
    let mut pp_destination = cfg.get_pp_destination()?;
    let export_file = cfg.to_export_file()?;
    // Check the environment
    export_file.check_all_declars();
    // Pretty print as necessary
    let pp_errs = export_file.pp_selected_declars(pp_destination.as_mut());
    if export_file.config.print_success_message {
        if pp_errs.is_empty() {
            Ok(Some(format!("Checked {} declarations with no errors", export_file.declars.len())))
        } else {
            Ok(Some(format!(
                "Checked {} declarations with no logical errors, {} pretty printer errors",
                export_file.declars.len(),
                pp_errs.len()
            )))
        }
    } else {
        Ok(None)
    }
}

struct MainError(Box<dyn Error>);

impl std::fmt::Debug for MainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}\n\n{}", self.0, HELP_SHORT) }
}

const HELP_SHORT: &str = "run with `-h` or `--help` for help";
const HELP_LONG: &str = concat!(
    "nanoda_bin",
    " ",
    env!("CARGO_PKG_VERSION"),
    "\n\n",
    env!("CARGO_PKG_DESCRIPTION"),
    "\n\n",
    "get more help at ",
    env!("CARGO_PKG_REPOSITORY"),
    "\n\n",
    include_str!("../README.md")
);
