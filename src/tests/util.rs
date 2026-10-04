use crate::env::EnvLimit;
use crate::expr::BinderStyle;
use crate::util::{Config, CowStr, ExportFile, ExprPtr, LevelPtr, TcCtx};
use rand::distr::Alphanumeric;
use rand::rngs::ThreadRng;
use std::error::Error;
use std::path::{Path, PathBuf};

pub(crate) fn test_export_file<A>(
    config_path: Option<&Path>,
    f: impl FnOnce(&ExportFile) -> A,
) -> Result<A, Box<dyn Error>> {
    let (export_file, _) = test_get_export_file(config_path)?;
    Ok(f(&export_file))
}

pub(crate) fn test_get_export_file<'p>(config_path: Option<&Path>) -> Result<(ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    let config_file = match config_path {
        None => Config {
            export_file_path: Some(PathBuf::from("test_resources/Empty/export")),
            use_stdin: false,
            permitted_axioms: Some(Vec::new()),
            unpermitted_axiom_hard_error: true,
            nat_extension: false,
            string_extension: false,
            pp_declars: None,
            pp_options: crate::pretty_printer::PpOptions::default(),
            unknown_pp_declar_hard_error: true,
            pp_output_path: None,
            pp_to_stdout: false,
            num_threads: 1,
            print_success_message: true,
            print_axioms: true,
            unsafe_permit_all_axioms: false
        },
        Some(config_path) => Config::try_from(config_path)?,
    };
    config_file.to_export_file()
}

#[allow(dead_code)]
pub(crate) fn test_export_file_should_panic<A>(config_path: Option<&Path>, f: impl FnOnce(&ExportFile) -> A) {
    // If there's an IO issue with actually getting the export file, we don't want
    // `should_panic` test to succeed, so we actually want to return success in this case.
    match test_get_export_file(config_path) {
        Err(..) => {}
        Ok((export_file, _)) => {
            f(&export_file);
        }
    }
}

pub(crate) fn test_ctx<'p, A>(path: Option<&Path>, f: impl FnOnce(&mut TcCtx) -> A) -> Result<A, Box<dyn Error>> {
    test_export_file(path, |export_file| export_file.with_ctx(f))
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    #[cfg(test)]
    pub(crate) fn level_n(&mut self, mut l: LevelPtr<'t>, n: u64) -> LevelPtr<'t> {
        for _ in 0..n {
            l = self.succ(l);
        }
        l
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn mk_succ_app(&mut self, n: usize) -> ExprPtr<'t> {
        let mut out = self.c_nat_zero().unwrap();
        let succ = self.c_nat_succ().unwrap();
        for _ in 0..n {
            out = self.mk_app(succ, out);
        }
        out
    }

    #[cfg(test)]
    pub(crate) fn param_quick(&mut self, s: &'static str) -> LevelPtr<'t> {
        let n = self.str1(&s);
        self.param(n)
    }
}

#[test]
fn check_empty() -> Result<(), Box<dyn Error>> {
    test_export_file(None, |export| {
        for declar in export.declars.values() {
            export.check_declar(declar);
        }
    })
}

#[test]
#[should_panic(expected = "infer_proj prop")]
fn check_proj_from_prop() {
    test_export_file_should_panic(
        Some(Path::new("test_resources/ProjFromProp/config.json")),
        |export| {
            for declar in export.declars.values() {
                export.check_declar(declar);
            }
        },
    )
}

#[test]
fn projection_type_name_participates_in_def_eq() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(Path::new("test_resources/ProjectionIdentity/config.json")), |export| {
        export.with_tc(EnvLimit::PpUnlimited, |tc| {
            let pprod = tc.ctx.str1("PProd");
            let other = tc.ctx.str1("Other");
            let binder = tc.ctx.str1("p");
            let one = tc.ctx.succ(tc.ctx.zero());
            let levels = tc.ctx.alloc_levels_slice(&[one, one]);
            let field_type = tc.ctx.mk_sort(one);
            let pprod_type = tc.ctx.mk_const(pprod, levels);
            let pprod_type = tc.ctx.mk_app(pprod_type, field_type);
            let pprod_type = tc.ctx.mk_app(pprod_type, field_type);
            let structure = tc.ctx.mk_dbj_level(binder, BinderStyle::Default, pprod_type);

            let left = tc.ctx.mk_proj(pprod, 0, structure);
            let same = tc.ctx.mk_proj(pprod, 0, structure);
            let other_index = tc.ctx.mk_proj(pprod, 1, structure);
            let other_type = tc.ctx.mk_proj(other, 0, structure);

            assert!(tc.def_eq(left, same));
            assert!(!tc.def_eq(left, other_index));
            assert!(!tc.def_eq(left, other_type));
        })
    })
}

pub(crate) fn rand_string<'t>(rng: &mut ThreadRng, size: usize) -> CowStr<'t> {
    use rand::RngExt;
    let rand_string: String = rng.sample_iter(&Alphanumeric).take(size).map(char::from).collect();
    CowStr::Owned(rand_string)
}

#[test]
fn hash_test0() -> Result<(), Box<dyn Error>> {
    use crate::hash64;
    use num_bigint::BigRng010;
    test_export_file(None, |export| {
        let mut rng = rand::rng();
        export.with_ctx(|ctx| {
            for size in 0..100 {
                for _ in 0..100 {
                    let s = rand_string(&mut rng, size);
                    let (l, r) = (ctx.mk_string_lit_quick(s.clone()), ctx.mk_string_lit_quick(s));
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
                for _ in 0..100 {
                    let s = rng.random_biguint(size as u64);
                    let (l, r) = (ctx.mk_nat_lit_quick(s.clone()), ctx.mk_nat_lit_quick(s));
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
            }
        })
    })
}
