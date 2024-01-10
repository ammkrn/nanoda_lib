use crate::expr::Expr::*;
use crate::tests::util::{rand_string, test_export_file};
use crate::util::{CowStr, ExportFile, ExprPtr, StringPtr, TcCtx};
use rand::{rngs::ThreadRng, thread_rng};
use std::error::Error;
use std::path::Path;

#[test]
fn string_lit_tests() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Init/config.json")), |export_file| {
        let mut rng = thread_rng();
        string_lit_conversion0(export_file, &mut rng);
        string_lit_def_eq_apps(export_file, &mut rng);
        string_lit_not_def_eq(export_file, &mut rng);
        string_lit_not_def_eq_apps(export_file, &mut rng);
    })
}

/// Converting a string literal to `String.mk (List.cons (Char.ofNat N) ... List.nil)`
/// and converting that back to a string literal returns the original string literal.
fn string_lit_conversion0(export_file: &ExportFile, rng: &mut ThreadRng) {
    export_file.with_tc(|tc| {
        for _ in 0..100 {
            for size in 0..100 {
                let string_ptr = tc.ctx.alloc_string(rand_string(rng, size));
                let as_expr = tc.ctx.str_lit_to_constructor(string_ptr).unwrap();
                assert_eq!(Some(string_ptr), tc.ctx.str_lit_from_app_str(as_expr))
            }
        }
    })
}

/// Converting a string literal to `String.mk (List.cons (Char.ofNat N) ... List.nil)`
/// creates an expression that is definitionally equal to the string literal.
fn string_lit_def_eq_apps(export_file: &ExportFile, rng: &mut ThreadRng) {
    export_file.with_tc(|tc| {
        for size in 0..100 {
            for _ in 0..100 {
                let string_ptr = tc.ctx.alloc_string(rand_string(rng, size));
                let stringlit = tc.ctx.mk_string_lit(string_ptr);
                let as_expr = tc.ctx.str_lit_to_constructor(string_ptr).unwrap();
                tc.tc_cache.clear();
                assert!(tc.def_eq(stringlit, as_expr));
            }
        }
    })
}

/// For any two string literals, if they are not equal, the definitional
/// equality procedure returns !def_eq
fn string_lit_not_def_eq(export_file: &ExportFile, rng: &mut ThreadRng) {
    export_file.with_tc(|tc| {
        for size in 1..100 {
            let mut iteration = 0;
            while iteration < 100 {
                let s1 = rand_string(rng, size);
                let s2 = rand_string(rng, size);
                if s1 == s2 {
                    continue
                } else {
                    iteration += 1;
                }
                let stringlit1 = tc.ctx.mk_string_lit_quick(s1);
                let stringlit2 = tc.ctx.mk_string_lit_quick(s2);
                tc.tc_cache.clear();
                assert!(!tc.def_eq(stringlit1, stringlit2));
            }
        }
    })
}

/// For any two string literals converted to char lists, if the strings
/// are not equal, the converted lists are not equal.
fn string_lit_not_def_eq_apps(export_file: &ExportFile, rng: &mut ThreadRng) {
    export_file.with_tc(|tc| {
        for size in 1..10 {
            let mut iteration = 0;
            while iteration < 100 {
                let s1 = rand_string(rng, size);
                let s2 = rand_string(rng, size);
                if s1 == s2 {
                    continue
                } else {
                    iteration += 1;
                }
                let string_ptr1 = tc.ctx.alloc_string(s1);
                let string_ptr2 = tc.ctx.alloc_string(s2);
                let e1 = tc.ctx.str_lit_to_constructor(string_ptr1).unwrap();
                let e2 = tc.ctx.str_lit_to_constructor(string_ptr2).unwrap();
                tc.tc_cache.clear();
                assert!(!tc.def_eq(e1, e2));
            }
        }
    })
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    fn unfold_apps_r(&self, mut e: ExprPtr<'t>) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        while let App { fun, arg, .. } = self.read_expr(e) {
            out.push(fun);
            e = arg;
        }
        out.push(e);
        out
    }

    fn char_from_char_of_nat(&mut self, e: ExprPtr<'t>) -> Option<char> {
        let zero = self.zero();
        let empty_levels = self.alloc_levels_slice(&[]);
        let tyzero_levels = self.alloc_levels_slice(&[zero]);
        let c_char = self.mk_const(self.export_file.name_cache.char?, empty_levels);
        let c_list_cons_char = {
            let f = self.mk_const(self.export_file.name_cache.list_cons?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        let c_char_of_nat = self.mk_const(self.export_file.name_cache.char_of_nat?, empty_levels);

        // Each element has to be `App(List.cons, (Char.ofNat n))`
        match self.read_expr(e) {
            App { fun, arg, .. } if fun == c_list_cons_char => match self.read_expr(arg) {
                App { fun, arg, .. } if fun == c_char_of_nat => match self.read_expr(arg) {
                    NatLit { ptr, .. } => {
                        let n = u32::try_from(self.read_bignum(ptr)).unwrap();
                        return char::from_u32(n)
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    fn str_lit_from_app_str(&mut self, e: ExprPtr<'t>) -> Option<StringPtr<'t>> {
        let fs = self.unfold_apps_r(e);
        match fs.as_slice() {
            [string_mk, char_conses @ .., nil_f, char_arg] => {
                let zero = self.zero();
                let empty_levels = self.alloc_levels_slice(&[]);
                let tyzero_levels = self.alloc_levels_slice(&[zero]);
                let c_char = self.mk_const(self.export_file.name_cache.char?, empty_levels);

                // @List.nil.{0}
                let list_nil = self.mk_const(self.export_file.name_cache.list_nil?, tyzero_levels);
                let string_mk_const = self.mk_const(self.export_file.name_cache.string_mk?, empty_levels);
                // The top must be an application of `String.mk`
                if *string_mk != string_mk_const {
                    return None
                }
                // The end of the spine must be `App(List.nil, Char)`
                if (*nil_f != list_nil) || (*char_arg != c_char) {
                    return None
                }
                let mut out = String::new();
                for cons_expr in char_conses {
                    out.push(self.char_from_char_of_nat(*cons_expr)?)
                }
                return Some(self.alloc_string(CowStr::Owned(out)))
            }
            _ => None,
        }
    }
}
