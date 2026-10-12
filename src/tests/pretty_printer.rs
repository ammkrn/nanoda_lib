use crate::expr::BinderStyle::{self, Default, Implicit};
use crate::tests::util::test_get_export_file;
use std::error::Error;

fn render_binders(is_pi: bool, binders: &[(&'static str, u64, BinderStyle)]) -> Result<String, Box<dyn Error>> {
    let (mut export, _) = test_get_export_file(None)?;
    export.config.pp_options.proofs = true;
    Ok(export.with_ctx(|ctx| {
        let mut body = ctx.mk_sort(ctx.zero());
        for &(name, level, style) in binders.iter().rev() {
            let name = ctx.str1(name);
            let level = ctx.level_n(ctx.zero(), level);
            let ty = ctx.mk_sort(level);
            body = if is_pi { ctx.mk_pi(name, style, ty, body) } else { ctx.mk_lambda(name, style, ty, body) };
        }
        ctx.with_pp(|pp| pp.pp_expr(body))
    }))
}

#[test]
fn forall_does_not_group_nonconsecutive_types() -> Result<(), Box<dyn Error>> {
    let actual =
        render_binders(true, &[("a", 1, Implicit), ("b", 0, Implicit), ("c", 1, Implicit), ("d", 1, Implicit)])?;
    assert_eq!(actual, "forall {a : Type 0} {b : Prop} {c d : Type 0}, Prop");
    Ok(())
}

#[test]
fn lambda_does_not_group_nonconsecutive_types() -> Result<(), Box<dyn Error>> {
    let actual = render_binders(false, &[("a", 1, Default), ("b", 0, Default), ("c", 1, Default), ("d", 1, Default)])?;
    assert_eq!(actual, "fun (a : Type 0) (b : Prop) (c d : Type 0) => Prop");
    Ok(())
}

#[test]
fn forall_does_not_group_nonconsecutive_styles() -> Result<(), Box<dyn Error>> {
    use crate::expr::BinderStyle::StrictImplicit;
    let actual =
        render_binders(true, &[("a", 1, Implicit), ("b", 1, StrictImplicit), ("c", 1, Implicit), ("d", 1, Implicit)])?;
    assert_eq!(actual, "forall {a : Type 0} {{b : Type 0}} {c d : Type 0}, Prop");
    Ok(())
}

#[test]
fn lambda_does_not_group_nonconsecutive_styles() -> Result<(), Box<dyn Error>> {
    let actual = render_binders(false, &[("a", 1, Default), ("b", 1, Implicit), ("c", 1, Default), ("d", 1, Default)])?;
    assert_eq!(actual, "fun (a : Type 0) {b : Type 0} (c d : Type 0) => Prop");
    Ok(())
}
