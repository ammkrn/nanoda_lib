use crate::env::EnvLimit;
use crate::expr::BinderStyle::{Default, Implicit};
use crate::tests::util::test_ctx;
use std::error::Error;

#[test]
fn alpha_eq_binders_and_scope() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let x = ctx.str1("x");
        let y = ctx.str1("y");
        let prop = ctx.mk_sort(ctx.zero());
        let v0 = ctx.mk_var(0);
        let v1 = ctx.mk_var(1);
        let inner_x = ctx.mk_lambda(x, Default, prop, v1);
        let inner_y = ctx.mk_lambda(y, Implicit, prop, v1);
        let lhs = ctx.mk_lambda(x, Default, prop, inner_x);
        let rhs = ctx.mk_lambda(y, Implicit, prop, inner_y);
        assert_ne!(lhs, rhs);
        assert!(ctx.alpha_eq(lhs, rhs));

        let wrong_scope = ctx.mk_lambda(y, Implicit, prop, v0);
        let wrong_scope = ctx.mk_lambda(y, Implicit, prop, wrong_scope);
        assert!(!ctx.alpha_eq(lhs, wrong_scope));

        let pi_x = ctx.mk_pi(x, Default, prop, prop);
        let pi_y = ctx.mk_pi(y, Implicit, prop, prop);
        assert!(ctx.alpha_eq(pi_x, pi_y));
        assert!(!ctx.alpha_eq(pi_x, lhs));
        let let_x = ctx.mk_let(x, prop, v0, v0, false);
        let let_y = ctx.mk_let(y, prop, v0, v0, false);
        assert!(ctx.alpha_eq(let_x, let_y));
        let different_value = ctx.mk_let(y, prop, v1, v0, false);
        assert!(!ctx.alpha_eq(let_x, different_value));
    })
}

#[test]
fn alpha_eq_preserves_semantic_fields() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let x = ctx.str1("x");
        let y = ctx.str1("y");
        let zero = ctx.zero();
        let one = ctx.succ(zero);
        let prop = ctx.mk_sort(zero);
        let ty = ctx.mk_sort(one);
        let v0 = ctx.mk_var(0);
        let lhs = ctx.mk_lambda(x, Default, prop, v0);
        let rhs = ctx.mk_lambda(y, Default, ty, v0);
        assert!(!ctx.alpha_eq(lhs, rhs));

        let us = ctx.alloc_levels_slice(&[zero]);
        let vs = ctx.alloc_levels_slice(&[one]);
        let cx = ctx.mk_const(x, us);
        let cy = ctx.mk_const(y, us);
        let cu = ctx.mk_const(x, vs);
        assert!(!ctx.alpha_eq(cx, cy));
        assert!(!ctx.alpha_eq(cx, cu));
        let px = ctx.mk_proj(x, 0, v0);
        let py = ctx.mk_proj(y, 0, v0);
        let pi = ctx.mk_proj(x, 1, v0);
        assert!(!ctx.alpha_eq(px, py));
        assert!(!ctx.alpha_eq(px, pi));

        let local_x = ctx.mk_dbj_level(x, Default, prop);
        ctx.dbj_level_counter = 0;
        let renamed = ctx.mk_dbj_level(y, Implicit, prop);
        assert!(ctx.alpha_eq(local_x, renamed));
        let fresh = ctx.mk_dbj_level(y, Implicit, prop);
        assert!(!ctx.alpha_eq(local_x, fresh));
        ctx.dbj_level_counter = 0;
        let retyped = ctx.mk_dbj_level(x, Default, ty);
        assert!(!ctx.alpha_eq(local_x, retyped));
    })
}

#[test]
fn alpha_eq_deep_shared_dag() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let x = ctx.str1("x");
        let y = ctx.str1("y");
        let prop = ctx.mk_sort(ctx.zero());
        let v0 = ctx.mk_var(0);
        let mut lhs = ctx.mk_lambda(x, Default, prop, v0);
        let mut rhs = ctx.mk_lambda(y, Default, prop, v0);
        // A structural comparison must visit DAG nodes, not expand the
        // exponentially larger trees they represent, or recurse on the stack.
        for _ in 0..10_000 {
            lhs = ctx.mk_app(lhs, lhs);
            rhs = ctx.mk_app(rhs, rhs);
        }
        assert!(ctx.alpha_eq(lhs, rhs));
    })
}

#[test]
fn def_eq_alpha_before_reduction() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let x = ctx.str1("x");
        let y = ctx.str1("y");
        let prop = ctx.mk_sort(ctx.zero());
        let one = ctx.succ(ctx.zero());
        let ty = ctx.mk_sort(one);
        let v0 = ctx.mk_var(0);
        let id_x = ctx.mk_lambda(x, Default, ty, v0);
        let id_y = ctx.mk_lambda(y, Default, ty, v0);
        let (mut lhs, mut rhs) = (prop, prop);
        // Both terms are well typed and alpha-equivalent. Normalizing these
        // long beta-reduction chains first needlessly consumes the stack.
        for _ in 0..10_000 {
            lhs = ctx.mk_app(id_x, lhs);
            rhs = ctx.mk_app(id_y, rhs);
        }
        ctx.with_tc(EnvLimit::Empty, |tc| assert!(tc.def_eq(lhs, rhs)));
    })
}
