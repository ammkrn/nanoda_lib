//! Construction of quotient types

use crate::env::{ConstructorData, Declar, DeclarInfo, InductiveData, EnvLimit};
use crate::expr::{BinderStyle, BinderStyle::*};
use crate::tc::TypeChecker;
use crate::util::TcCtx;

/// From `in ctx, [a, b, c, .., n]`, create `app(app(app(a, b), c).. n)`
#[macro_export]
macro_rules! app {
    ( in $ctx:expr; $fun:expr, $arg:expr ) => {
        {
            $ctx.mk_app($fun, $arg)
        }
    };
    ( in $ctx:expr; $fun:expr, $arg:expr, $($tl:expr),*) => {
        {
            let mut base = $ctx.mk_app($fun, $arg);
            $(
                base = $ctx.mk_app(base, $tl);
            )*
            base
        }
    }
}

/// Create a pi telescope from a list of binders and a body, but...\
/// 1. Do not perform abstraction, because the binders are not `Local`s.
/// 2. Use anonymous binder names
#[macro_export]
macro_rules! arrow {
    ( in $ctx:expr; $dom:expr, $body:expr ) => {
        {
            let anon = $ctx.anonymous();
            $ctx.mk_pi(anon, BinderStyle::Default, $dom, $body)
        }
    };
    ( in $ctx:expr; $dom:expr, $($tl:expr),* ) => {
        {
            let anon = $ctx.anonymous();
            let inner = arrow!(in $ctx; $($tl),*);
            $ctx.mk_pi(anon, BinderStyle::Default, $dom, inner)
        }
    }
}

/// Create a pi telescope from a list of binders and a body, and perform
/// abstraction (re-binding any free variables in the body to suit the pi telescope
/// being constructed).
#[macro_export]
macro_rules! pi_telescope {
    ( in $ctx:expr; $body:expr ) => {
        { $body }
    };
    ( in $ctx:expr; $ty:expr, $($tl:expr),*) => {

        {
            let inner = pi_telescope!(in $ctx; $($tl),*);
            $ctx.abstr_pi($ty, inner)
        }
    }
}

/// The `Quot` declarations rely on `Eq` being defined as it is in
/// the prelude, so a prereq for checking the `Quot` declarations is asserting
/// that a propery constructed `Eq` and `Eq.refl`
pub fn check_eq<'x, 't: 'x, 'p: 't>(ctx: &'x mut TcCtx<'t, 'p>, declar: &Declar<'p>) {
    use crate::expr::BinderStyle::*;
    let name = ctx.str1("Eq");
    let cname = ctx.str2("Eq", "refl");
    let alpha_name = ctx.str1("α");
    let a_name = ctx.str1("a");
    let prop = ctx.prop();
    let env = ctx.export_file.new_env(EnvLimit::ByName(declar.info().name));
    match env.get_inductive(&name).cloned() {
        // The `Eq` declaration offered up by the export file;
        Some(InductiveData { info, num_params, all_ctor_names, .. }) => {
            let eq_const = ctx.mk_const(name, info.uparams);
            assert_eq!(ctx.read_levels(info.uparams).len(), 1);
            assert_eq!(num_params, 2);
            let uparam = match ctx.read_levels(info.uparams).as_ref() {
                &[u] => ctx.mk_sort(u),
                owise => panic!("Bad `Eq` type; inductive `Eq` is expected to have 1 uparam, found {}", owise.len()),
            };
            let alpha = ctx.mk_unique(alpha_name, Implicit, uparam);
            let inner = arrow!(in ctx; alpha, alpha, prop);
            let expected = pi_telescope!(in ctx; alpha, inner);
            let mut tc = TypeChecker::new(ctx, &env, Some(info));
            tc.assert_def_eq(info.ty, expected);
            match all_ctor_names.as_ref() {
                &[ctor_name] => {
                    assert_eq!(cname, ctor_name);
                    match env.get_constructor(&ctor_name) {
                        Some(ConstructorData { info, .. }) => {
                            let uparam_sort = match ctx.read_levels(info.uparams).as_ref() {
                                &[uparam] => ctx.mk_sort(uparam),
                                _ => panic!(),
                            };
                            let alpha = ctx.mk_unique(alpha_name, Implicit, uparam_sort);
                            let a = ctx.mk_unique(a_name, Default, alpha);

                            let app = app!(in ctx; eq_const, alpha, a, a);
                            let expected = pi_telescope!(in ctx; alpha, a, app);
                            let mut tc = TypeChecker::new(ctx, &env, Some(*info));
                            tc.assert_def_eq(info.ty, expected);
                        }
                        None => panic!(
                            "cannot add Quot; constructor `Eq.refl` was expected, but not found in the environment"
                        ),
                    }
                }
                owise => panic!(
                    "cannot add Quot; `Eq` type improperly formed; expected one constructor, found {}",
                    owise.len()
                ),
            }
        }
        None => panic!("cannot add Quot; improperly formed `Eq` type := {:?} ", ctx.debug_print(declar.info().name)),
    }
}

#[allow(non_snake_case)]
pub fn check_quot<'x, 't: 'x, 'p: 't>(ctx: &'x mut TcCtx<'t, 'p>, declar: &Declar<'p>) {
    // `Eq` matching expectations is a prerequisite for checking `Quot`.
    let prop = ctx.prop();
    let u_name = ctx.str1("u");
    let v_name = ctx.str1("v");
    let q_name = ctx.str1("q");
    let u_level = ctx.param(u_name);
    let v_level = ctx.param(v_name);
    let sort_u = ctx.mk_sort(u_level);
    let sort_v = ctx.mk_sort(v_level);

    let levels_u = ctx.alloc_levels_slice(&[u_level]);
    let levels_v = ctx.alloc_levels_slice(&[v_level]);
    let levels_uv = ctx.alloc_levels_slice(&[u_level, v_level]);
    let quot_name = ctx.export_file.name_cache.quot.unwrap();
    let quot_mk_name = ctx.export_file.name_cache.quot_mk.unwrap();

    let A_name = ctx.str1("A");
    let B_name = ctx.str1("B");
    let r_name = ctx.str1("r");
    let f_name = ctx.str1("f");
    let a_name = ctx.str1("a");
    let b_name = ctx.str1("b");

    // local for `{A : Sort u}`
    let A = ctx.mk_unique(A_name, Implicit, sort_u);
    // local for `{B : Sort v}`
    let B = ctx.mk_unique(B_name, Implicit, sort_v);
    let A_A_Prop = arrow!(in ctx; A, A, prop);
    let A_B = arrow!(in ctx; A, B);
    // local for `(r : A -> A -> Prop)`
    let r = ctx.mk_unique(r_name, Default, A_A_Prop);
    // local for `(f : A -> B)`
    let f = ctx.mk_unique(f_name, Default, A_B);
    // local for `(a1 : A)`
    let a = ctx.mk_unique(a_name, Default, A);
    // local for `(b : A)`
    let b = ctx.mk_unique(b_name, Default, A);

    // Quot : Π {A : Sort u}, (A → A → Prop) → Sort u
    let expected_quot = Declar::Quot {
        info: DeclarInfo { name: quot_name, uparams: levels_u, ty: pi_telescope!(in ctx; A, r, sort_u) },
    };
    let quot_const = ctx.mk_const(expected_quot.info().name, levels_u);
    let quot_A_r = app!(in ctx; quot_const, A, r);

    // Quot.mk : Π {A : Sort u} (r : A → A → Prop), A → @Quot A r
    let expected_quot_mk = Declar::Quot {
        info: DeclarInfo {
            name: quot_mk_name,
            uparams: levels_u,
            ty: pi_telescope! {
                in ctx;
                A,
                r,
                arrow!(in ctx; A, quot_A_r)
            },
        },
    };

    let quot_mk_const = ctx.mk_const(expected_quot_mk.info().name, levels_u);
    let eq_name = ctx.str1("Eq");
    let eq_const = ctx.mk_const(eq_name, levels_v);

    let fa = app!(in ctx; f, a);
    let fb = app!(in ctx; f, b);
    // @eq B (f a) = (f b)
    let eq_app = app!(in ctx; eq_const, B, fa, fb);
    let rab = app!(in ctx; r, a, b);

    // (∀ (a b : A), r a b → f a = f b)
    let lift_inner = pi_telescope! {
        in ctx;
        a,
        b,
        arrow! {
            in ctx;
            rab,
            eq_app
        }
    };

    if declar.info().name == ctx.str1("Quot") {
        let env = ctx.export_file.new_env(EnvLimit::ByName(quot_name));
        let mut tc = TypeChecker::new(ctx, &env, Some(*declar.info()));
        tc.assert_def_eq(declar.info().ty, expected_quot.info().ty);
    } else if declar.info().name == ctx.str2("Quot", "mk") {
        let env = ctx.export_file.new_env(EnvLimit::ByName(quot_mk_name));
        let mut tc = TypeChecker::new(ctx, &env, Some(*declar.info()));
        tc.assert_def_eq(declar.info().ty, expected_quot_mk.info().ty);
    } else if declar.info().name == ctx.str2("Quot", "lift") {
        check_eq(ctx, declar);
        // Quot.lift : Π {A : Sort u} {r : A → A → Prop} {B : Sort v} (f : A → B),
        //   (∀ (a b : A), r a b → f a = f b) → @Quot A r → B
        let expected_quot_lift = Declar::Quot {
            info: DeclarInfo {
                name: declar.info().name,
                uparams: levels_uv,
                ty: pi_telescope! {
                    in ctx;
                    A,
                    r,
                    B,
                    f,
                    arrow! {
                        in ctx;
                        lift_inner,
                        quot_A_r,
                        B
                    }
                },
            },
        };
        let env = ctx.export_file.new_env(EnvLimit::ByName(declar.info().name));
        let mut tc = TypeChecker::new(ctx, &env, Some(*declar.info()));
        tc.assert_def_eq(declar.info().ty, expected_quot_lift.info().ty);
        return
    } else if declar.info().name == ctx.str2("Quot", "ind") {
        // {B : @Quot A r → Prop}
        let quot_A_r_prop = arrow!(in ctx; quot_A_r, prop);

        let B_local = ctx.mk_unique(B_name, Implicit, quot_A_r_prop);

        // (q : @Quot A r)
        let q_local = ctx.mk_unique(q_name, Default, quot_A_r);

        // @Quot.mk A r a
        let quot_mk_app = app!(in ctx; quot_mk_const, A, r, a);

        // (∀ (a : A), B (@Quot.mk A r a))
        let lhs = pi_telescope!(in ctx; a, app!(in ctx; B_local, quot_mk_app));
        //  ∀ (q : @Quot A r), B q
        let rhs = pi_telescope!(in ctx; q_local, app!(in ctx; B_local, q_local));

        // Quot.ind : ∀ {A : Sort u} {r : A → A → Prop} {B : @Quot A r → Prop},
        //           (∀ (a : A), B (@Quot.mk A r a)) → ∀ (q : @Quot A r), B q
        let expected_quot_ind = Declar::Quot {
            info: DeclarInfo {
                name: declar.info().name,
                uparams: levels_u,
                ty: pi_telescope!(in ctx; A, r, B_local, arrow!(in ctx; lhs, rhs)),
            },
        };

        let env = ctx.export_file.new_env(EnvLimit::ByName(declar.info().name));
        let mut tc = TypeChecker::new(ctx, &env, Some(*declar.info()));
        tc.assert_def_eq(declar.info().ty, expected_quot_ind.info().ty);
        return
    } else {
        panic!("invalid quotient declaration {:?}", ctx.debug_print(declar.info().name))
    }
}
