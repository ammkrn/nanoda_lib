use crate::utils::{ Live, List,};
use crate::name::{ Name, Name::* };
use crate::level::{ Level::*, LevelsPtr, Level };
use crate::expr::{ ExprPtr, BinderStyle, BinderStyle::* };
use crate::env::Declar::*;
use crate::{ app, param, arrow, fold_pis, name, sort };
use crate::trace::IsTracer;
use crate::trace::steps::*;

pub fn add_quot<'l, 'e : 'l>(live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
    let prop = Zero.alloc(live).new_sort(live);
    let sort_u = sort!("u", live);
    let sort_v = sort!("v", live);
    let quot_name = name!("quot", live.env);
    let quot_mk_name = name!(["quot", "mk"], live.env);
    let quot_lift_name = name!(["quot", "lift"], live.env);
    let quot_ind_name = name!(["quot", "ind"], live.env);

    // local for `{A : Sort u}`
    let A = <ExprPtr>::new_local(name!("A", live), sort_u, Implicit, live);
    // local for `{B : Sort v}`
    let B = <ExprPtr>::new_local(name!("B", live), sort_v, Implicit, live);
    // local for `(r : A -> A -> Sort u)`
    let r = <ExprPtr>::new_local(name!("r", live), arrow!([A, A, prop], live), Default, live);
    // local for `(f : A -> B)`
    let f = <ExprPtr>::new_local(name!("f", live), arrow!([A, B], live), Default, live);
    // local for `(a1 : A)`
    let a = <ExprPtr>::new_local(name!("a", live), A, Default, live);
    // local for `(b : A)`
    let b = <ExprPtr>::new_local(name!("b", live), A, Default, live);    

    // quot : Π {A : Sort u}, (A → A → Prop) → Sort u
    let quot = Quot {
        name : quot_name,
        uparams : param!(["u"], live),
        type_ : fold_pis!([A, r, sort_u], live),
    };    
    
    let quot_const = <ExprPtr>::new_const(quot.name(), quot.uparams(), live);

    // `@quot A r`; gets used frequently hereafter
    let quot_A_r = app!([quot_const, A, r], live);

    // quot.mk : Π {A : Sort u} (r : A → A → Prop), A → @quot A r
    let quot_mk = Quot {
        name : quot_mk_name,
        uparams : param!(["u"], live),
        type_ : fold_pis!([A, r, arrow!([A, quot_A_r], live)], live)
    };

    let quot_mk_const = <ExprPtr>::new_const(quot_mk.name(), quot_mk.uparams(), live);
    let eq_const = <ExprPtr>::new_const(name!("eq", live), param!(["v"], live), live);

    // @eq B (f a) = (f b)
    let eq_app = app!([eq_const, B, app!([f, a], live), app!([f, b], live)], live);

    // (∀ (a b : A), r a b → f a = f b) 
    let lift_inner = fold_pis!([a, b, arrow!([app!([r, a, b], live), eq_app], live)], live);


    // quot.lift : Π {A : Sort u} {r : A → A → Prop} {B : Sort v} (f : A → B),
    //   (∀ (a b : A), r a b → f a = f b) → @quot A r → B  
    let quot_lift = Quot {
        name : quot_lift_name,
        uparams : param!(["u", "v"], live),
        type_ : fold_pis!([A, r, B, f, arrow!([lift_inner, quot_A_r, B], live)], live)
    };

    // {B : @quot A r → Prop}
    let B_local = <ExprPtr>::new_local(name!("B", live), arrow!([quot_A_r, prop], live), Implicit, live);

    // (q : @quot A r)
    let q_local = <ExprPtr>::new_local(name!("q", live), quot_A_r, Default, live);

    // @quot.mk A r a
    let quot_mk_app = app!([quot_mk_const, A, r, a], live);

    // (∀ (a : A), B (@quot.mk A r a))
    let lhs = fold_pis!([a, app!([B_local, quot_mk_app], live)], live);
    //  ∀ (q : @quot A r), B q
    let rhs = fold_pis!([q_local, app!([B_local, q_local], live)], live);


    // quot.ind : ∀ {A : Sort u} {r : A → A → Prop} {B : @quot A r → Prop},
    //           (∀ (a : A), B (@quot.mk A r a)) → ∀ (q : @quot A r), B q    
    let quot_ind = Quot {
        name : quot_ind_name,
        uparams : param!(["u"], live),
        type_ : fold_pis!([A, r, B_local, arrow!([lhs, rhs], live)], live),
    };    

    let quot = quot.insert_env(live.env, &live.store);
    let quot_mk = quot_mk.insert_env(live.env, &live.store);
    let quot_lift = quot_lift.insert_env(live.env, &live.store);
    let quot_ind = quot_ind.insert_env(live.env, &live.store);

    live.env.quot_mk = Some(quot_mk_name);
    live.env.quot_lift = Some(quot_lift_name);
    live.env.quot_ind = Some(quot_ind_name);

    let quot_step = AdmitDeclar::Quot {
        env : live.last_admit(),
        n : quot.name(live),
        ups : quot.uparams(live),
        t : quot.type_(live),
        d : quot
    }.step_only(live);
    live.admit_declar(quot, quot_step);

    let quot_mk_step = AdmitDeclar::Quot {
        env : live.last_admit(),
        n : quot_mk.name(live),
        ups : quot_mk.uparams(live),
        t : quot_mk.type_(live),
        d : quot_mk
    }.step_only(live);
    live.admit_declar(quot_mk, quot_mk_step);

    let quot_lift_step = AdmitDeclar::Quot {
        env : live.last_admit(),
        n : quot_lift.name(live),
        ups : quot_lift.uparams(live),
        t : quot_lift.type_(live),
        d : quot_lift
    }.step_only(live);
    live.admit_declar(quot_lift, quot_lift_step);

    let quot_ind_step = AdmitDeclar::Quot {
        env : live.last_admit(),
        n : quot_ind.name(live),
        ups : quot_ind.uparams(live),
        t : quot_ind.type_(live),
        d : quot_ind
    }.step_only(live);
    live.admit_declar(quot_ind, quot_ind_step);

}

