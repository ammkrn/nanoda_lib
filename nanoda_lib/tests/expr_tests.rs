#![allow(unused_imports)]
#![allow(unused_variables)]
use nanoda_lib::utils::{ HasNanodaDbg, List,  List::*, Env };
use nanoda_lib::name::Name;
use nanoda_lib::level::{ LevelsPtr, Level };
use nanoda_lib::{ names, param, name, exprs, levels };
use nanoda_lib::trace::StdoutTracer;
use nanoda_lib::trace::items::HasPtrRepr;
use nanoda_lib::expr::{ Expr, ExprPtr, ExprsPtr, BinderStyle::* };

#[test]
fn expr_inst_test0() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let v0 = <ExprPtr>::new_var(0, &mut live);
    let v1 = <ExprPtr>::new_var(1, &mut live);

    let app = <ExprPtr>::new_app(v0, v1, &mut live);

    let sub = param!("u", &mut live).new_sort(&mut live);
    let subs = Cons(sub, Nil::<Expr>.alloc(&mut live)).alloc(&mut live);

    let target = <ExprPtr>::new_app(sub, v1, &mut live);

    let (subbed, _) = app.inst(subs, &mut live);
}

#[test]
fn expr_inst_test1() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();
    let b_name = name!("x", &mut live);
    let b_type = <ExprPtr>::new_const(
        name!("nat", &mut live), 
        levels!([], &mut live),
        &mut live
    );
    let b_style = Default;
    let v0 = <ExprPtr>::new_var(0, &mut live);
    let v1 = <ExprPtr>::new_var(1, &mut live);
    let lambda0 = <ExprPtr>::new_lambda(
        b_name,
        b_type,
        b_style,
        v0,
        &mut live
    );

    let lambda1 = <ExprPtr>::new_lambda(
        b_name,
        b_type,
        b_style,
        v1,
        &mut live
    );

    let sub = param!("u", &mut live).new_sort(&mut live);
    let subs = Cons(sub, Nil::<Expr>.alloc(&mut live)).alloc(&mut live);

    let target = <ExprPtr>::new_lambda(
        b_name,
        b_type,
        b_style,
        sub,
        &mut live
    );

    let (subbed0, _) = lambda0.inst(subs, &mut live);
    let (subbed1, _) = lambda1.inst(subs, &mut live);
    assert_eq!(lambda0, subbed0);
    assert_eq!(subbed1, target);
    assert_ne!(subbed0, subbed1);
}


#[test]
fn expr_fold_apps_test0() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();


    let base= <ExprPtr>::new_const(
        name!("nat", &mut live),
        levels!([], &mut live),
        &mut live
    );
    let v0 = <ExprPtr>::new_var(0, &mut live);
    let v1 = <ExprPtr>::new_var(1, &mut live);
    let v2 = <ExprPtr>::new_var(2, &mut live);

    let fold_target = base.new_app(v0, &mut live)
                     .new_app(v1, &mut live)
                     .new_app(v2, &mut live);

    let list = exprs!([v0, v1, v2], &mut live);

    let (folded, _) = base.foldl_apps(list, &mut live);
    let ((base2, args2), _) = folded.unfold_apps(&mut live);


    assert_eq!(folded, fold_target);

    assert_eq!(base, base2);
    assert_eq!(list, args2);
}


#[test]
fn expr_telescope_len_test0() {
    let mut env = Env::new(());
    let mut live = env.as_live();
    
    let base= <ExprPtr>::new_const(
        name!("nat", &mut live),
        levels!([], &mut live),
        &mut live
    );

    let (len, _) = base.telescope_size(&mut live);
    assert_eq!(len, 0);

}

#[test]
fn expr_telescope_len_test1() {
    let mut env = Env::new(());
    let mut live = env.as_live();
    let v0 = <ExprPtr>::new_var(0, &mut live);

    let b_n = name!("x", &mut live);
    let p1 = <ExprPtr>::new_pi(b_n, v0, Default, v0, &mut live);
    let p2 = <ExprPtr>::new_pi(b_n, p1, Implicit, p1, &mut live);
    let p3 = <ExprPtr>::new_pi(b_n, p2, StrictImplicit, p2, &mut live);
    let p4 = <ExprPtr>::new_pi(b_n, v0, InstImplicit, p3, &mut live);
    let (size, _) = p4.telescope_size(&mut live);

    assert_eq!(size, 4);
}

#[test]
fn expr_apply_pi_test0() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let n1 = name!("n1", &mut live);
    let n2 = name!("n2", &mut live);
    
    let cn1 = name!("cn1", &mut live);
    let cn2 = name!("cn2", &mut live);

    let bt_1 = <ExprPtr>::new_const(cn1, Nil::<Level>.alloc(&mut live), &mut live);
    let bt_2 = <ExprPtr>::new_const(cn2, Nil::<Level>.alloc(&mut live), &mut live);


    let local1 = <ExprPtr>::new_local(n1, bt_1, Implicit, &mut live);
    let local2 = <ExprPtr>::new_local(n2, bt_2, Implicit, &mut live);

    let body_app = local1.new_app(local1, &mut live);

    let v = <ExprPtr>::new_var(0, &mut live);

    // Pi {n1 : Const cn1 []}, App (v0) (v0)
    let target = <ExprPtr>::new_pi(n1, bt_1, Implicit, v.new_app(v, &mut live), &mut live);

    let (applied, _) = local1.apply_pi(body_app, &mut live);

    assert_eq!(target, applied);
}


#[test]
fn expr_fold_lambda_test0() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let n1 = name!("n1", &mut live);
    let n2 = name!("n2", &mut live);
    
    let cn1 = name!("cn1", &mut live);
    let cn2 = name!("cn2", &mut live);

    let bt_1 = <ExprPtr>::new_const(cn1, Nil::<Level>.alloc(&mut live), &mut live);
    let bt_2 = <ExprPtr>::new_const(cn2, Nil::<Level>.alloc(&mut live), &mut live);


    let local1 = <ExprPtr>::new_local(n1, bt_1, Implicit, &mut live);
    let local2 = <ExprPtr>::new_local(n2, bt_2, Implicit, &mut live);
    let body_app = local1.new_app(local2, &mut live);

    let doms = exprs!([local1, local2], &mut live);



    let v = <ExprPtr>::new_var(0, &mut live);
    let target_app = <ExprPtr>::new_app(<ExprPtr>::new_var(1, &mut live), <ExprPtr>::new_var(0, &mut live), &mut live);
    let target_1 = <ExprPtr>::new_lambda(n2, bt_2, Implicit, target_app, &mut live);
    let target = <ExprPtr>::new_lambda(n1, bt_1, Implicit, target_1, &mut live);


    let (folded, _) = doms.fold_lambdas(body_app, &mut live);
    assert_eq!(folded, target);    
}


#[test]
fn expr_fold_pi_test0() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let n1 = name!("n1", &mut live);
    let n2 = name!("n2", &mut live);
    
    let cn1 = name!("cn1", &mut live);
    let cn2 = name!("cn2", &mut live);

    let bt_1 = <ExprPtr>::new_const(cn1, Nil::<Level>.alloc(&mut live), &mut live);
    let bt_2 = <ExprPtr>::new_const(cn2, Nil::<Level>.alloc(&mut live), &mut live);


    let local1 = <ExprPtr>::new_local(n1, bt_1, Implicit, &mut live);
    let local2 = <ExprPtr>::new_local(n2, bt_2, Implicit, &mut live);
    let body_app = local1.new_app(local2, &mut live);

    let doms = exprs!([local1, local2], &mut live);



    let v = <ExprPtr>::new_var(0, &mut live);
    let target_app = <ExprPtr>::new_app(<ExprPtr>::new_var(1, &mut live), <ExprPtr>::new_var(0, &mut live), &mut live);
    let target_1 = <ExprPtr>::new_pi(n2, bt_2, Implicit, target_app, &mut live);
    let target = <ExprPtr>::new_pi(n1, bt_1, Implicit, target_1, &mut live);


    let (folded, _) = doms.fold_pis(body_app, &mut live);
    assert_eq!(folded, target);
}


#[test]
fn has_ind_occ_test0() {
    let mut env = Env::new(());
    let mut live = env.as_live();

    let ind_n1 = name!("ind_type1", &mut live);
    let ind_n2 = name!("ind_type2", &mut live);
    let ind_names = names!([ind_n1, ind_n2], &mut live);

    let has_none = <ExprPtr>::new_const(name!("nat", &mut live), levels!([], &mut live), &mut live);
    let app = has_none.new_app(has_none, &mut live);
    let (checked, _) = app.has_ind_occ(ind_names, &mut live);
    assert!(!checked);    
}

#[test]
fn has_ind_occ_test1() {
    let mut env = Env::new(());
    let mut live = env.as_live();

    let ind_n1 = name!("ind_type1", &mut live);
    let ind_n2 = name!("ind_type2", &mut live);
    let ind_names = names!([ind_n1, ind_n2], &mut live);

    let has_none = <ExprPtr>::new_const(name!("ind_type2", &mut live), levels!([], &mut live), &mut live);
    let app = has_none.new_app(has_none, &mut live);
    let (checked, _) = app.has_ind_occ(ind_names, &mut live);
    assert!(checked);    
}


#[test]
fn local_counter_test0() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();
    
    let b_n = name!("x", &mut live);
    let b_t = param!("u", &mut live).new_sort(&mut live);
    let local1 = <ExprPtr>::new_local(b_n, b_t, Default, &mut live);
    let local2 = <ExprPtr>::new_local(b_n, b_t, Default, &mut live);
    assert_ne!(local1, local2);
    assert_ne!(local1.local_serial_infal(&live), local2.local_serial_infal(&live));
}