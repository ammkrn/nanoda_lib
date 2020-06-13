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
fn reduce_lambda_test0() {
    let mut env = Env::new(());
    let mut live = env.as_live();
    let mut tc = live.as_tc(None, None);

    let v0 = <ExprPtr>::new_var(0, &mut tc);

    let cn1 = name!("const_name1", &mut tc);
    let cn2 = name!("const_name2", &mut tc);
    let const1 = <ExprPtr>::new_const(cn1, param!(["a"], &mut tc), &mut tc);
    let const2 = <ExprPtr>::new_const(cn2, param!(["b"], &mut tc), &mut tc);

    let lam1 = <ExprPtr>::new_lambda(name!("x", &mut tc), const1, Default, v0, &mut tc);

    let (reduced, _) = lam1.whnf_lambda(exprs!([const2], &mut tc), exprs!([], &mut tc), &mut tc);
    assert_eq!(reduced, const2);
}

#[test]
fn reduce_lambda_test1() {
    let mut env = Env::new(());
    let mut live = env.as_live();
    let mut tc = live.as_tc(None, None);

    let v0 = <ExprPtr>::new_var(0, &mut tc);
    let v1 = <ExprPtr>::new_var(1, &mut tc);
    let v2 = <ExprPtr>::new_var(2, &mut tc);

    let cn1 = name!("const_name1", &mut tc);
    let cn2 = name!("const_name2", &mut tc);
    let cn3 = name!("const_name3", &mut tc);
    let const1 = <ExprPtr>::new_const(cn1, param!(["c"], &mut tc), &mut tc);
    let const2 = <ExprPtr>::new_const(cn2, param!(["b"], &mut tc), &mut tc);
    let const3 = <ExprPtr>::new_const(cn3, param!(["a"], &mut tc), &mut tc);

    let inner = v0.new_app(v1, &mut tc).new_app(v2, &mut tc);
    let lam1 = <ExprPtr>::new_lambda(name!("z", &mut tc), const1, Default, inner, &mut tc);
    let lam2 = <ExprPtr>::new_lambda(name!("y", &mut tc), const2, Default, lam1, &mut tc);
    let lam3 = <ExprPtr>::new_lambda(name!("x", &mut tc), const3, Default, lam2, &mut tc);

    let target = const1.new_app(const2, &mut tc).new_app(const3, &mut tc);

    let args = exprs!([const3, const2, const1], &mut tc);

    let (reduced, _) = lam3.whnf_lambda(args, exprs!([], &mut tc), &mut tc);
    assert_eq!(reduced, target);
}

// One more lambda than arguments
#[test]
fn reduce_lambda_test2() {
    let mut env = Env::new(());
    let mut live = env.as_live();
    let mut tc = live.as_tc(None, None);

    let v0 = <ExprPtr>::new_var(0, &mut tc);
    let v1 = <ExprPtr>::new_var(1, &mut tc);
    let v2 = <ExprPtr>::new_var(2, &mut tc);

    let cn1 = name!("const_name1", &mut tc);
    let cn2 = name!("const_name2", &mut tc);
    let cn3 = name!("const_name3", &mut tc);
    let const1 = <ExprPtr>::new_const(cn1, param!(["c"], &mut tc), &mut tc);
    let const2 = <ExprPtr>::new_const(cn2, param!(["b"], &mut tc), &mut tc);
    let const3 = <ExprPtr>::new_const(cn3, param!(["a"], &mut tc), &mut tc);

    let inner = v0.new_app(v1, &mut tc).new_app(v2, &mut tc);
    let lam1 = <ExprPtr>::new_lambda(name!("z", &mut tc), const1, Default, inner, &mut tc);
    let lam2 = <ExprPtr>::new_lambda(name!("y", &mut tc), const2, Default, lam1, &mut tc);
    let lam3 = <ExprPtr>::new_lambda(name!("x", &mut tc), const3, Default, lam2, &mut tc);

    let target = <ExprPtr>::new_lambda(
        name!("z", &mut tc),
        const1,
        Default,
        v0.new_app(const2, &mut tc).new_app(const3, &mut tc),
        &mut tc
    );

    let args = exprs!([const3, const2], &mut tc);

    let (reduced, _) = lam3.whnf_lambda(args, exprs!([], &mut tc), &mut tc);
    assert_eq!(reduced, target);
}


// one more arg than lambda
#[test]
fn reduce_lambda_test3() {
    let mut env = Env::new(());
    let mut live = env.as_live();
    let mut tc = live.as_tc(None, None);

    let v0 = <ExprPtr>::new_var(0, &mut tc);
    let v1 = <ExprPtr>::new_var(1, &mut tc);
    let v2 = <ExprPtr>::new_var(2, &mut tc);

    let cn1 = name!("const_name1", &mut tc);
    let cn2 = name!("const_name2", &mut tc);
    let cn3 = name!("const_name3", &mut tc);
    let const1 = <ExprPtr>::new_const(cn1, param!(["c"], &mut tc), &mut tc);
    let const2 = <ExprPtr>::new_const(cn2, param!(["b"], &mut tc), &mut tc);
    let const3 = <ExprPtr>::new_const(cn3, param!(["a"], &mut tc), &mut tc);

    let inner = v0.new_app(v1, &mut tc).new_app(v2, &mut tc);
    let lam1 = <ExprPtr>::new_lambda(name!("z", &mut tc), const1, Default, inner, &mut tc);
    let lam2 = <ExprPtr>::new_lambda(name!("y", &mut tc), const2, Default, lam1, &mut tc);

    let target = const2.new_app(const3, &mut tc).new_app(v2, &mut tc).new_app(const1, &mut tc);

    let args = exprs!([const3, const2, const1], &mut tc);

    let (reduced, _) = lam2.whnf_lambda(args, exprs!([], &mut tc), &mut tc);
    assert_eq!(reduced, target);
}
