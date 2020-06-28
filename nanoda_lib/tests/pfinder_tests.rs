#![allow(unused_imports)]
#![allow(unused_variables)]
use nanoda_lib::utils::{ HasNanodaDbg, List,  List::*, Env, IsTc };
use nanoda_lib::name::Name;
use nanoda_lib::level::Level;
use nanoda_lib::trace::NoopTracer;
use nanoda_lib::{ param, name, exprs, levels };
use nanoda_lib::expr::{ Expr, ExprPtr, ExprsPtr, BinderStyle::* };

#[test]
fn pfinder_test0() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let v0 = <ExprPtr>::new_var(0, &mut live);
    let v1 = <ExprPtr>::new_var(1, &mut live);
    let app12 = v0.new_app(v1, &mut live);

    let v2 = <ExprPtr>::new_var(2, &mut live);
    let v3 = <ExprPtr>::new_var(3, &mut live);
    let app23 = v2.new_app(v3, &mut live);

    let mut tc = live.as_tc(None, None);

    let cn0 = name!("const0", &mut tc);
    let cn1 = name!("const1", &mut tc);
    let cn2 = name!("const2", &mut tc);
    let cn3 = name!("const3", &mut tc);
    let u = param!("u", &mut tc).new_sort(&mut tc);
    let const0 = <ExprPtr>::new_const(cn0, param!(["a"], &mut tc), &mut tc);
    let const1 = <ExprPtr>::new_const(cn1, param!(["b"], &mut tc), &mut tc);
    let const2 = <ExprPtr>::new_const(cn1, param!(["b"], &mut tc), &mut tc);
    let const3 = <ExprPtr>::new_const(cn1, param!(["b"], &mut tc), &mut tc);

    let subs0 = exprs!([const1, const0], &mut tc);
    let subs1 = exprs!([const3, const2], &mut tc);

    {
        
        let mut pf0 = tc.as_pfinder();
        let inst0 = app12.inst(subs0, &mut pf0);
        
        {

            let mut pf1 = pf0.as_pfinder();
            let inst1 = app23.inst(subs1, &mut pf1);
        }

    }
}

