#![allow(unused_imports)]
#![allow(unused_variables)]
use nanoda_lib::utils::{ IsTc, Env, List, List::*, HasNanodaDbg };
use nanoda_lib::name::{ Name };
use nanoda_lib::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use nanoda_lib::param;
use nanoda_lib::trace::StdoutTracer;

#[test]
fn level_test_iz_zero() {
    let mut env = Env::new(());
    let mut live = env.as_live();

    let zero = Zero.alloc(&mut live);
    let one = zero.new_succ(&mut live);
    let m = one.new_max(one, &mut live);
    let im = one.new_imax(one, &mut live);
    let param = param!("a", &mut live);
    assert!(zero.is_zero_lit(&mut live).0);
    assert!(!one.is_zero_lit(&mut live).0);
    assert!(!m.is_zero_lit(&mut live).0);
    assert!(!im.is_zero_lit(&mut live).0);
    assert!(!param.is_zero_lit(&mut live).0);
}


#[test]
fn level_test_is_succ() {
    let mut env = Env::new(());
    let mut live = env.as_live();

    let zero = Zero.alloc(&mut live);
    let one = zero.new_succ(&mut live);
    let m = one.new_max(one, &mut live);
    let im = one.new_imax(one, &mut live);
    let param = param!("a", &mut live);
    assert!(!zero.is_succ(&mut live).0);
    assert!(one.is_succ(&mut live).0);
    assert!(!m.is_succ(&mut live).0);
    assert!(!im.is_succ(&mut live).0);
    assert!(!param.is_succ(&mut live).0);
}

#[test]
fn level_test_is_any_max() {
    let mut env = Env::new(());
    let mut live = env.as_live();

    let zero = Zero.alloc(&mut live);
    let one = zero.new_succ(&mut live);
    let m = one.new_max(one, &mut live);
    let im = one.new_imax(one, &mut live);
    let param = param!("a", &mut live);
    assert!(!zero.is_any_max(&mut live).0);
    assert!(!one.is_any_max(&mut live).0);
    assert!(m.is_any_max(&mut live).0);
    assert!(im.is_any_max(&mut live).0);
    assert!(!param.is_any_max(&mut live).0);
}




#[test]
fn level_test0() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let one = zero.new_succ(&mut env);
    let two = one.new_succ(&mut env);

    let max_2_2 = two.new_max(two, &mut env);

    {
        let mut live = env.as_live();
        let simplified = max_2_2.simplify(&mut live);
        assert!(max_2_2.leq(two, &mut live).0);
        assert!(two.leq(max_2_2, &mut live).0);
        assert_eq!(two, simplified.0);
    }
}

#[test]
fn level_test1() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);

    let imax_u_0 = u.new_imax(zero, &mut env);

    {
        let mut live = env.as_live();
        let simplified = imax_u_0.simplify(&mut live).0;
        assert_eq!(simplified, zero);
    }
}

#[test]
fn level_test2() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_live();
        assert!(zero.leq(u, &mut live).0);
    }

}


#[test]
fn level_test3() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_live();
        assert!(u.leq(u, &mut live).0);
    }
}


#[test]
fn level_test4() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    let v = param!("v", &mut env);
    
    {
        let mut live = env.as_live();
        assert!(!u.leq(v, &mut live).0);
        assert!(!v.leq(u, &mut live).0);
    }
}

#[test]
fn level_test5() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let m_u_u = u.new_max(u, &mut env);
    
    {
        let mut live = env.as_live();
        assert!(u.leq(s_u, &mut live).0);
        assert!(!s_u.leq(u, &mut live).0);
        assert!(m_u_u.leq(s_u, &mut live).0);
    }
}


#[test]
fn level_test6() {
    let mut env = Env::new(());
    let zero = Zero.alloc(&mut env);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let s_s_u = s_u.new_succ(&mut env);

    let v = param!("v", &mut env);
    let s_v = v.new_succ(&mut env);
    
    {
        let mut live = env.as_live();
        let im1 = s_s_u.new_imax(zero, &mut live);
        let im2 = s_v.new_imax(zero, &mut live);
        assert!(im1.leq(im2, &mut live).0);
        assert!(im2.leq(im1, &mut live).0);
    }
}

// With TC

#[test]
fn level_test7() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let one = zero.new_succ(&mut env);
    let two = one.new_succ(&mut env);

    let max_2_2 = two.new_max(two, &mut env);

    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let simplified = max_2_2.simplify(&mut tc);
        assert!(max_2_2.leq(two, &mut tc).0);
        assert!(two.leq(max_2_2, &mut tc).0);
        assert_eq!(two, simplified.0);
    }
}

#[test]
fn level_test8() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);

    let imax_u_0 = u.new_imax(zero, &mut env);

    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let simplified = imax_u_0.simplify(&mut tc);
        assert_eq!(simplified.0, zero);
    }
}

#[test]
fn level_test9() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        assert!(zero.leq(u, &mut tc).0);
    }

}


#[test]
fn level_test10() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        assert!(u.leq(u, &mut tc).0);
    }
}


#[test]
fn level_test11() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    let v = param!("v", &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        assert!(!u.leq(v, &mut tc).0);
        assert!(!v.leq(u, &mut tc).0);
    }
}

#[test]
fn level_test12() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let m_u_u = u.new_max(u, &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        assert!(u.leq(s_u, &mut tc).0);
        assert!(!s_u.leq(u, &mut tc).0);
        assert!(m_u_u.leq(s_u, &mut tc).0);
    }
}


#[test]
fn level_test13() {
    let mut env = Env::new(());
    let zero = Zero.alloc(&mut env);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let s_s_u = s_u.new_succ(&mut env);

    let v = param!("v", &mut env);
    let s_v = v.new_succ(&mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let im1 = s_s_u.new_imax(zero, &mut tc);
        let im2 = s_v.new_imax(zero, &mut tc);
        assert!(im1.leq(im2, &mut tc).0);
        assert!(im2.leq(im1, &mut tc).0);
    }
}


// With Pfinder 

#[test]
fn level_test14() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let one = zero.new_succ(&mut env);
    let two = one.new_succ(&mut env);

    let max_2_2 = two.new_max(two, &mut env);

    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        let simplified = max_2_2.simplify(&mut pfinder);
        assert!(max_2_2.leq(two, &mut pfinder).0);
        assert!(two.leq(max_2_2, &mut pfinder).0);
        assert_eq!(two, simplified.0);
    }
}

#[test]
fn level_test15() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);

    let imax_u_0 = u.new_imax(zero, &mut env);

    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        let simplified = imax_u_0.simplify(&mut pfinder);
        assert_eq!(simplified.0, zero);
    }
}

#[test]
fn level_test16() {
    let mut env = Env::new(());

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        assert!(zero.leq(u, &mut pfinder).0);
    }

}


#[test]
fn level_test17() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        assert!(u.leq(u, &mut pfinder).0);
    }
}


#[test]
fn level_test18() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    let v = param!("v", &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        assert!(!u.leq(v, &mut pfinder).0);
        assert!(!v.leq(u, &mut pfinder).0);
    }
}

#[test]
fn level_test19() {
    let mut env = Env::new(());

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let m_u_u = u.new_max(u, &mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        assert!(u.leq(s_u, &mut pfinder).0);
        assert!(!s_u.leq(u, &mut pfinder).0);
        assert!(m_u_u.leq(s_u, &mut pfinder).0);
    }
}


#[test]
fn level_test20() {
    let mut env = Env::new(());
    let zero = Zero.alloc(&mut env);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let s_s_u = s_u.new_succ(&mut env);

    let v = param!("v", &mut env);
    let s_v = v.new_succ(&mut env);
    
    {
        let mut live = env.as_live();
        let mut tc = live.as_tc(None, None);
        let mut pfinder = tc.as_pfinder();
        let im1 = s_s_u.new_imax(zero, &mut pfinder);
        let im2 = s_v.new_imax(zero, &mut pfinder);
        assert!(im1.leq(im2, &mut pfinder).0);
        assert!(im2.leq(im1, &mut pfinder).0);
    }
}

#[test]
fn level_test21() {
    let mut env = Env::new(StdoutTracer::new());
    let zero = Zero.alloc(&mut env);
    
    let mut live = env.as_live();
    let e = param!("e", &mut live);
    let fold_args = param!(["c", "b", "a"], &mut live);

    let target = <LevelPtr>::new_imax(param!("c", &mut live), e, &mut live);
    let target = <LevelPtr>::new_imax(param!("b", &mut live), target, &mut live);
    let target = <LevelPtr>::new_imax(param!("a", &mut live), target, &mut live);


    let (out, _) = fold_args.fold_imaxs(e, &mut live);
    println!("out : {}\n", out.nanoda_dbg(&live));
    assert_eq!(target, out);


    
}