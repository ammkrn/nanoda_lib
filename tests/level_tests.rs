use nanoda_lib::utils::Env;

use nanoda_lib::name::Name;
use nanoda_lib::level::Level::*;
use nanoda_lib::param;


#[test]
fn level_test0() {
    let mut env = Env::new(false);

    let zero = Zero.alloc(&mut env);
    let one = zero.new_succ(&mut env);
    let two = one.new_succ(&mut env);

    let max_2_2 = two.new_max(two, &mut env);

    {
        let mut live = env.as_compiler();
        let simplified = max_2_2.simplify(&mut live);
        assert!(max_2_2.leq(two, &mut live));
        assert!(two.leq(max_2_2, &mut live));
        assert_eq!(two, simplified);
    }
}

#[test]
fn level_test1() {
    let mut env = Env::new(false);

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);

    let imax_u_0 = u.new_imax(zero, &mut env);

    {
        let mut live = env.as_compiler();
        let simplified = imax_u_0.simplify(&mut live);
        assert_eq!(simplified, zero);
    }
}

#[test]
fn level_test2() {
    let mut env = Env::new(false);

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_compiler();
        assert!(zero.leq(u, &mut live));
    }

}


#[test]
fn level_test3() {
    let mut env = Env::new(false);

    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_compiler();
        assert!(u.leq(u, &mut live));
    }
}


#[test]
fn level_test4() {
    let mut env = Env::new(false);

    let u = param!("u", &mut env);
    let v = param!("v", &mut env);
    
    {
        let mut live = env.as_compiler();
        assert!(!u.leq(v, &mut live));
        assert!(!v.leq(u, &mut live));
    }
}

#[test]
fn level_test5() {
    let mut env = Env::new(false);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let m_u_u = u.new_max(u, &mut env);
    
    {
        let mut live = env.as_compiler();
        assert!(u.leq(s_u, &mut live));
        assert!(!s_u.leq(u, &mut live));
        assert!(m_u_u.leq(s_u, &mut live));
    }
}


#[test]
fn level_test6() {
    let mut env = Env::new(false);
    let zero = Zero.alloc(&mut env);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let s_s_u = s_u.new_succ(&mut env);

    let v = param!("v", &mut env);
    let s_v = v.new_succ(&mut env);
    
    {
        let mut live = env.as_compiler();
        let im1 = s_s_u.new_imax(zero, &mut live);
        let im2 = s_v.new_imax(zero, &mut live);
        assert!(im1.leq(im2, &mut live));
        assert!(im2.leq(im1, &mut live));
    }
}

// With TC

#[test]
fn level_test7() {
    let mut env = Env::new(false);

    let zero = Zero.alloc(&mut env);
    let one = zero.new_succ(&mut env);
    let two = one.new_succ(&mut env);

    let max_2_2 = two.new_max(two, &mut env);

    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        let simplified = max_2_2.simplify(&mut tc);
        assert!(max_2_2.leq(two, &mut tc));
        assert!(two.leq(max_2_2, &mut tc));
        assert_eq!(two, simplified);
    }
}

#[test]
fn level_test8() {
    let mut env = Env::new(false);

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);

    let imax_u_0 = u.new_imax(zero, &mut env);

    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        let simplified = imax_u_0.simplify(&mut tc);
        assert_eq!(simplified, zero);
    }
}

#[test]
fn level_test9() {
    let mut env = Env::new(false);

    let zero = Zero.alloc(&mut env);
    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        assert!(zero.leq(u, &mut tc));
    }

}


#[test]
fn level_test10() {
    let mut env = Env::new(false);

    let u = param!("u", &mut env);
    
    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        assert!(u.leq(u, &mut tc));
    }
}


#[test]
fn level_test11() {
    let mut env = Env::new(false);

    let u = param!("u", &mut env);
    let v = param!("v", &mut env);
    
    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        assert!(!u.leq(v, &mut tc));
        assert!(!v.leq(u, &mut tc));
    }
}

#[test]
fn level_test12() {
    let mut env = Env::new(false);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let m_u_u = u.new_max(u, &mut env);
    
    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        assert!(u.leq(s_u, &mut tc));
        assert!(!s_u.leq(u, &mut tc));
        assert!(m_u_u.leq(s_u, &mut tc));
    }
}


#[test]
fn level_test13() {
    let mut env = Env::new(false);
    let zero = Zero.alloc(&mut env);

    let u = param!("u", &mut env);
    let s_u = u.new_succ(&mut env);
    let s_s_u = s_u.new_succ(&mut env);

    let v = param!("v", &mut env);
    let s_v = v.new_succ(&mut env);
    
    {
        let mut live = env.as_compiler();
        let mut tc = live.as_tc(None, None);
        let im1 = s_s_u.new_imax(zero, &mut tc);
        let im2 = s_v.new_imax(zero, &mut tc);
        assert!(im1.leq(im2, &mut tc));
        assert!(im2.leq(im1, &mut tc));
    }
}

