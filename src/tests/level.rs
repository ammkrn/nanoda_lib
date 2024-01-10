use crate::tests::util::test_ctx;
use rand::prelude::*;
use std::error::Error;

#[test]
fn leq_test0() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let m = ctx.max(s, s);
        assert!(ctx.leq(s, m));
        assert!(ctx.leq(m, s));
        assert!(ctx.eq_antisymm(s, m));
    })
}

#[test]
fn leq_test1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let im = ctx.imax(ss, z);
        assert!(ctx.leq(im, z));
        assert!(ctx.eq_antisymm(z, im));
    })
}

#[test]
fn leq_test2() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let a = ctx.param_quick("a");
        let b = ctx.param_quick("b");
        assert!(!ctx.leq(a, b));
        assert!(!ctx.leq(b, a));
    })
}

#[test]
fn leq_test3() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let a = ctx.param_quick("a");
        let b = ctx.param_quick("b");
        assert!(!ctx.leq(a, b));
        assert!(!ctx.leq(b, a));
    })
}

#[test]
fn leq_test4() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        for _ in 0..100 {
            let mut rng = thread_rng();
            let (small, large) = {
                let (x, y): (u8, u8) = rng.gen();
                (x.min(y), x.max(y))
            };

            let p = ctx.param_quick("p");
            let (a, b) = (ctx.level_n(p, small as u64), ctx.level_n(p, large as u64));
            assert!(ctx.leq(a, b));
        }
    })
}

#[test]
fn leq_test5() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
        let mut rng = thread_rng();
        for _ in 0..100 {
            let (small, large) = {
                let (x, y): (u8, u8) = rng.gen();
                (x.min(y) as u64, x.max(y) as u64)
            };
            let lhs = {
                let (p_small, q_small) = (ctx.level_n(p, small), ctx.level_n(q, small));
                let lhs = ctx.max(p_small, q_small);
                ctx.level_n(lhs, small)
            };
            let rhs = {
                let (p_large, q_large) = (ctx.level_n(p, large), ctx.level_n(q, large));
                let rhs = ctx.max(p_large, q_large);
                ctx.level_n(rhs, large)
            };

            assert!(ctx.leq(lhs, rhs));
        }
    })
}

#[test]
fn leq_test6() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
        let mut rng = thread_rng();
        for _ in 0..100 {
            let (small, large) = {
                let (x, y): (u8, u8) = rng.gen();
                (x.min(y) as u64, x.max(y) as u64)
            };
            let lhs = {
                let (p_small, q_small) = (ctx.level_n(p, small), ctx.level_n(q, small));
                let lhs = ctx.imax(p_small, q_small);
                ctx.level_n(lhs, small)
            };
            let rhs = {
                let (p_large, q_large) = (ctx.level_n(p, large), ctx.level_n(q, large));
                let rhs = ctx.imax(p_large, q_large);
                ctx.level_n(rhs, large)
            };

            assert!(ctx.leq(lhs, rhs));
        }
    })
}

#[test]
fn leq_test7() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
        let mut rng = thread_rng();
        for _ in 0..100 {
            let (u, v, w) = {
                let (u, v, w): (u8, u8, u8) = rng.gen();
                (u as u64, v as u64, w as u64)
            };
            let lhs = {
                let (p_, q_) = (ctx.level_n(p, u), ctx.level_n(q, v + 1));
                let lhs = ctx.imax(p_, q_);
                ctx.level_n(lhs, w)
            };
            let rhs = {
                let (p_, q_) = (ctx.level_n(p, u), ctx.level_n(q, v + 1));
                let rhs = ctx.max(p_, q_);
                ctx.level_n(rhs, w)
            };

            assert!(ctx.eq_antisymm(lhs, rhs));
        }
    })
}

#[test]
fn eq_test1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let m = ctx.max(s, s);
        let sm = ctx.succ(m);
        assert!(ctx.eq_antisymm(ss, sm));
    })
}

#[test]
fn eq_many_test1() -> Result<(), Box<dyn Error>> {
    // [2] == [max(1, 1) + 1]
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let m = ctx.max(s, s);
        let sm = ctx.succ(m);
        let ups1 = ctx.alloc_levels(std::sync::Arc::from([ss]));
        let ups2 = ctx.alloc_levels(std::sync::Arc::from([sm]));
        assert!(ctx.eq_antisymm_many(ups1, ups2));
    })
}

#[test]
fn debug_test0() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let (z_, num) = ctx.level_succs(ss);
        assert_eq!(z_, z);
        assert_eq!(num, 2);
        assert_eq!("2", format!("{:?}", ctx.debug_print(ss)));
    })
}

#[test]
fn debug_test1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let m = ctx.max(s, s);
        let sm = ctx.succ(m);
        let (m_, num) = ctx.level_succs(sm);
        assert_eq!(m, m_);
        assert_eq!(num, 1);
        assert_eq!("max(1, 1) + 1", format!("{:?}", ctx.debug_print(sm)));
    })
}
