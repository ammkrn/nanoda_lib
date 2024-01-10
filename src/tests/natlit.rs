use crate::tc::{NatBinOp, TypeChecker};
use crate::tests::util::test_export_file;
use crate::util::{nat_div, nat_mod, nat_sub};
use crate::util::{ExportFile, ExprPtr, TcCtx};
use num_bigint::BigUint;
use num_bigint::RandBigInt;
use num_traits::{One, Zero};
use rand::rngs::ThreadRng;
use std::error::Error;
use std::path::Path;

#[cfg(test)]
fn pred(x: BigUint) -> BigUint {
    if x == BigUint::zero() {
        x
    } else {
        x - BigUint::one()
    }
}

/*
```
theorem Nat.div_le_self (n : Nat) (k : Nat) : n / k ≤ n
```
 */
#[test]
fn nat_div_le_self() {
    let mut rng = rand::thread_rng();
    for size in 0..1024 {
        for _ in 0..10 {
            let (n, k) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert!(nat_div(n.clone(), k) <= n);
        }
    }
}

/// Test that the theorem defining natural number division in Lean 4
/// is equal to `nat_div`, where `nat_div` is the "fast" operation
/// on the bignum type we're using. This is mostly just a mental health
/// check relative to `nat_div`.
///
/// `x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0`
#[test]
fn nat_div_eq() {
    fn nat_div_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if BigUint::zero() < y && y <= x {
            nat_div_eq_f(x - y.clone(), y) + BigUint::one()
        } else {
            BigUint::zero()
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_div_eq_f(x.clone(), y.clone()), nat_div(x, y))
        }
    }
}

#[test]
fn nat_add_eq() {
    fn nat_add_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if BigUint::zero() == y {
            x
        } else {
            nat_add_eq_f(x, y - BigUint::one()) + BigUint::one()
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_add_eq_f(x.clone(), y.clone()), x + y)
        }
    }
}

#[test]
fn nat_sub_eq() {
    fn nat_sub_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if BigUint::zero() == y {
            x
        } else {
            pred(nat_sub_eq_f(x, y - BigUint::one()))
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_sub_eq_f(x.clone(), y.clone()), nat_sub(x, y))
        }
    }
}

#[test]
fn nat_pow_eq() {
    use num_traits::Pow;
    fn nat_pow_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if BigUint::zero() == y {
            BigUint::one()
        } else {
            (x.clone().pow(y - BigUint::one())) * x
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_pow_eq_f(x.clone(), y.clone()), x.pow(y))
        }
    }
}

#[test]
fn nat_mul_eq() {
    fn nat_mul_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if BigUint::zero() == y {
            BigUint::zero()
        } else {
            nat_mul_eq_f(x.clone(), y - BigUint::one()) + x
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_mul_eq_f(x.clone(), y.clone()), x * y)
        }
    }
}

#[test]
fn nat_ble_eq() {
    fn nat_ble_eq_f(x: BigUint, y: BigUint) -> bool {
        let zero = BigUint::zero();
        if x == zero && y == zero {
            true
        } else if x == zero && zero < y {
            true
        } else if zero < x && y == zero {
            false
        } else {
            nat_ble_eq_f(pred(x), pred(y))
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_ble_eq_f(x.clone(), y.clone()), x <= y)
        }
    }
}

/// Test that the theorem defining natural number mod in Lean 4
/// is equal to `nad_mod`, where `nat_mod` is the "fast" operation
/// on the bignum type we're using. This is mostly just a mental health
/// check relative to `nat_mod`.
///
/// `x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x`
#[test]
fn nat_mod_eq() {
    fn nat_mod_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if BigUint::zero() < y && y <= x {
            nat_mod_eq_f(x - y.clone(), y)
        } else {
            x
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(nat_mod_eq_f(x.clone(), y.clone()), nat_mod(x, y))
        }
    }
}

//.. Nat.div_add_mod (m : Nat) (n : Nat) :
//n * (m / n) + m % n = m
#[test]
fn nat_div_add_mod() {
    let mut rng = rand::thread_rng();
    for size in 0..128 {
        for _ in 0..32 {
            let (n, m) = (rng.gen_biguint(size), rng.gen_biguint(size));
            let m_div_n = nat_div(m.clone(), n.clone());
            let m_mod_n = nat_mod(m.clone(), n.clone());
            let nat_mul_div = n.clone() * m_div_n;
            assert_eq!((nat_mul_div + m_mod_n), m)
        }
    }
}
/*
theorem Nat.mod_eq_sub_mod {a : Nat} {b : Nat} (h : a ≥ b) :
a % b = (a - b) % b
 */
#[test]
fn nat_mod_eq_sub_mod() {
    let mut rng = rand::thread_rng();
    for size in 0..128 {
        let mut iterations = 0;
        while iterations < 32 {
            let (a, b) = (rng.gen_biguint(size), rng.gen_biguint(size));
            if a >= b {
                iterations += 1;
                assert_eq!(nat_mod(a.clone(), b.clone()), nat_mod(a.clone() - b.clone(), b))
            } else {
                assert!(b > a);
                continue
            }
        }
    }
}

/// For randomly generated bignums `n`, `Nat.succ` applied n times to `Nat.zero)` is defEq to `NatLit n`
///
/// The size of the generated bignums needs to be kept relatively small since artificially
/// creating a bunch of unary nats could otherwise be resource intensive.
fn e_succ_zero_eq(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        for size in 0..8 {
            for _iteration in 0..100 {
                let target = rng.gen_biguint(size);
                let of_succ = {
                    let mut out = tc.ctx.c_nat_zero();
                    let c_succ = tc.ctx.c_nat_succ();
                    for _ in 0..u8::try_from(&target).unwrap() {
                        out = tc.ctx.mk_app(c_succ, out);
                    }
                    out
                };
                let bignum = tc.ctx.mk_nat_lit_quick(target);
                assert!(tc.def_eq(of_succ, bignum))
            }
        }
    })
}

/// For randomly generated bignums `n` and `m`, `Nat.succ` applied n times to `NatLit m`
/// is defEq to `NatLit n + m` using native addition.
fn e_succ_nat_lit_eq(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        for size in 0..=8 {
            for _iteration in 0..100 {
                let (n, m) = (rng.gen_biguint(size), rng.gen_biguint(size * 64));
                let of_succ = {
                    let mut out = tc.ctx.mk_nat_lit_quick(m.clone());
                    let c_succ = tc.ctx.c_nat_succ();
                    for _ in 0..u8::try_from(&n).unwrap() {
                        out = tc.ctx.mk_app(c_succ, out);
                    }
                    out
                };
                let bignum = tc.ctx.mk_nat_lit_quick(n + m);
                assert!(tc.def_eq(of_succ, bignum))
            }
        }
    })
}

/// theorem Nat.mul_zero (n : Nat) : n * 0 = 0
fn e_nat_mul_zero(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let zero = tc.ctx.mk_nat_lit_quick(BigUint::zero());
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let n = tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size));
                let n_mul_zero = tc.ctx.nat_binop(n, NatBinOp::Mul, zero);
                assert!(tc.def_eq(n_mul_zero, zero));
            }
        }
    })
}

///theorem Nat.mul_succ (n : Nat) (m : Nat) : n * Nat.succ m = n * m + n
fn e_nat_mul_succ(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let c_succ = tc.ctx.c_nat_succ();
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, m) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let succ_m = tc.ctx.mk_app(c_succ, m);
                let n_mul_succ_m = tc.ctx.nat_binop(n, NatBinOp::Mul, succ_m);
                let n_mul_m = tc.ctx.nat_binop(n, NatBinOp::Mul, m);
                let n_mul_m_add_n = tc.ctx.nat_binop(n_mul_m, NatBinOp::Add, n);
                assert!(tc.def_eq(n_mul_succ_m, n_mul_m_add_n));
            }
        }
    })
}

///theorem Nat.mul_comm (n : Nat) (m : Nat) : n * m = m * n
fn e_nat_mul_comm(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, m) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let n_mul_m = tc.ctx.nat_binop(n, NatBinOp::Mul, m);
                let m_mul_n = tc.ctx.nat_binop(m, NatBinOp::Mul, n);
                assert!(tc.def_eq(n_mul_m, m_mul_n));
            }
        }
    })
}

///theorem Nat.zero_add (n : Nat) : 0 + n = n
fn e_nat_zero_add(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let zero = tc.ctx.mk_nat_lit_quick(BigUint::zero());
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let n = tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size));
                let zero_add_n = tc.ctx.nat_binop(zero, NatBinOp::Add, n);
                assert!(tc.def_eq(zero_add_n, n));
            }
        }
    })
}
///theorem Nat.succ_add (n : Nat) (m : Nat) : Nat.succ n + m = Nat.succ (n + m)
fn e_nat_succ_add(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let c_succ = tc.ctx.c_nat_succ();
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, m) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let succ_n = tc.ctx.mk_app(c_succ, n);
                #[allow(non_snake_case)]
                let succ_n__add_m = tc.ctx.nat_binop(succ_n, NatBinOp::Add, m);
                let n_add_m = tc.ctx.nat_binop(n, NatBinOp::Add, m);
                #[allow(non_snake_case)]
                let succ__n_add_m = tc.ctx.mk_app(c_succ, n_add_m);
                assert!(tc.def_eq(succ_n__add_m, succ__n_add_m));
            }
        }
    })
}

/// (n / k) <= n
fn e_nat_div_le_self(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let bool_true = tc.ctx.bool_to_expr(true).unwrap();
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, k) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let n_div_k = tc.ctx.nat_binop(n, NatBinOp::Div, k);
                let n_div_k_le_n = tc.ctx.nat_binop(n_div_k, NatBinOp::Ble, n);
                assert!(tc.def_eq(n_div_k_le_n, bool_true));
            }
        }
    })
}

//theorem Nat.ne_of_lt {a : Nat} {b : Nat} (h : a < b) : a ≠ b
fn e_nat_ne_of_lt(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        for size in 0..1024 {
            let mut iterations = 0;
            while iterations < 10 {
                let (a, b) = (rng.gen_biguint(size), rng.gen_biguint(size + 1));
                if a < b {
                    iterations += 1;
                    tc.tc_cache.clear();
                    let (a, b) = (tc.ctx.mk_nat_lit_quick(a), tc.ctx.mk_nat_lit_quick(b));
                    assert!(!tc.def_eq(a, b));
                    tc.assert_not_beq(a, b)
                } else {
                    continue
                }
            }
        }
    })
}

///theorem Nat.div_lt_self {n : Nat} {k : Nat} (hLtN : 0 < n) (hLtK : 1 < k) : n / k < n
fn e_nat_div_lt_self(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let bool_true = tc.ctx.bool_to_expr(true).unwrap();
        let zero = BigUint::zero();
        let one = BigUint::one();
        for size in 0..1024 {
            let mut iterations = 0;
            while iterations < 10 {
                let (n, k) = (rng.gen_biguint(size + 1), rng.gen_biguint(size + 2));
                if zero < n && one < k {
                    iterations += 1;
                    let (n, k) = (tc.ctx.mk_nat_lit_quick(n), tc.ctx.mk_nat_lit_quick(k));
                    tc.tc_cache.clear();
                    let n_div_k = tc.ctx.nat_binop(n, NatBinOp::Div, k);
                    let n_div_k_lt_n = tc.ctx.nat_binop(n_div_k, NatBinOp::Ble, n);
                    assert!(tc.def_eq(n_div_k_lt_n, bool_true));
                } else {
                    continue
                }
            }
        }
    })
}

///theorem Nat.mod_eq_sub_mod {a : Nat} {b : Nat} (h : a ≥ b) : a % b = (a - b) % b
fn e_nat_mod_sub_eq(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        for size in 0..128 {
            let mut iteration = 0;
            while iteration < 32 {
                let (a, b) = (rng.gen_biguint(size), rng.gen_biguint(size));
                if a >= b {
                    iteration += 1;
                    tc.tc_cache.clear();
                    let (a, b) = (tc.ctx.mk_nat_lit_quick(a), tc.ctx.mk_nat_lit_quick(b));
                    let a_mod_b = tc.ctx.nat_binop(a, NatBinOp::Mod, b);
                    let a_sub_b = tc.ctx.nat_binop(a, NatBinOp::Sub, b);
                    let a_sub_b_mod_b = tc.ctx.nat_binop(a_sub_b, NatBinOp::Mod, b);
                    assert!(tc.def_eq(a_mod_b, a_sub_b_mod_b));
                } else {
                    continue
                }
            }
        }
    })
}

/// theorem Nat.pow_zero (n : Nat) : n ^ 0 = 1
fn e_nat_pow_zero(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let zero = tc.ctx.mk_nat_lit_quick(BigUint::zero());
        let one = tc.ctx.mk_nat_lit_quick(BigUint::one());
        for size in 0..512 {
            for _ in 0..32 {
                let n = tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size));
                let n_pow_zero = tc.ctx.nat_binop(n, NatBinOp::Pow, zero);
                assert!(tc.def_eq(n_pow_zero, one));
            }
        }
    })
}

///theorem Nat.sub_zero (n : Nat) : n - 0 = n
fn e_nat_sub_zero(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let zero = tc.ctx.mk_nat_lit_quick(BigUint::zero());
        for size in 0..512 {
            for _ in 0..32 {
                let n = tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size));
                let n_sub_zero = tc.ctx.nat_binop(n, NatBinOp::Sub, zero);
                assert!(tc.def_eq(n_sub_zero, n));
            }
        }
    })
}

/// theorem Nat.sub_le (n : Nat) (m : Nat) : n - m ≤ n
fn e_nat_sub_le(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let bool_true = tc.ctx.bool_to_expr(true).unwrap();
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, m) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let n_sub_m = tc.ctx.nat_binop(n, NatBinOp::Sub, m);
                let n_sub_m_le_n = tc.ctx.nat_binop(n_sub_m, NatBinOp::Ble, n);
                assert!(tc.def_eq(n_sub_m_le_n, bool_true));
            }
        }
    })
}

/// theorem Nat.succ_sub_succ_eq_sub (n : Nat) (m : Nat) : Nat.succ n - Nat.succ m = n - m
fn e_nat_succ_sub_succ_eq_sub(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        let c_succ = tc.ctx.c_nat_succ();
        for size in 0..1024 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, m) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let succ_n = tc.ctx.mk_app(c_succ, n);
                let succ_m = tc.ctx.mk_app(c_succ, m);
                let succ_n_sub_succ_m = tc.ctx.nat_binop(succ_n, NatBinOp::Sub, succ_m);
                let n_sub_m = tc.ctx.nat_binop(n, NatBinOp::Sub, m);
                tc.assert_eq_beq(succ_n_sub_succ_m, n_sub_m);
            }
        }
    })
}

/// n ^ Nat.succ m = n ^ m * n
fn e_nat_pow_succ(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        // keep this one small
        let c_succ = tc.ctx.c_nat_succ();
        for size in 0..5 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let (n, m) =
                    (tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)), tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size)));
                let succ_m = tc.ctx.mk_app(c_succ, m);
                let n_pow_succ_m = tc.ctx.nat_binop(n, NatBinOp::Pow, succ_m);
                let n_pow_m = tc.ctx.nat_binop(n, NatBinOp::Pow, m);
                let n_pow_m_mul_n = tc.ctx.nat_binop(n_pow_m, NatBinOp::Mul, n);
                assert!(tc.def_eq(n_pow_succ_m, n_pow_m_mul_n));
            }
        }
    })
}
/// theorem Nat.lt_succ_self (n : Nat) : n < Nat.succ n
fn e_nat_lt_succ_self(export: &ExportFile, rng: &mut ThreadRng) {
    export.with_tc(|tc| {
        // keep this one small
        let c_succ = tc.ctx.c_nat_succ();
        let bool_true = tc.ctx.bool_to_expr(true).unwrap();
        for size in 0..512 {
            for _iteration in 0..10 {
                tc.tc_cache.clear();
                let n = tc.ctx.mk_nat_lit_quick(rng.gen_biguint(size));
                let succ_n = tc.ctx.mk_app(c_succ, n);
                let n_lt_succ_n = tc.ctx.nat_binop(n, NatBinOp::Ble, succ_n);
                assert!(tc.def_eq(n_lt_succ_n, bool_true));
            }
        }
    })
}

/// Runs a series of tests using the same export file so we don't have to
/// re-parse the file for every test.
#[test]
fn e_nat_tests() -> Result<(), Box<dyn Error>> {
    test_export_file(Some(&Path::new("test_resources/Init/config.json")), |export| {
        let mut rng = rand::thread_rng();
        e_succ_zero_eq(export, &mut rng);
        e_succ_nat_lit_eq(export, &mut rng);
        e_nat_zero_add(export, &mut rng);
        e_nat_succ_add(export, &mut rng);
        e_nat_succ_sub_succ_eq_sub(export, &mut rng);
        e_nat_sub_zero(export, &mut rng);
        e_nat_sub_le(export, &mut rng);
        e_nat_lt_succ_self(export, &mut rng);
        e_nat_div_le_self(export, &mut rng);
        e_nat_div_lt_self(export, &mut rng);
        e_nat_mod_sub_eq(export, &mut rng);
        e_nat_pow_zero(export, &mut rng);
        e_nat_pow_succ(export, &mut rng);
        e_nat_mul_zero(export, &mut rng);
        e_nat_mul_succ(export, &mut rng);
        e_nat_mul_comm(export, &mut rng);
        e_nat_ne_of_lt(export, &mut rng);
    })
}

#[cfg(test)]
impl<'t, 'p> TcCtx<'t, 'p> {
    fn nat_binop(&mut self, l: ExprPtr<'t>, op: NatBinOp, r: ExprPtr<'t>) -> ExprPtr<'t> {
        let op_name = match op {
            NatBinOp::Add => self.export_file.name_cache.nat_add.unwrap(),
            NatBinOp::Sub => self.export_file.name_cache.nat_sub.unwrap(),
            NatBinOp::Mul => self.export_file.name_cache.nat_mul.unwrap(),
            NatBinOp::Pow => self.export_file.name_cache.nat_pow.unwrap(),
            NatBinOp::Mod => self.export_file.name_cache.nat_mod.unwrap(),
            NatBinOp::Div => self.export_file.name_cache.nat_div.unwrap(),
            NatBinOp::Beq => self.export_file.name_cache.nat_beq.unwrap(),
            NatBinOp::Ble => self.export_file.name_cache.nat_ble.unwrap(),
        };
        let levels = self.alloc_levels_slice(&[]);
        let c_op = self.mk_const(op_name, levels);
        let out = self.mk_app(c_op, l);
        self.mk_app(out, r)
    }
}

#[cfg(test)]
impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    fn assert_eq_beq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.tc_cache.clear();
        assert!(self.def_eq(x, y));
        self.assert_beq(x, y)
    }

    fn assert_beq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.tc_cache.clear();
        let bool_true = self.ctx.bool_to_expr(true).unwrap();
        let beq = self.ctx.nat_binop(x, NatBinOp::Beq, y);
        assert!(self.def_eq(beq, bool_true))
    }

    fn assert_not_beq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.tc_cache.clear();
        let beq = self.ctx.nat_binop(x, NatBinOp::Beq, y);
        let bool_false = self.ctx.bool_to_expr(false).unwrap();
        assert!(self.def_eq(beq, bool_false))
    }

    #[allow(dead_code)]
    fn assert_ble(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.tc_cache.clear();
        let bool_true = self.ctx.bool_to_expr(true).unwrap();
        let ble = self.ctx.nat_binop(x, NatBinOp::Ble, y);
        assert!(self.def_eq(ble, bool_true))
    }
}
