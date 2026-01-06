use crate::util::{nat_div, nat_mod, nat_sub};
use num_bigint::BigUint;
use num_bigint::RandBigInt;
use num_traits::{One, Zero};

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
fn nat_shr_eq() {
    use crate::util::nat_shr;
    assert_eq!(nat_shr(BigUint::from(4u8), BigUint::from(2u8)), BigUint::one());
    assert_eq!(nat_shr(BigUint::from(8u8), BigUint::from(2u8)), BigUint::from(2u8));
    assert_eq!(nat_shr(BigUint::from(8u8), BigUint::from(3u8)), BigUint::one());
    assert_eq!(nat_shr(BigUint::from(0u8), BigUint::from(3u8)), BigUint::zero());
    //def shiftRight : @& Nat → @& Nat → Nat
    //  | n, 0 => n
    //  | n, succ m => shiftRight n m / 2
    // m >>> n = m / 2 ^ n
    fn nat_shr_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if y.is_zero() {
            x
        } else {
            nat_shr_eq_f(x, y - BigUint::one()) / BigUint::from(2u8)
        }
    }
    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size % 6));
            assert_eq!(nat_shr_eq_f(x.clone(), y.clone()), nat_shr(x, y))
        }
    }
}

#[test]
fn nat_shl_eq() {
    use crate::util::nat_shl;
    assert_eq!(nat_shl(BigUint::one(), BigUint::from(2u8)), BigUint::from(4u8));
    assert_eq!(nat_shl(BigUint::one(), BigUint::from(3u8)), BigUint::from(8u8));
    assert_eq!(nat_shl(BigUint::zero(), BigUint::from(3u8)), BigUint::zero());
    assert_eq!(nat_shl(BigUint::from(0xf1 as u32), BigUint::from(4u8)), BigUint::from(0xf10 as u32));
    // def shiftLeft : @& Nat → @& Nat → Nat
    //   | n, 0 => n
    //   | n, succ m => shiftLeft (2*n) m
    // a <<< b = a * 2 ^ b
    fn nat_shl_eq_f(x: BigUint, y: BigUint) -> BigUint {
        if y.is_zero() {
            x
        } else {
            nat_shl_eq_f(BigUint::from(2u8) * x, y - BigUint::one())
        }
    }

    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size % 6));
            assert_eq!(nat_shl_eq_f(x.clone(), y.clone()), nat_shl(x, y))
        }
    }
}

#[test]
fn nat_gcd_eq() {
    use crate::util::nat_gcd;
    assert_eq!(nat_gcd(&BigUint::from(10u8), &BigUint::from(15u8)), BigUint::from(5u8));
    assert_eq!(nat_gcd(&BigUint::zero(), &BigUint::from(5u8)), BigUint::from(5u8));
    assert_eq!(nat_gcd(&BigUint::from(7u8), &BigUint::zero()), BigUint::from(7u8));
    assert_eq!(nat_gcd(&BigUint::from(1u8), &BigUint::zero()), BigUint::from(1u8));
    //def gcd (m n : @& Nat) : Nat :=
    //  if m = 0 then
    //    n
    //  else
    //    gcd (n % m) m
    fn nat_gcd_eq_f(m: BigUint, n: BigUint) -> BigUint {
        if m.is_zero() {
            n
        } else {
            nat_gcd_eq_f(n % m.clone(), m)
        }
    }

    let mut rng = rand::thread_rng();
    for size in 0..8 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            let gcd = nat_gcd(&x, &y);
            assert_eq!(nat_gcd_eq_f(x, y), gcd)
        }
    }
}

fn bitwise(f: fn(bool, bool) -> bool, n : BigUint, m: BigUint) -> BigUint {
    if n.is_zero() {
        if f(false, true) {
            m
        } else {
            BigUint::zero()
        }
    } else if m.is_zero() {
        if f(true, false) {
            n
        } else {
            BigUint::zero()
        }
    } else {
        let nprime = n.clone() / BigUint::from(2u8);
        let mprime = m.clone() / BigUint::from(2u8);
        let b1 = n % BigUint::from(2u8) == BigUint::one();
        let b2 = m % BigUint::from(2u8) == BigUint::one();
        let r = bitwise(f, nprime, mprime);
        if f(b1, b2) {
            r.clone() + r + BigUint::one()
        } else {
            r.clone() + r
        }
    }
}

#[test]
fn nat_xor_eq() {
    fn spec_xor(x: BigUint, y: BigUint) -> BigUint {
      fn bool_xor(x: bool, y: bool) -> bool {
          x ^ y
      }
      bitwise(bool_xor, x, y)
    }

    use crate::util::nat_xor;
    let mut rng = rand::thread_rng();
    for size in 0..5 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            let rhs = nat_xor(&x, &y);
            eprintln!("{:?} ^ {:?} := {:?}", x, y, rhs);
            assert_eq!(spec_xor(x, y), rhs)
        }
    }
}

#[test]
fn nat_lor_eq() {
    fn spec_lor(x: BigUint, y: BigUint) -> BigUint {
      fn bool_or(x: bool, y: bool) -> bool {
          x || y
      }
      bitwise(bool_or, x, y)
    }

    use crate::util::nat_lor;
    let mut rng = rand::thread_rng();
    for size in 0..5 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(spec_lor(x.clone(), y.clone()), nat_lor(x, y))
        }
    }
}

#[test]
fn nat_land_eq() {
    fn spec_land(x: BigUint, y: BigUint) -> BigUint {
        fn bool_and(x: bool, y: bool) -> bool {
            x && y
        }
        bitwise(bool_and, x, y)
    }

    use crate::util::nat_land;
    let mut rng = rand::thread_rng();
    for size in 0..5 {
        for _ in 0..32 {
            let (x, y) = (rng.gen_biguint(size), rng.gen_biguint(size));
            assert_eq!(spec_land(x.clone(), y.clone()), nat_land(x, y))
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

// Tests requiring Init export file removed (tests for Nat kernel extension
// definitional equality that require constants like Nat.add, Nat.succ, etc.
// from the Lean prelude)
