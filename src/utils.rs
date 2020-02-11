use hashbrown::HashMap;

use crate::expr::Expr;

pub trait HasInstantiate<T> {
    fn instantiate<I>(&self, es : I) -> Self 
    where I : Iterator<Item = T> + Clone;
}

pub fn foldr<A, B, I>(fun : impl Fn(A, B) -> B, i : I, init : B) -> B 
where I : IntoIterator<Item = A>,
      I :: IntoIter : DoubleEndedIterator {
    i.into_iter().rev().fold(init, |acc, next| fun(next, acc))
}


#[macro_export]
macro_rules! ret_none_if {
    ( $e:expr ) => {
            if $e {
                return None
            }
    }
}


#[macro_export]
macro_rules! chain {
    ( $( $e:expr),* ) => {
        {
            let acc = None.into_iter();

            $(
                let acc = acc.chain(Some($e).into_iter());
            )*

            acc
        }

    };
}

pub fn safe_minus_one(n : u16) -> u16 {
    if n == 0 {
        n
    } else {
        n - 1
    }
}

pub fn max3(n1 : u16, n2 : u16, n3 : u16) -> u16 {
    n1.max(n2).max(n3)
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Judgment {
    OK,
    NG,
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ShortCircuit {
    EqShort,
    NeqShort,
}

impl ShortCircuit {
    pub fn is_eq_short(self) -> bool {
        self == ShortCircuit::EqShort
    }

    pub fn is_neq_short(self) -> bool {
        self == ShortCircuit::NeqShort
    }
}



pub type SSOption = Option<ShortCircuit>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DeltaResult {
    Continue(Expr, Expr),
    Short(ShortCircuit),
    Unknown
}



#[derive(Debug, Copy, Clone)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// HashMap based cache; given two expressions, will tell you whether
/// the TypeChecker has seen this particular pair before, and if so,
/// what the result of a definitional equality comparison was. 
/// HashMap<(Expr, Expr), ShortCircuit> would be more intuitive, but
/// would require cloning both keys on every lookup due to the memory
/// layout of tuples.
#[derive(Clone)]
pub struct EqCache {
    inner : HashMap<Expr, Vec<(Expr, ShortCircuit)>>
}

impl EqCache {
    pub fn with_capacity(n : usize) -> Self {
        EqCache {
            inner : HashMap::with_capacity(n)
        }
    }

    pub fn get(&self, e1 : &Expr, e2 : &Expr) -> Option<ShortCircuit> {
        let closure = |k : &Expr, seq : &Vec<(Expr, ShortCircuit)>| {
            seq.iter().find(|(lhs, _)| lhs == k).map(|(_, ss_result)| *ss_result)
        };

        self.inner.get(e1)
        .and_then(|vec1| closure(e2, vec1))
        .or_else(|| self.inner.get(e2)
        .and_then(|vec2| closure(e1, vec2)))
    }

    pub fn insert(&mut self, e : Expr, ee : Expr, val : ShortCircuit) {
        match self.inner.get_mut(&e) {
            Some(v) => {
                v.push((ee, val));
            },
            None => {
                let mut v = Vec::with_capacity(10);
                v.push((ee, val));
                self.inner.insert(e, v);
            }
        }
    }
}

// used to prevent repeating failed lookups in dealta reduction.
#[derive(Clone)]
pub struct FailureCache {
    inner : HashMap<Expr, Vec<Expr>>
}

impl FailureCache {
    pub fn with_capacity(n : usize) -> Self {
        FailureCache {
            inner : HashMap::with_capacity(n)
        }
    }

    pub fn get(&self, e1 : &Expr, e2 : &Expr) -> bool {
        if let Some(v) = self.inner.get(e1) {
            if v.iter().any(|x| e1 == x) {
                return true
            }
        }

        if let Some(v) = self.inner.get(e2) {
            if v.iter().any(|x| e2 == x) {
                return true
            }
        }

        false
    }

    pub fn insert(&mut self, e : Expr, ee : Expr) {
        match self.inner.get_mut(&e) {
            Some(v) => {
                v.push(ee);
            },
            None => {
                let mut v = Vec::with_capacity(10);
                v.push(ee);
                self.inner.insert(e, v);
            }
        }
    }
}

