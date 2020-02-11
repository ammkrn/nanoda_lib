use std::sync::Arc;

use hashbrown::HashSet;

use InnerName::*;

/// `Name` is an Arc wrapper for the `InnerName` enum, which together represent Lean's hierarchical names, where
/// hierarchical just means "nested namespaces that can be accessed with a dot", like `nat.rec`. They have a very 
/// similar structure to an inductive `List` type, with `Anon`, the anonymous name acting as `Nil`, 
/// while `Str` and `Num` act like `cons`, but specialized to consing string and integer elements respectively.
/// Name values always begin with `Anon`, and can contain any combination of `Str` and `Num` applications, 
/// IE (in pseudo-code) `Num n (Str s (Num n' (Str s' (Anon))))` would be a valid construction.
#[derive(Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct Name(Arc<InnerName>);

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub enum InnerName {
    Anon,
    Str(Name, String),
    Num(Name, u64),
}

pub fn mk_anon() -> Name {
    Name(Arc::new(InnerName::Anon))
}


impl Name {
    pub fn is_anon(&self) -> bool {
        match self {
            Name(x) => match x.as_ref() {
                Anon => true,
                _ => false
            }
        }
    }

    pub fn replace_prefix(&self, prefix : &Name, new_prefix : &Name) -> Name {
        match self.as_ref() {
            Anon => mk_anon(),
            Str(pfx, hd) => {
                let hd_name = Name::from(hd.as_str());
                // "A.B.D == D"
                if &hd_name == prefix {
                    let new_head = new_prefix.clone();
                    let new_base = pfx.replace_prefix(prefix, new_prefix);
                    new_base.concat(&new_head)
                } else {
                    // no match; no need to replace
                    pfx.replace_prefix(prefix, new_prefix).extend_str(hd)

                }
            },
            Num(pfx, hd) => {
                let hd_name = Name::from(*hd);
                if &hd_name == prefix {
                    // match; replace
                    let new_head = new_prefix.clone();
                    let new_base = pfx.replace_prefix(prefix, new_prefix);
                    new_base.concat(&new_head)
                } else {
                    // no need to replace
                    pfx.replace_prefix(prefix, new_prefix).extend_num(*hd)
                }
            }

        }
    }


    pub fn mk_rec_name(&self) -> Name {
        self.extend_str("rec")
    }


    /// Extend some hierarchical name with a string. IE `nat` => `nat.rec`
    pub fn extend_str(&self, hd : &str) -> Self {
        Str(self.clone(), String::from(hd)).into()    // InnerName -> Name
    }

    /// Extend some hierarchical name with an integer. IE `prod` => `prod.3`
    pub fn extend_num(&self, hd : u64) -> Self {
        Num(self.clone(), hd).into()                  // InnerName -> Name
    }

    pub fn get_prefix(&self) -> &Name {
        match self.as_ref() {
            Anon => self,
            | Str(pfx, _) 
            | Num(pfx, _) => pfx
        }
    }


    /// Given a suggested prefix and a set of names we want to avoid collisions with,
    /// extend the suggestion with an incrementing integer until we get a name that doesn't collide with
    /// any of the names given in `forbidden`. This implementation relies on the laziness of iterators.
    pub fn fresh_name(suggested : &str, forbidden : HashSet<&Name>) -> Self {
        let base = Name::from(suggested);
        if !forbidden.contains(&base) {
            return base
        }
        (0u64..).into_iter()
                .map(|n| base.extend_num(n))
                .filter(|candidate| !forbidden.contains(candidate))
                .next()
                .unwrap()

    }


    pub fn is_recursor(&self) -> bool {
        match self.as_ref() {
            Anon => false,
            Str(pfx, s) => {
                s.as_str() == "rec"
                || pfx.is_recursor()
            },
            Num(pfx, _) => pfx.is_recursor()
        }
    }

    pub fn concat(&self, n : &Name) -> Name {
        match n.as_ref() {
            Anon => self.clone(),
            Str(pfx, hd) => {
                let inner = self.concat(pfx);
                inner.extend_str(hd)
            },
            Num(pfx, hd) => {
                let inner = self.concat(pfx);
                inner.extend_num(*hd)
            }
        }
    }

}




/// Convenience function to get the `InnerName` from a `Name`    
impl std::convert::AsRef<InnerName> for Name {
    fn as_ref(&self) -> &InnerName {
        match self {
            Name(x) => x.as_ref()
        }
    }
}

/// Convenience function for converting an Arc<InnerName> into its newtype `Name`
impl From<Arc<InnerName>> for Name {
    fn from(x : Arc<InnerName>) -> Name {
        Name(x)
    }
}
// Convenience function for converting an InnerName to a Name
impl From<InnerName> for Name {
    fn from(x : InnerName) -> Name {
        Name(Arc::new(x))
    }
}

/// Creates a Name value from a string slice. 
impl From<&str> for Name {
    fn from(s : &str) -> Name {
        mk_anon().extend_str(s)
    }
}

impl From<u64> for Name {
    fn from(n : u64) -> Name {
        mk_anon().extend_num(n)
    }
}


/// Hierarchical names should display from left to right, with a `.` separating elements, and the anonymous name
/// should display as an empty string.
/// IE the formatted version of Anon ++ Str(list) ++ Str(cases_on) ++ Num(777) should display as
/// `list.cases_on.777`
impl std::fmt::Debug for Name {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.as_ref() {
            Anon => write!(f, ""),
            Str(pfx, hd) => match pfx.as_ref() {
                Anon     => write!(f, "{}", hd),
                owise        => write!(f, "{}.{}", owise, hd)
            },
            Num(pfx, hd) => match pfx.as_ref() {
                Anon     => write!(f, "{}", hd),
                owise        => write!(f, "{}.{}", owise, hd)
            }
        }
    }
}


impl std::fmt::Display for Name {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.as_ref() {
            Anon => write!(f, ""),
            Str(pfx, hd) => match pfx.as_ref() {
                Anon     => write!(f, "{}", hd),
                owise        => write!(f, "{}.{}", owise, hd)
            },
            Num(pfx, hd) => match pfx.as_ref() {
                Anon     => write!(f, "{}", hd),
                owise        => write!(f, "{}.{}", owise, hd)
            }
        }
    }
}


impl std::fmt::Display for InnerName {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Anon => write!(f, ""),
            Str(pfx, hd) => match pfx.as_ref() {
                Anon     => write!(f, "{}", hd),
                owise        => write!(f, "{}.{}", owise, hd)
            },
            Num(pfx, hd) => match pfx.as_ref() {
                Anon     => write!(f, "{}", hd),
                owise        => write!(f, "{}.{}", owise, hd)
            }
        }
    }
}

#[cfg(test)]
mod name_tests {
    use super::*;

    #[test]
    fn nametest1() {
        let n1 = Name::from("A").extend_str("B").extend_num(12).extend_str("H");
        let target = Name::from("A").extend_str("C").extend_num(777).extend_str("H");
        let n2 = Name::from("B");
        let n3 = Name::from("C");
        let n4 = Name::from(12);
        let n5 = Name::from(777);

        let n1_ = n1.replace_prefix(&n2, &n3);
        let n2_ = n1_.replace_prefix(&n4, &n5);
        assert_eq!(n2_, target);
    }
}

