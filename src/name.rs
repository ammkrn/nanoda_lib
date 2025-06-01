//! Implementaiton of the `Name` type (hierarchical names)
use crate::util::{CowStr, NamePtr, StringPtr, TcCtx};
use Name::*;

pub(crate) const ANON_HASH: u64 = 43;
pub(crate) const STR_HASH: u64 = 911;
pub(crate) const NUM_HASH: u64 = 103;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name<'a> {
    Anon,
    Str(NamePtr<'a>, StringPtr<'a>, u64),
    Num(NamePtr<'a>, u64, u64),
}

impl<'a> std::hash::Hash for Name<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

impl<'a> Name<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Anon => ANON_HASH,
            Str(.., hash) | Num(.., hash) => *hash,
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn concat_name(&mut self, n1: NamePtr<'t>, n2: NamePtr<'t>) -> NamePtr<'t> {
        match self.read_name(n2) {
            Anon => n1,
            Str(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.num(pfx, sfx)
            }
        }
    }

    pub(crate) fn append_index_after(&mut self, n: NamePtr<'t>, idx: u64) -> NamePtr<'t> {
        match self.read_name(n) {
            Str(pfx, sfx, ..) => {
                let s = self.read_string(sfx);
                let s = self.alloc_string(CowStr::Owned(format!("{}_{}", s, idx)));
                self.str(pfx, s)
            }
            _ => {
                let s = self.alloc_string(CowStr::Owned(format!("_{}", idx)));
                self.str(n, s)
            }
        }
    }

    pub(crate) fn replace_pfx(&mut self, n: NamePtr<'t>, outgoing: NamePtr<'t>, incoming: NamePtr<'t>) -> NamePtr<'t> {
        match self.read_name(n) {
            Anon => match self.read_name(outgoing) {
                Anon => incoming,
                _ => self.anonymous(),
            },
            Str(..) | Num(..) if n == outgoing => incoming,
            Str(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.num(pfx, sfx)
            }
        }
    }
}
