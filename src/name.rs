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
    pub(crate) fn name_components(&self, n: NamePtr<'t>) -> Vec<NameComponent> {
        match self.read_name(n) {
            Anon => Vec::new(),
            Str(pfx, sfx, _) => {
                let mut components = self.name_components(pfx);
                components.push(NameComponent::Str(self.read_string(sfx).to_string()));
                components
            }
            Num(pfx, sfx, _) => {
                let mut components = self.name_components(pfx);
                components.push(NameComponent::Num(sfx));
                components
            }
        }
    }

    pub(crate) fn name_from_components(&mut self, components: &[NameComponent]) -> NamePtr<'t> {
        let mut out = self.anonymous();
        for component in components {
            out = match component {
                NameComponent::Str(s) => {
                    let s = self.alloc_string(CowStr::Owned(s.clone()));
                    self.str(out, s)
                }
                NameComponent::Num(n) => self.num(out, *n),
            };
        }
        out
    }

    pub(crate) fn get_pfx(&self, mut n: NamePtr<'t>) -> NamePtr<'t> {
        let anonymous = self.anonymous();
        loop {
            match self.read_name(n) {
                Anon => return n,
                Str(pfx, ..) | Num(pfx, ..) => { 
                    if pfx == anonymous {
                        return n
                    } else {
                        n = pfx 
                    }
                },
            }
        }
    }

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

// Identifier characters, following `isLetterLike`, `isSubScriptAlnum`, `isIdFirst` and `isIdRest` in
// https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Init/Meta/Defs.lean#L101-L134
fn is_letter_like(c: char) -> bool {
    let c = c as u32;
    ((0x3b1..=0x3c9).contains(&c) && c != 0x3bb) // Lower greek, but lambda
        || ((0x391..=0x3a9).contains(&c) && c != 0x3a0 && c != 0x3a3) // Upper greek, but Pi and Sigma
        || (0x3ca..=0x3fb).contains(&c) // Coptic letters
        || (0x1f00..=0x1ffe).contains(&c) // Polytonic Greek Extended Character Set
        || (0x2100..=0x214f).contains(&c) // Letter like block
        || (0x1d49c..=0x1d59f).contains(&c) // Latin letters, Script, Double-struck, Fractur
        || ((0xc0..=0xff).contains(&c) && c != 0xd7 && c != 0xf7) // Latin-1 supplement letters but × and ÷
        || (0x100..=0x17f).contains(&c) // Latin Extended-A
}

fn is_sub_script_alnum(c: char) -> bool {
    let c = c as u32;
    (0x2080..=0x2089).contains(&c) || (0x2090..=0x209c).contains(&c) || (0x1d62..=0x1d6a).contains(&c) || c == 0x2c7c
}

pub(crate) fn is_id_first(c: char) -> bool { c.is_ascii_alphabetic() || c == '_' || is_letter_like(c) }

pub(crate) fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?') || is_letter_like(c) || is_sub_script_alnum(c)
}

fn is_id(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(is_id_first) && chars.all(is_id_rest)
}

/// A name component. Outside the export file's name table, a name is a `Vec<NameComponent>` in
/// source order, e.g. `Quot.sound` is `[Str("Quot"), Str("sound")]`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum NameComponent {
    Str(String),
    Num(u64),
}

/// Parses a name like Lean's `String.toName`: components are separated by `.`, a component written
/// between `«` and `»` is taken as is, and a run of digits is a numeric component, e.g. `Quot.sound`,
/// `«Quot.sound»` or `Foo.«bar baz».1`.
///
/// Where `String.toName` would give the anonymous name (empty or malformed input), this gives `None`,
/// as it does for a numeric component that doesn't fit in a `u64`.
pub(crate) fn parse_name(s: &str) -> Option<Vec<NameComponent>> {
    let mut components = Vec::new();
    let mut rest = s;
    loop {
        let c = rest.chars().next()?;
        let (component, tail) = if let Some(escaped) = rest.strip_prefix('«') {
            let (inner, tail) = escaped.split_once('»')?;
            (NameComponent::Str(inner.to_string()), tail)
        } else if is_id_first(c) {
            let end = rest.find(|c| !is_id_rest(c)).unwrap_or(rest.len());
            (NameComponent::Str(rest[..end].to_string()), &rest[end..])
        } else if c.is_ascii_digit() {
            let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
            (NameComponent::Num(rest[..end].parse().ok()?), &rest[end..])
        } else {
            return None
        };
        components.push(component);
        if tail.is_empty() {
            return Some(components)
        }
        rest = tail.strip_prefix('.')?;
    }
}

/// Formats a name for messages. String components that are not identifiers are escaped with `«»` as
/// in Lean's `Name.toString`, except that escaping is never turned off (Lean prints e.g. hygienic and
/// inaccessible names without it). A component that contains `»` can't be escaped and is left as is.
pub(crate) fn format_name(components: &[NameComponent]) -> String {
    if components.is_empty() {
        return "[anonymous]".to_string()
    }
    components
        .iter()
        .map(|component| match component {
            NameComponent::Str(s) if is_id(s) || s.contains('»') => s.clone(),
            NameComponent::Str(s) => format!("«{}»", s),
            NameComponent::Num(n) => n.to_string(),
        })
        .collect::<Vec<_>>()
        .join(".")
}
