use crate::util::{ExprPtr, FxHashMap, FxIndexMap, LevelsPtr, NamePtr};
use std::sync::Arc;
use serde::Deserialize;

/// Reducibility hints accompany definitions; used to determine how
/// to unfold expressions in order to most efficiently proceed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum ReducibilityHint {
    #[serde(rename = "opaque")]
    Opaque,
    #[serde(rename = "regular")]
    Regular(u16),
    #[serde(rename = "abbrev")]
    Abbrev,
}

impl ReducibilityHint {
    /// Check whether `self` is "less than" `other` in terms of reducibility; during
    /// delta reduction in equality checking, we want to unfold the greater of the two
    /// definitions to try and bring the two closer.
    pub(crate) fn is_lt(&self, other: &Self) -> bool {
        use ReducibilityHint::*;
        match (self, other) {
            (_, Opaque) => false,
            (Abbrev, _) => false,
            (Opaque, _) => true,
            (_, Abbrev) => true,
            (Regular(h1), Regular(h2)) => h1 < h2,
        }
    }
}

/// Convenience declaration for the elements common across all kinds
/// of declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarInfo<'a> {
    pub name: NamePtr<'a>,
    pub uparams: LevelsPtr<'a>,
    pub ty: ExprPtr<'a>,
}

/// Computation rules for iota-reduction (pattern matching).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecRule<'a> {
    pub ctor_name: NamePtr<'a>,
    /// the constructor's telescope size minus the params (but including indices).
    /// So a constructor with 2 params, 1 index, and 4 args is (1 + 4) = 5.
    pub ctor_telescope_size_wo_params: u16,
    pub val: ExprPtr<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declar<'a> {
    Axiom { info: DeclarInfo<'a> },
    Quot { info: DeclarInfo<'a> },
    Theorem { info: DeclarInfo<'a>, val: ExprPtr<'a> },
    Definition { info: DeclarInfo<'a>, val: ExprPtr<'a>, hint: ReducibilityHint },
    Opaque { info: DeclarInfo<'a>, val: ExprPtr<'a> },
    Inductive(InductiveData<'a>),
    Constructor(ConstructorData<'a>),
    Recursor(RecursorData<'a>),
}

/// This structure is what's taken from the export file; it contains enough
/// information to begin the process of checking an inductive declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveData<'a> {
    pub(crate) info: DeclarInfo<'a>,
    /// `true` when recursive (that is, the inductive type appears as an argument in a constructor).
    pub(crate) is_recursive: bool,
    /// `true` when this typs is a nested inductive
    #[allow(dead_code)]
    pub(crate) is_nested: bool,
    /// All inductive types in a mutual block must have the same parameters, though this
    /// does not exactly hold for nested inductives.
    pub(crate) num_params: u16,
    pub(crate) num_indices: u16,
    /// The names of this type, and any other inductive types in a `mutual..end`
    /// block. No nested inductive info is conveyed here.
    pub(crate) all_ind_names: Arc<[NamePtr<'a>]>,
    /// The constructor names for THIS type only. No constructors
    /// from other elements in a mutual block, nothing from any nested
    /// construction.
    pub(crate) all_ctor_names: Arc<[NamePtr<'a>]>,
}

/// `inductive_name` is the name of the type this constructs. e.g. `Prod` for `Prod.mk`
///
/// `ctor_idx` is 0-based; e.g. `List.nil (ctor_idx := 0)`, `List.cons (ctor_idx := 1)`
///
/// num_params is the number of parameters in the inductive specification, not including ctor args;
/// num_fields is the number of ctor args, not including parameters.
///
/// `Prod.mk (A B) (a b) ;;
/// (num_params := 2) (num_fields := 2)`
///
/// `HAppend.mk {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) → HAppend α β γ
/// (num_params := 3) (num_fields := 1)`
///
/// `Syntax.node (num_params := 0) (num_fields := 3)`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorData<'a> {
    pub info: DeclarInfo<'a>,
    pub inductive_name: NamePtr<'a>,
    pub ctor_idx: u16,
    /// The number of parameters, not including ctor args
    pub num_params: u16,
    /// The number of ctor args, not including parameters.
    pub num_fields: u16,
}

/// Information received from the export file regarding a recursor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorData<'a> {
    pub info: DeclarInfo<'a>,
    pub all_inductives: Arc<[NamePtr<'a>]>,
    pub num_params: u16,
    pub num_indices: u16,
    pub num_motives: u16,
    pub num_minors: u16,
    pub rec_rules: Arc<[RecRule<'a>]>,
    pub is_k: bool,
}

impl<'a> RecursorData<'a> {
    /// Compute the index in the recursor's type (in the telescope) where the major premise is located. 
    pub fn major_idx(&self) -> usize {
        (self.num_params + self.num_motives + self.num_minors + self.num_indices) as usize
    }
}

impl<'a> Declar<'a> {
    pub fn info(&self) -> &DeclarInfo<'a> {
        use Declar::*;
        match self {
            Axiom { info, .. }
            | Quot { info, .. }
            | Theorem { info, .. }
            | Definition { info, .. }
            | Inductive(InductiveData { info, .. })
            | Constructor(ConstructorData { info, .. })
            | Recursor(RecursorData { info, .. })
            | Opaque { info, .. } => info,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Notation<'a> {
    Prefix { name: NamePtr<'a>, priority: usize, oper: Arc<str> },
    Infix { name: NamePtr<'a>, priority: usize, oper: Arc<str> },
    Postfix { name: NamePtr<'a>, priority: usize, oper: Arc<str> },
}

impl<'a> Notation<'a> {
    pub fn new_prefix(name: NamePtr<'a>, priority: usize, oper: Arc<str>) -> Self {
        Notation::Prefix { name, priority, oper }
    }

    pub fn new_infix(name: NamePtr<'a>, priority: usize, oper: Arc<str>) -> Self {
        Notation::Infix { name, priority, oper }
    }

    pub fn new_postfix(name: NamePtr<'a>, priority: usize, oper: Arc<str>) -> Self {
        Notation::Postfix { name, priority, oper }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum EnvLimit<'a> {
    Empty,
    ByIndex(usize),
    ByName(NamePtr<'a>),
    PpUnlimited
}

/// A Lean environment, which consists of a set of declarations that my have a temporary
/// extension, and some notation items. The temporary extensions are used to acommodate
/// the specialization process needed for checking nested inductives.
///
/// When a tyep checker looks up a declaration in the environment, it will check the temporary
/// extension first if there is one, then fall back to the persistent map.
pub struct Env<'x, 'a: 'x> {
    declars: &'a FxIndexMap<NamePtr<'a>, Declar<'a>>,
    /// Used for checking nested inductives.
    temp_declars: Option<&'x FxIndexMap<NamePtr<'a>, Declar<'a>>>,
    #[allow(dead_code)]
    pub(crate) notation: &'a FxHashMap<NamePtr<'a>, Notation<'a>>,
    /// `cutoff` is used to mark the end of what should be the "visible" environment.
    /// This allows us to make the complete environment at parse time, and then control visibility
    /// between threads by only making a particular slice of that environment available to a thread.
    cutoff: usize,
}

pub(crate) type DeclarMap<'a> = FxIndexMap<NamePtr<'a>, Declar<'a>>;
pub(crate) type NotationMap<'a> = FxHashMap<NamePtr<'a>, Notation<'a>>;

impl<'x, 'a: 'x> Env<'x, 'a> {
    /// Create a new environment (without any temporary extension)
    pub fn new(declars: &'a DeclarMap<'a>, notation: &'a NotationMap<'a>, limit: EnvLimit<'a>) -> Self {
        Self::new_w_temp_ext(declars, None, notation, limit)
    }

    /// Create a new environment that includes some temporary extension; the temporary
    /// extension is used for checking nested inductives.
    pub fn new_w_temp_ext(
        declars: &'a DeclarMap<'a>,
        temp_declars: Option<&'x DeclarMap<'a>>,
        notation: &'a NotationMap<'a>,
        limit: EnvLimit<'a>
    ) -> Self {
        let cutoff = match limit {
            EnvLimit::Empty => 0,
            EnvLimit::ByIndex(idx) => idx,
            EnvLimit::PpUnlimited => declars.len(),
            EnvLimit::ByName(n) => declars.get_index_of(&n).unwrap_or(0),
        };
        Self { declars, cutoff, temp_declars, notation }
    }

    /// Retrieve a declaration by first checking the contents of any temporary extension,
    /// then checking the persistent environment.
    pub fn get_declar(&self, n: &NamePtr<'a>) -> Option<&Declar<'a>> {
        self.temp_declars.as_ref().and_then(|ext| ext.get(n)).or_else(|| self.get_old_declar(n))
    }

    /// Get a declaration, only looking in the temporary extension.
    pub fn get_temp_declar(&self, n: &NamePtr<'a>) -> Option<&Declar<'a>> {
        self.temp_declars.as_ref().and_then(|ext| ext.get(n))
    }

    /// Get a declaration, bypassing the temporary extension, only searching in
    /// the persistent set of declarations.
    pub fn get_old_declar(&self, n: &NamePtr<'a>) -> Option<&Declar<'a>> { 
        let (idx, _, v) = self.declars.get_full(n)?;
        if idx < self.cutoff {
            Some(v)
        } else {
            None
        }
    }

    pub fn get_inductive(&self, n: &NamePtr<'a>) -> Option<&InductiveData<'a>> {
        match self.get_declar(n) {
            Some(Declar::Inductive(i)) => Some(i),
            _ => None,
        }
    }

    pub fn get_recursor(&self, n: &NamePtr<'a>) -> Option<&RecursorData<'a>> {
        match self.get_declar(n) {
            Some(Declar::Recursor(r)) => Some(r),
            _ => None,
        }
    }

    pub fn get_constructor(&self, n: &NamePtr<'a>) -> Option<&ConstructorData<'a>> {
        match self.get_declar(n) {
            Some(Declar::Constructor(c)) => Some(c),
            _ => None,
        }
    }

    /// Returns `true` iff the inductive type declaration associated with `n` has the
    /// characteristics required of a structure. The requirements to be a structure are
    /// (1) the inductive declaration is not recursive, (2) the declaration has only one
    /// constructor, and (3) the type is declared with no indices.
    pub(crate) fn can_be_struct(&self, n: &NamePtr<'a>) -> bool {
        match self.get_inductive(n) {
            Some(InductiveData { is_recursive, num_indices, all_ctor_names, .. }) =>
                (!is_recursive) && (all_ctor_names.len() == 1) && (*num_indices == 0),
            _ => false,
        }
    }

    /// Get the value of a declaration, if that declaration has an associated value (only
    /// definitions and theorems have values). Also returns the declaration's universe parameters.
    pub fn get_declar_val(&self, n: &NamePtr<'a>) -> Option<(LevelsPtr<'a>, ExprPtr<'a>)> {
        match self.get_declar(n)? {
            Declar::Definition { info, val, .. } | Declar::Theorem { info, val, .. } => Some((info.uparams, *val)),
            _ => None,
        }
    }
}
