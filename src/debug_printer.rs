use crate::expr::Expr::*;
use crate::level::Level;
use crate::name::Name;
use crate::util::{ExprPtr, LevelPtr, NamePtr, TcCtx};

pub struct DebugPrinter<'x, 't, 'p, A> {
    pub(crate) ctx: &'x TcCtx<'t, 'p>,
    pub(crate) elem_to_print: A,
}

impl<'x, 't: 'x, 'p: 't> TcCtx<'t, 'p> {
    pub fn debug_print<A>(&'x self, elem_to_print: A) -> DebugPrinter<'x, 't, 'p, A> {
        DebugPrinter { ctx: self, elem_to_print }
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, NamePtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Name::*;
        match self.ctx.read_name(self.elem_to_print) {
            Anon => Ok(()),
            Str(pfx, sfx, _) => {
                let sfx = self.ctx.read_string(sfx);
                match self.ctx.read_name(pfx) {
                    Anon => write!(f, "{}", sfx),
                    _ => write!(f, "{:?}.{}", self.ctx.debug_print(pfx), sfx),
                }
            }
            Num(pfx, sfx, _) => match self.ctx.read_name(pfx) {
                Anon => write!(f, "{}", sfx),
                _ => write!(f, "{:?}.{}", self.ctx.debug_print(pfx), sfx),
            },
        }
    }
}

use std::fmt;
impl<'x, 't, 'p, A, B> std::fmt::Debug for DebugPrinter<'x, 't, 'p, (A, B)>
where
    A: Copy,
    B: Copy,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
    DebugPrinter<'x, 't, 'p, B>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({:?}, {:?})",
            self.ctx.debug_print(self.elem_to_print.0),
            self.ctx.debug_print(self.elem_to_print.1)
        )
    }
}
impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, &[A]>
where
    A: Copy,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.elem_to_print.iter().copied().map(|x| self.ctx.debug_print(x))).finish()
    }
}

impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, Vec<A>>
where
    A: Clone,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.elem_to_print.clone().into_iter().map(|x| self.ctx.debug_print(x))).finish()
    }
}
impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, std::rc::Rc<A>>
where
    A: Clone,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &self.ctx.debug_print(self.elem_to_print.as_ref().clone()))
    }
}
impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, Option<A>>
where
    A: Copy,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.elem_to_print {
            None => write!(f, "None"),
            Some(ref x) => write!(f, "Some({:?})", self.ctx.debug_print(*x)),
        }
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, LevelPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Level::*;
        match self.ctx.read_level(self.elem_to_print) {
            Zero => write!(f, "0"),
            Succ(..) => {
                let (val, n) = self.ctx.level_succs(self.elem_to_print);
                if self.ctx.read_level(val) == Zero {
                    write!(f, "{}", n)
                } else {
                    write!(f, "{:?} + {}", self.ctx.debug_print(val), n)
                }
            }
            Max(l, r, _) => {
                write!(f, "max{:?}", self.ctx.debug_print((l, r)))
            }
            IMax(l, r, _) => {
                write!(f, "imax{:?}", self.ctx.debug_print((l, r)))
            }
            Param(name, _) => {
                write!(f, "{:?}", self.ctx.debug_print(name))
            }
        }
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, ExprPtr<'t>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ctx.read_expr(self.elem_to_print) {
            Var { dbj_idx, .. } => write!(f, "${}", dbj_idx),
            Sort { level, .. } => write!(f, "Sort({:?})", self.ctx.debug_print(level)),
            Const { name, levels, .. } => {
                let levels = self.ctx.read_levels(levels);
                write!(f, "{:?}.{:?}", self.ctx.debug_print(name), self.ctx.debug_print(levels.as_ref()))
            }
            App { fun, arg, .. } => write!(f, "({:?} {:?})", self.ctx.debug_print(fun), self.ctx.debug_print(arg)),
            Let { binder_name, val, binder_type: binder, body, .. } => {
                write!(
                    f,
                    "let {:?} : {:?} := {:?} in {:?}",
                    self.ctx.debug_print(binder_name),
                    self.ctx.debug_print(binder),
                    self.ctx.debug_print(val),
                    self.ctx.debug_print(body)
                )
            }
            Pi { binder_name, binder_type, body, .. } => {
                write!(
                    f,
                    "Pi ({:?} : {:?}), {:?}",
                    self.ctx.debug_print(binder_name),
                    self.ctx.debug_print(binder_type),
                    self.ctx.debug_print(body)
                )
            }
            Lambda { binder_name, binder_type, body, .. } => {
                write!(
                    f,
                    "fun ({:?} : {:?}) => {:?}",
                    self.ctx.debug_print(binder_name),
                    self.ctx.debug_print(binder_type),
                    self.ctx.debug_print(body)
                )
            }
            Local { binder_name, binder_type, id, .. } => {
                write!(
                    f,
                    "#({:?}, {:?} : {:?})",
                    self.ctx.debug_print(binder_name),
                    id,
                    self.ctx.debug_print(binder_type)
                )
            }
            Proj { idx, structure, .. } => {
                write!(f, "%({:?}).{}", self.ctx.debug_print(structure), idx)
            }
            NatLit { ptr, .. } => write!(f, "NLit({})", self.ctx.read_bignum(ptr).unwrap()),
            StringLit { ptr, .. } => write!(f, "SLit({})", self.ctx.read_string(ptr)),
        }
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, crate::util::LevelsPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.ctx.read_levels(self.elem_to_print))
    }
}
impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, crate::util::StringPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.ctx.read_string(self.elem_to_print))
    }
}
impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, crate::util::BigUintPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.ctx.read_bignum(self.elem_to_print).unwrap())
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, &crate::env::DeclarInfo<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeclarInfo")
            .field("name", &self.ctx.debug_print(self.elem_to_print.name))
            .field("ty", &self.ctx.debug_print(self.elem_to_print.ty))
            .field("uparams", &self.ctx.debug_print(self.ctx.read_levels(self.elem_to_print.uparams).as_ref()))
            .finish()
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, crate::env::RecRule<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RecRule")
            .field("ctor_name", &self.ctx.debug_print(self.elem_to_print.ctor_name))
            .field("ctor_telescope_size_wo_params", &self.elem_to_print.ctor_telescope_size_wo_params)
            .field("val", &self.ctx.debug_print(self.elem_to_print.val))
            .finish()
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, crate::tc::DeltaResult<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.elem_to_print {
            crate::tc::DeltaResult::FoundEqResult(b) => write!(f, "DeltaResult::FoundEqResult({})", b),
            crate::tc::DeltaResult::Exhausted(e1, e2) => f
                .debug_struct("DeltaResult::Exhausted")
                .field("lhs", &self.ctx.debug_print(e1))
                .field("rhs", &self.ctx.debug_print(e2))
                .finish(),
        }
    }
}

impl<'x, 't, 'p> std::fmt::Debug for DebugPrinter<'x, 't, 'p, crate::env::ReducibilityHint> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{:?}", self.elem_to_print) }
}
