use std::cmp::Ordering::*;
use hashbrown::HashMap;
use once_cell::sync::Lazy;
use nanoda_macros::trace;

use Cheap::*;
use crate::ret_none_if;
use crate::utils::{ 
                    Either, 
                    FailureCache, 
                    Either::*, 
                    DeltaResult, 
                    DeltaResult::*, 
                    ShortCircuit, 
                    ShortCircuit::*, 
                    SSOption, 
                    Judgment,
                    EqCache };
use crate::name::Name;
use crate::level::{ Level, 
                    mk_imax, 
                    mk_succ, 
                    is_def_eq_lvls };
use crate::env::{ ArcEnv, ConstantInfo };
use crate::errors::*;
use crate::recursor::RecursorVal;
use crate::expr::{ Expr, 
                   mk_var,
                   mk_sort,
                   mk_const, 
                   mk_app,
                   mk_pi,
                   mk_lambda,
                   mk_prop,
                   Binder, InnerExpr::*, };
use crate::trace::{ ArcTraceMgr, Tracer };

pub static QLIFT    : Lazy<Name> = Lazy::new(|| Name::from("quot").extend_str("lift"));
pub static QMK      : Lazy<Name> = Lazy::new(|| Name::from("quot").extend_str("mk"));
pub static QIND     : Lazy<Name> = Lazy::new(|| Name::from("quot").extend_str("ind"));
pub static ID_DELTA : Lazy<Name> = Lazy::new(|| Name::from("id_delta"));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Cheap {
    CheapTrue,
    CheapFalse,
}

#[derive(Clone)]
pub struct TypeChecker<T : Tracer> {
    pub m_safe_only : bool,
    pub infer_cache : HashMap<Expr, Expr>,
    pub eq_cache : EqCache,
    pub whnf_cache : HashMap<Expr, Expr>,
    pub env : ArcEnv,
    pub m_lparams : Option<Vec<Level>>,
    pub failure_cache : FailureCache,
    pub quot_is_init : bool,
    pub trace_mgr : ArcTraceMgr<T>,
}


impl<T : Tracer> std::fmt::Debug for TypeChecker<T> {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "<typechecker>")
    }
}

impl<T : Tracer> std::cmp::PartialEq for TypeChecker<T> {
    fn eq(&self, _ : &TypeChecker<T>) -> bool {
        true
    }
}

impl<T : Tracer> std::cmp::Eq for TypeChecker<T> {}

impl<T : Tracer> TypeChecker<T> {
    pub fn new(safe_only : Option<bool>, env : ArcEnv, trace_mgr : ArcTraceMgr<T>) -> Self {
        let quot_is_init = env.read().quot_is_init;
        TypeChecker {
            m_safe_only : safe_only.unwrap_or(false),
            infer_cache : HashMap::with_capacity(500),
            eq_cache : EqCache::with_capacity(500),
            whnf_cache : HashMap::with_capacity(500),
            env,
            m_lparams : None,
            failure_cache : FailureCache::with_capacity(500),
            quot_is_init,
            trace_mgr,
        }
    }

    pub fn set_safe_only(&mut self, safe_only : Option<bool>) {
        std::mem::replace(&mut self.m_safe_only, safe_only.unwrap_or(false));
    }

    pub fn swap_tracer(&mut self, t : ArcTraceMgr<T>) {
        std::mem::replace(&mut self.trace_mgr, t);
    }

}


// Basically just instantiate_lparams for a ConstantInfo it it's one 
// that has a Value with some optimizations.
#[trace(trace_mgr, InstantiateValueLparam(const_info, ls))]
pub fn instantiate_value_lparams(const_info : &ConstantInfo, ls : &Vec<Level>, trace_mgr : &ArcTraceMgr<impl Tracer>) -> Expr {
    if (const_info.get_constant_base().lparams.len() != ls.len()) {
        err_mismatch_lparams(line!(), const_info, ls)
    } else if (!const_info.has_value(None)) {
        err_no_value(line!(), const_info)
   } else {
        let zip = const_info.get_constant_base().lparams.iter().zip(ls.iter());
        const_info.get_value().instantiate_lparams_trace(trace_mgr, zip)
    }
}


#[trace(trace_mgr, CheckLevel(m_lparams.clone(), l))]
pub fn check_level(m_lparams : Option<&Vec<Level>>, l : &Level, trace_mgr : &ArcTraceMgr<impl Tracer>) {
    if let Some(set) = m_lparams {
        match l.get_undef_param(set) {
            Some(bad) => err_bad_sort(line!(), bad),
            _ => ()
        }
    }
}

/*
#[derive(Clone)]
pub struct LcCache {
    inner : HashMap<Expr, Vec<Expr>>
}

impl LcCache {
    pub fn new() -> Self {
        LcCache {
            inner : HashMap::with_capacity(500)
        }
    }



    pub fn get_lc(&mut self, b : &Binder) -> Expr {
        match self.inner.get_mut(&b.type_) {
            Some(v) => {
                match v.pop() {
                    Some(l) => {
                        l
                    }
                    None => b.clone().as_local()
                }
            },
            None => {
                b.clone().as_local()
            }
        }
    }

    pub fn replace_lc(&mut self, b : Binder, lc : Expr) {
        match self.inner.get_mut(&b.type_) {
            Some(v) => {
                v.push(lc);
            }
            None => {
                let mut _v = Vec::with_capacity(100);
                _v.push(lc);
                //self.inner.insert(b.type_, vec![lc]);
                self.inner.insert(b.type_, _v);
            }
        }
    }

    pub fn replace_lcs(&mut self, mut bs : Vec<Binder>, mut lcs : Vec<Expr>) {
        assert_eq!(bs.len(), lcs.len());
        while !bs.is_empty() {
            let b = bs.pop().unwrap();
            let l = lcs.pop().unwrap();
            self.replace_lc(b, l);
        }
    }
}
*/


#[trace(tc.trace_mgr, InferConst(n, ls))]
pub fn infer_const(n : &Name, ls : &Vec<Level>, infer_only : bool, tc : &mut TypeChecker<impl Tracer>) -> Expr {
    let _x = tc.env.read().get_constant_info(n);
    if let Some(const_info) = _x {
        assert_eq!(ls.len(), const_info.get_constant_base().lparams.len());
        if !infer_only {
            if ((tc.m_safe_only) && const_info.is_unsafe()) {
                panic!("Cannot check an unsafe definition in this manner")
            }

            ls.iter().for_each(|l| check_level(tc.m_lparams.as_ref(), l, &tc.trace_mgr))
        }

        const_info.get_constant_base()
        .type_
        .instantiate_lparams_trace(&tc.trace_mgr, const_info.get_constant_base().lparams.iter().zip(ls))
    } else {
        err_infer_const(line!(), n)
    }
}

#[trace(tc.trace_mgr, InferLet(dom, val, body, infer_only))]
pub fn infer_let(dom : &Binder, val : &Expr, body : &Expr, infer_only : bool, tc : &mut TypeChecker<impl Tracer>) -> Expr {
    if !infer_only {
        dom.type_.infer_sort(tc);
    }
    if !infer_only {
        let infd = val.infer_type_core(tc, infer_only);
        assert!(infd.check_def_eq(&dom.type_, tc) == EqShort)
    }

    let instd_body = body.instantiate_trace(tc.trace_mgr.clone(), Some(val).into_iter());
    instd_body.infer_type_core(tc, infer_only)
}

impl Expr {

    #[trace(tc.trace_mgr, CheckType(self, type_))]
    pub fn check_type__(&self, type_ : &Expr, tc : &mut TypeChecker<impl Tracer>) -> Judgment {
        match self.infer_type_core(tc, false)
                  .check_def_eq(type_, tc) {
            EqShort => Judgment::OK,
            _ => {
                err_check_type(line!(), self, type_)
            }
        }
    }

    #[trace(tc.trace_mgr, CheckedInfer(self, &lparams))]
    pub fn checked_infer(&self, lparams : Vec<Level>, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        tc.m_lparams = Some(lparams);
        self.infer_type_core(tc, false)
    }

    #[trace(tc.trace_mgr, UncheckedInfer(self))]
    pub fn unchecked_infer(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        self.infer_type(tc)
    }

    #[trace(tc.trace_mgr, InferType(self))]
    pub fn infer_type(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        self.infer_type_core(tc, true)
    }

    #[trace(tc.trace_mgr, InferSort(self))]
    pub fn infer_sort(&self, tc : &mut TypeChecker<impl Tracer>) -> Level {
        match self.infer_type_core(tc, false)
                  .whnf(tc)
                  .as_ref() {
            Sort { level, .. } => level.clone(),
            owise => err_infer_universe(line!(), owise)
        }
    }

    // If we've already inferred this expression, return the cached result.
    // Otherwise, dispatch the term to the correct function based
    // on its discriminant, and cache the eventual result.
    #[trace(tc.trace_mgr, InferTypeCore(self))]
    pub fn infer_type_core(&self, tc : &mut TypeChecker<impl Tracer>, infer_only : bool) -> Expr {
        if let Some(cached) = tc.infer_cache.get(self) {
            cached.clone()
        } else {
            let result = match self.as_ref() {
                Sort { level, .. } => {
                    //EXAMPLE
                    //tc.trace_mgr.write().push_extra(format!("sort_arm"));
                    //
                    if !infer_only {
                        check_level(tc.m_lparams.as_ref(), level, &tc.trace_mgr);
                    }
                    mk_sort(mk_succ(level.clone()))
                },
                Const { name, levels, .. } => infer_const(name, levels, infer_only, tc),
                App    {..} => self.infer_apps(infer_only, tc),
                Pi {..} => self.infer_pi(tc),
                Lambda {..} => self.infer_lambda(infer_only, tc),
                Let    { binder, val, body, .. } => infer_let(binder, val, body, infer_only, tc),
                Local  { binder, .. } => binder.type_.clone(),
                owise => err_infer_var(line!(), owise)
            };

            tc.infer_cache.insert(self.clone(), result.clone());
            result
        }
    }


    #[trace(tc.trace_mgr, EnsureType(self))]
    pub fn ensure_type(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        self.unchecked_infer(tc).ensure_sort(tc)
    }

    #[trace(tc.trace_mgr, EnsurePi(self.clone()))]
    pub fn ensure_pi(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        self.ensure_pi_core(tc)
    }

    #[trace(tc.trace_mgr, EnsurePiCore(self.clone()))]
    pub fn ensure_pi_core(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        if self.as_ref().is_pi() {
            self.clone()
        } else {
            match self.whnf(tc) {
                whnfd if whnfd.as_ref().is_pi() => whnfd,
                owise => panic!("ensure_pi_core expected to produce a Pi, got {:#?}\n", owise)
            }
        }
    }

    #[trace(tc.trace_mgr, EnsureSort(self.clone()))]
    pub fn ensure_sort(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        self.ensure_sort_core(tc)
    }

    #[trace(tc.trace_mgr, EnsureSortCore(self.clone()))]
    pub fn ensure_sort_core(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        if self.as_ref().is_sort() {
            self.clone()
        } else {
            match self.whnf(tc) {
                whnfd if whnfd.as_ref().is_sort() => whnfd,
                owise => panic!("Ensure sort_core expected to produce a Sort, got {:#?}\n", owise)
            }
       }
    }



    #[trace(tc.trace_mgr, CheckDefEq(self.clone(), other.clone()))]
    pub fn check_def_eq(&self, other :&Expr, tc : &mut TypeChecker<impl Tracer>) -> ShortCircuit {
        tc.eq_cache.get(self, other).unwrap_or_else(|| {
            let result = if self == other {
                EqShort
            } else {
                self.check_def_eq_core(other, tc)
            };
            tc.eq_cache.insert(self.clone(), other.clone(), result);
            result
        })
    }




    // Change this so that it only checks the cache when given
    // a flag (IE the 2nd time around after whnf_core, when whnf_core)
    // has succeeded in reduction in some form.
    #[trace(tc.trace_mgr, QuickDefEq(self.clone(), other.clone()))]
    pub fn quick_def_eq(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> Option<ShortCircuit> {
        if let Some(cached) = tc.eq_cache.get(self, other) {
            Some(cached)
        } else if (self == other) {
            Some(EqShort)
        } else {
            match (self.as_ref(), other.as_ref()) {
                (Sort { level : level1, .. }, Sort { level : level2, .. }) => {
                    match level1.eq_by_antisymm(level2, &tc.trace_mgr) {
                        true => Some(EqShort),
                        false => Some(NeqShort)
                    }
                },
                (Lambda {..}, Lambda {..}) => Some(self.def_eq_lambdas(other, tc)),
                (Pi {..}, Pi {..}) => Some(self.def_eq_pis(other, tc)),
                _ => None
            }
        }
    }

    #[trace(tc.trace_mgr, DefEqLambdas(self.clone(), other.clone()))]
    pub fn def_eq_lambdas(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> ShortCircuit {
        let mut lhs_cursor = self;
        let mut rhs_cursor = other;
        let mut substs = Vec::new();
        while let (Lambda { binder : dom1, body : body1, .. }, Lambda { binder : dom2, body : body2, .. }) = (lhs_cursor.as_ref(), rhs_cursor.as_ref()) {
            let mut lhs_type = None;

            if dom1 != dom2 {
                let instd_d2_ty = dom2.type_.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
                let instd_d1_ty = dom1.type_.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
                lhs_type = Some(dom2.clone().swap_ty(instd_d2_ty.clone()));
                if (instd_d1_ty.check_def_eq(&instd_d2_ty, tc) == NeqShort) {
                    return NeqShort
                }
            }

            if (body1.has_vars() || body2.has_vars()) {
                let new_local = match lhs_type {
                    Some(elem) => elem.as_local(),
                    None => {
                        let mut _x = dom2.clone();
                        let new_ty = _x.type_.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
                        _x.swap_ty(new_ty).as_local()
                    }
                };
                substs.push(new_local);
            }  else { 
                substs.push(mk_prop()) 
            }

            lhs_cursor = body1;
            rhs_cursor = body2;
         }

         let lhs = lhs_cursor.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
         let rhs = rhs_cursor.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
         lhs.check_def_eq(&rhs, tc)
   }
    
   #[trace(tc.trace_mgr, DefEqPis(self.clone(), other.clone()))]
    pub fn def_eq_pis(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> ShortCircuit {
        let mut lhs_cursor = self;
        let mut rhs_cursor = other;
        let mut substs = Vec::new();
        while let (Pi { binder : dom1, body : body1, .. }, Pi { binder : dom2, body : body2, .. }) = (lhs_cursor.as_ref(), rhs_cursor.as_ref()) {
            let mut lhs_type = None;

            if dom1 != dom2 {
                let instd_d2_ty = dom2.type_.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
                let instd_d1_ty = dom1.type_.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
                lhs_type = Some(dom2.clone().swap_ty(instd_d2_ty.clone()));
                if (instd_d1_ty.check_def_eq(&instd_d2_ty, tc) == NeqShort) {
                    return NeqShort
                }
            }

            if (body1.has_vars() || body2.has_vars()) {
                let new_local = match lhs_type {
                    Some(elem) => elem.as_local(),
                    None => {
                        let mut _x = dom2.clone();
                        let new_ty = _x.type_.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
                        _x.swap_ty(new_ty).as_local()
                    }
                };
                substs.push(new_local);
            }  else { 
                substs.push(mk_prop()) 
            }

            lhs_cursor = body1;
            rhs_cursor = body2;
         }

         let lhs = lhs_cursor.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
         let rhs = rhs_cursor.instantiate_trace(tc.trace_mgr.clone(), substs.iter().rev());
         lhs.check_def_eq(&rhs, tc)

    }

    #[trace(tc.trace_mgr, EqCore(self.clone(), other.clone()))]
    pub fn check_def_eq_core(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> ShortCircuit {
        if let Some(short) = self.quick_def_eq(other, tc) {
            return short
        }

        let t_n = self.whnf_core(tc, None);
        let s_n = other.whnf_core(tc, None);

        if ((!t_n.check_ptr_eq(self)) || (!s_n.check_ptr_eq(other))) {
            if let Some(short) = t_n.quick_def_eq(&s_n, tc) {
                return short
            }
        }

        if t_n.proof_irrel_eq(&s_n, tc) {
            return EqShort
        }

        let (t_reduced, s_reduced) = match t_n.lazy_delta_reduction(&s_n, tc) {
            Left(Some(short)) => return short,
            Left(None) => unreachable!(),
            Right((e1, e2)) => (e1, e2)
        };

        if let (Const { name : n1, levels : lvls1, .. }, Const { name : n2, levels : lvls2, .. }) = (t_reduced.as_ref(), s_reduced.as_ref()) {
            if (n1 == n2) && (is_def_eq_lvls(lvls1, lvls2, &tc.trace_mgr)) {
                return EqShort
            }
        }
    
        // if two Locals have the same serial, they must
        // be clones, and are therefore definitionally equal.
        if let (Local { serial : serial1, .. }, Local { serial : serial2, .. }) = (t_reduced.as_ref(), s_reduced.as_ref()) {
            if serial1 == serial2 {
                return EqShort
            }
        }

        // Projections are not implemented
        //if let (Proj(.., pidx1, proj_expr1), Proj(.., pidx2, proj_expr2)) = (t_reduced.as_ref(), s_reduced.as_ref()) {
        //    if proj_expr1 == proj_expr2 {
        //        return true
        //    }
        //}

        if t_reduced.is_def_eq_app(&s_reduced, tc) {
            return EqShort
        }



        if t_reduced.try_eta_expansion(&s_reduced, tc) {
            return EqShort
        }

        NeqShort
    }

    /// e is a prop iff it destructures as Sort(Level(Zero))
    #[trace(tc.trace_mgr, IsProp(self.clone()))]
    pub fn is_prop(&self, tc : &mut TypeChecker<impl Tracer>) -> bool {
        match self.whnf(tc).as_ref() {
            Sort { level, .. } => level.is_zero(),
            _ => false
        }
    }

    /// tries is_prop after inferring e
    #[trace(tc.trace_mgr, IsProposition(self.clone()))]
    pub fn is_proposition(&self, tc : &mut TypeChecker<impl Tracer>) -> bool {
        self.unchecked_infer(tc).is_prop(tc)
    }



    #[trace(tc.trace_mgr, IsProof(self.clone()))]
    pub fn is_proof(&self, tc : &mut TypeChecker<impl Tracer>) -> bool {
        self.unchecked_infer(tc).is_proposition(tc)
    }

    #[trace(tc.trace_mgr, ProofIrrelEq(self.clone(), other.clone()))]
    pub fn proof_irrel_eq(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> bool {
        (self.is_proof(tc)) && (other.is_proof(tc))
    }


    #[trace(tc.trace_mgr, IsDelta(self.clone()))]
    pub fn is_delta(&self, tc : &mut TypeChecker<impl Tracer>) -> Option<ConstantInfo> {
        self.unfold_apps_fn()
            .get_const_name()
            .and_then(|name| tc.env.read().get_constant_info(name))
            .and_then(|const_info| 
                match const_info.has_value(None) {
                    true => Some(const_info),
                    false => None
            })
    }


    #[trace(tc.trace_mgr, UnfoldDefCore(self.clone()))]
    pub fn unfold_def_core(&self, tc : &mut TypeChecker<impl Tracer>) -> Option<Expr> {
        if let (Const { levels, .. }, Some(ref const_info)) = (self.as_ref(), self.is_delta(tc)) {
            if (levels.len() == const_info.get_constant_base().lparams.len()) {
                return Some(instantiate_value_lparams(const_info, levels, &tc.trace_mgr))
            }
        }
        None
    }

    #[trace(tc.trace_mgr, UnfoldDefInfallible(self.clone()))]
    pub fn unfold_def_infallible(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        self.unfold_def(tc)
        .unwrap_or_else(|| crate::errors::unfold_def_infallible_failed(line!(), self))
    }
    
    #[trace(tc.trace_mgr, UnfoldDef(self.clone()))]
    pub fn unfold_def(&self, tc : &mut TypeChecker<impl Tracer>) -> Option<Expr> {
        if let App {..} = self.as_ref() {
            self.unfold_apps_fn()
            .unfold_def_core(tc)
            .map(|unfolded| {
                unfolded.foldl_apps(self.unfold_apps_rev().1.iter().copied())
            })
        } else {
            self.unfold_def_core(tc)
        }
    }

    // FIXME figure out how to do this without allocating
    // vectors
    // The reversal here is super important; if you don't reverse this,
    // you'll hit a wall trying to check things like pi314
    #[trace(tc.trace_mgr, EqArgs(self.clone(), other.clone()))]
    pub fn eq_args(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> bool {
        let (_, t_args) = self.unfold_apps_rev();
        let (_, s_args) = other.unfold_apps_rev();

        if t_args.len() != s_args.len() {
            false 
        } else {
            t_args.into_iter()
                  .zip(s_args.into_iter())
                  .all(|(a, b)| a.check_def_eq(b, tc) == EqShort)
        }

    }

    #[trace(tc.trace_mgr, IsDefEqApp(self.clone(), other.clone()))]
    pub fn is_def_eq_app(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> bool {
        if (self.as_ref().is_app() && other.as_ref().is_app()) {
            let (t_fn, t_args) = self.unfold_apps_rev();
            let (s_fn, s_args) = other.unfold_apps_rev();

               (t_args.len() == s_args.len())
            && (t_fn.check_def_eq(s_fn, tc) == EqShort)
            && (t_args.into_iter()
                      .zip(s_args.into_iter())
                      .all(|(l, r)| l.check_def_eq(r, tc) == EqShort))

        } else {
            false
        }
    }



    #[trace(tc.trace_mgr, InferLambda(self, infer_only))]
    pub fn infer_lambda(&self, infer_only : bool, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        let mut term_cursor = self;
        let mut domains = Vec::with_capacity(50);
        let mut locals  = Vec::with_capacity(50);

        while let Lambda { binder, body, .. } = term_cursor.as_ref() {
            domains.push(binder.clone());

            let new_dom_ty = binder.type_.instantiate_trace(tc.trace_mgr.clone(), locals.iter().rev());
            let new_dom = binder.clone().swap_ty(new_dom_ty.clone());

            if !infer_only {
                new_dom_ty.infer_sort(tc);
            }

            locals.push(new_dom.as_local());
            term_cursor = body;
        }

        let mut abstrd = term_cursor.instantiate_trace(tc.trace_mgr.clone(), locals.iter().rev())
                                    .infer_type_core(tc, infer_only)
                                    .abstract_trace(tc.trace_mgr.clone(), locals.iter().rev());
        while let Some(d) = domains.pop() {
            abstrd = mk_pi(d, abstrd);
        }
        abstrd
                    

    }

    #[trace(tc.trace_mgr, InferPi(self.clone()))]
    pub fn infer_pi(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        let mut term_cursor = self;
        let mut locals = Vec::new();
        let mut universes = Vec::new();

        while let Pi { binder, body, .. } = term_cursor.as_ref() {
            let new_dom_ty = binder.type_.instantiate_trace(tc.trace_mgr.clone(), locals.iter().rev());
            let new_dom = binder.clone().swap_ty(new_dom_ty.clone());
            let dom_univ = new_dom_ty.infer_sort(tc);


            universes.push(dom_univ);
            let new_local = new_dom.as_local();
            locals.push(new_local);
            term_cursor = body;
        }

        let mut inferred = term_cursor.instantiate_trace(tc.trace_mgr.clone(), locals.iter().rev())
                                  .infer_sort(tc);
        while let Some(u) = universes.pop() {
            inferred = mk_imax(u, inferred);
        }

        mk_sort(inferred)
    }


    #[trace(tc.trace_mgr, InferApps(self, infer_only))]
    pub fn infer_apps(&self, infer_only : bool, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        let (fn_, mut apps) = self.unfold_apps();

        let mut acc = fn_.infer_type_core(tc, infer_only);

        let mut context = Vec::<&Expr>::with_capacity(apps.len());

        while let Some(elem) = apps.pop() {
            if let Pi { binder, body, .. } = acc.as_ref() {
                if !infer_only {
                    let new_dom_ty = binder.type_.instantiate_trace(tc.trace_mgr.clone(), context.iter().copied().rev());
                    elem.check_type__(&new_dom_ty, tc);
                }
                context.push(elem);
                acc = body.clone();
            } else {
                let whnfd = acc.instantiate_trace(tc.trace_mgr.clone(), context.iter().copied().rev())
                               .whnf(tc);
                match whnfd.as_ref() {
                    Pi {..} => {
                        apps.push(elem);
                        context = Vec::new();
                        acc = whnfd;
                    },
                    owise => err_infer_apps(line!(), owise)
                }
            }
        }

        acc.instantiate_trace(tc.trace_mgr.clone(), context.iter().copied().rev())
    }


    // Not sure whether to do the delta steps here.
    #[trace(tc.trace_mgr, LazyDeltaReduction(self, other))]
    pub fn lazy_delta_reduction(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> Either<SSOption, (Expr, Expr)> {
        let mut t_cursor = self.clone();
        let mut s_cursor = other.clone();

        loop {
            match t_cursor.lazy_delta_reduction_step(&s_cursor, tc) {
                Continue(t_, s_) => {
                    t_cursor = t_;
                    s_cursor = s_;
                },
                Short(EqShort) => return Left(Some(EqShort)),
                Short(NeqShort) => return Left(Some(NeqShort)),
                Unknown => return Right((t_cursor, s_cursor))
            }
        }
    }


    #[trace(tc.trace_mgr, LazyDeltaReductionStep(self, other))]
    pub fn lazy_delta_reduction_step(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> DeltaResult {
        let delta_t = self.is_delta(tc);
        let delta_s = other.is_delta(tc);

        let (reduced_t, reduced_s) = match (delta_t, delta_s) {
            (None, None) => return Unknown,
            (Some(dt_info), _) if &dt_info.get_constant_base().name == (&*ID_DELTA) => {
                let whnfd = self.unfold_def_infallible(tc).whnf_core(tc, None);
                if &whnfd == other {
                    return Short(EqShort)
                } else if let Some(u) = whnfd.unfold_def(tc) {
                    return Continue(u.whnf_core(tc, None), other.clone())
                } else {
                    return Continue(whnfd, other.clone())
                }
            },
            (_, Some(ds_info)) if &ds_info.get_constant_base().name == (&*ID_DELTA) => {
                let whnfd = other.unfold_def_infallible(tc).whnf_core(tc, None);
                if self == &whnfd {
                    return Short(EqShort)
                } else if let Some(u) = whnfd.unfold_def(tc) {
                    return Continue(self.clone(), u.whnf_core(tc, None))
                } else {
                    return Continue(self.clone(), whnfd)
                }
            },
            (Some(_), None) => {
                (self.unfold_def_infallible(tc).whnf_core(tc, None), other.clone())
            },
            (None, Some(_)) => {
                (self.clone(), other.unfold_def_infallible(tc).whnf_core(tc, None))
            }
            (Some(dt_info), Some(ds_info)) => {
                match dt_info.get_hint().compare(ds_info.get_hint()) {
                    Greater => (self.unfold_def_infallible(tc).whnf_core(tc, None), other.clone()),
                    Less    => (self.clone(), other.unfold_def_infallible(tc).whnf_core(tc, None)),
                    Equal => {
                        if ((self.as_ref().is_app()) && (other.as_ref().is_app()) && (dt_info == ds_info)) {
                            // FIXME ideally would return errors instead of using
                            // partial get_const_levels
                            // "If these two expressions have the same arguments, and their 
                            // base constants have the same universe levels, 
                            // they are equal"
                            if ((self.eq_args(other, tc)) && (is_def_eq_lvls(self.unfold_apps_fn().get_const_levels_inf(), other.unfold_apps_fn().get_const_levels_inf(), &tc.trace_mgr))) {
                                return Short(EqShort)
                            } else {

                                tc.failure_cache.insert(self.clone(), other.clone())
                            }
                        }

                        (self.unfold_def_infallible(tc).whnf_core(tc, None),
                         other.unfold_def_infallible(tc).whnf_core(tc, None))
                    }
                }
            }

        };

        match reduced_t.quick_def_eq(&reduced_s, tc) {
            Some(EqShort) => Short(EqShort),
            Some(NeqShort) => Short(NeqShort),
            None => Continue(reduced_t, reduced_s)
        }
    }


    #[trace(tc.trace_mgr, Whnf(self))]
    pub fn whnf(&self, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        tc.whnf_cache.get(self).cloned().unwrap_or_else(|| {
            let mut cursor = self.clone();
            loop {
                let whnfd = cursor.whnf_core(tc, None);
                if let Some(next_term) = whnfd.unfold_def(tc) {
                    cursor = next_term
                } else {
                    tc.whnf_cache.insert(self.clone(), whnfd.clone());
                    return whnfd
                }
            }
        })
    }

    #[trace(tc.trace_mgr, WhnfCore(self, _cheap))]
    pub fn whnf_core(&self, tc : &mut TypeChecker<impl Tracer>, _cheap : Option<Cheap>) -> Expr {
        let cheap = _cheap.unwrap_or(CheapFalse);

        let (_fn, args) = self.unfold_apps();
        match _fn.as_ref() {
            Sort { level, .. } => mk_sort(level.simplify_tracing(&tc.trace_mgr)),
            Lambda { .. } if !args.is_empty() => {
                _fn.whnf_lambda(args, tc)
                   .whnf_core(tc, Some(cheap))
            },
            Let { val, body, .. } => {
                let applied = body.instantiate_trace(tc.trace_mgr.clone(), Some(val).into_iter())
                                  .foldl_apps(args.into_iter().rev());
                applied.whnf_core(tc, Some(cheap))
            },
            _ => self.reduce_quot_rec(tc)
                  .or(self.reduce_inductive_rec(cheap, tc))
                  .map(|reduced| reduced.whnf_core(tc, Some(cheap)))
                  .unwrap_or_else(|| self.clone())
        }
    }



    // Two examples:
    ///                  A_0
    ///                 /   \...
    ///               A_1
    ///              /   \...
    ///            λ_w          => [(λ_w, A_1),
    ///          /    \              (λ_x, A_0)]
    ///       ..      λ_x
    ///             /    \
    ///                  λ_y
    ///                    \
    ///                    λ_z
    ///                      \
    ///                       E
    ///
    ///        Or
    ///
    ///              A_0
    ///              /
    ///            A_1
    ///           /
    ///         A_2
    ///         /
    ///       A_3          => [(λ_x, A_4),
    ///      /                 (λ_y, A_3)]
    ///     A_4
    ///     /
    ///    λ_x
    ///      \
    ///       λ_y
    ///         \ 
    ///          E
    #[trace(tc.trace_mgr, WhnfLambda(self, &args))]
    pub fn whnf_lambda(&self, args : Vec<&Expr>, tc : &mut TypeChecker<impl Tracer>) -> Expr {
        let mut lambda_cursor = self;
        let mut num_lambdas = 0usize;

        while let Lambda { body, .. } = lambda_cursor.as_ref() {
            if ((num_lambdas) < args.len()) {
                num_lambdas += 1;
                lambda_cursor = body;
            } else {
                break
            }
        }

        // IE from args = [A1, A2, A3, A4, A5, A6, A7]
        // and 2 lambda applications, creates
        // ([A1, A2, A3, A4, A5], [A6, A7])
        let (fold, inst) = args.split_at(args.len() - num_lambdas);
        lambda_cursor.instantiate_trace(tc.trace_mgr.clone(), inst.into_iter().copied())
                     .foldl_apps(fold.into_iter().rev().copied())
    }

    #[trace(tc.trace_mgr, ReduceQuotRec(self))]
    pub fn reduce_quot_rec(&self, tc : &mut TypeChecker<impl Tracer>) -> Option<Expr> {
        ret_none_if! { !tc.quot_is_init };

        let (fun, args) = self.unfold_apps_rev();

        let (mk_pos, arg_pos) = match fun.get_const_name()? {
            n if n == &*QLIFT => (5, 3),
            n if n == &*QIND => (4, 3),
            _ => return None
        };

        ret_none_if! { args.len() <= mk_pos };

        let mk = args.get(mk_pos)?
                     .whnf(tc);

        ret_none_if! { !(mk.unfold_apps_fn().get_const_name()? == &*QMK) };

        let r = match mk.as_ref() {
            App { arg, .. } => args.get(arg_pos)?.mk_app(arg),
            owise => crate::errors::quot_rec_bad_app(line!(), owise)
        };

        let elim_arity = mk_pos + 1;

        if (args.len() > elim_arity) {
            Some(r.foldl_apps(args.iter()
                                  .skip(elim_arity)
                                  .take(args.len() - elim_arity)
                                  .copied()))
        } else {
            Some(r)
        }
    }


    #[trace(tc.trace_mgr, ReduceInductiveRec(self, cheap))]
    pub fn reduce_inductive_rec<T>(&self, cheap : Cheap, tc : &mut TypeChecker<T>) -> Option<Expr> 
    where T : Tracer {
        let (fun, args) = self.unfold_apps_rev();
        let (name, levels) = fun.try_const_fields()?;

        let whnf_closure = |e : &Expr, tc : &mut TypeChecker<T> | {
            match cheap {
                CheapTrue => e.whnf_core(tc, Some(cheap)),
                _ => e.whnf(tc)
            }
        };

        let recursor_val = tc.env.read().get_recursor_val(name, tc.trace_mgr.clone())?;
        let major_idx = recursor_val.get_major_idx(tc.trace_mgr.clone());

        ret_none_if! { major_idx >= args.len() };

        let mut major = (*&args[major_idx]).clone();
        if recursor_val.is_k {
            if let Some(k_cnstr) = major.to_cnstr_when_K(&recursor_val, tc) {
                major = k_cnstr;
            }
        }

        major = whnf_closure(&major, tc);

        let rule = recursor_val.get_rec_rule_for(&major, tc.trace_mgr.clone())?;

        let (_, major_args) = major.unfold_apps_rev();
        ret_none_if! { rule.nfields > major_args.len() };
        ret_none_if! { (levels.len() != (recursor_val.get_constant_base().lparams.len())) };


        let rhs_zip = recursor_val.get_constant_base().lparams.iter().zip(levels.iter());
        let rhs = rule.rhs.instantiate_lparams_trace(&tc.trace_mgr, rhs_zip);
        let rhs = rhs.foldl_apps(args.iter().take(recursor_val.nparams 
                                                + recursor_val.nmotives 
                                                + recursor_val.nminors).copied());
        let nparams = major_args.len() - rule.get_nfields();

        let rhs = rhs.foldl_apps(major_args.iter().skip(nparams).take(rule.get_nfields()).copied());

        if (args.len() > major_idx + 1) {
            let nextra = args.len() - major_idx - 1;
            let rhs = rhs.foldl_apps(args.iter().skip(major_idx + 1).take(nextra).copied());
            Some(rhs)
        } else {
            Some(rhs)
        }

    }


    #[trace(tc.trace_mgr, MkNullaryCnstr(self))]
    pub fn mk_nullary_cnstr(&self, num_params : usize, tc : &mut TypeChecker<impl Tracer>) -> Option<Expr> {
        let (fun, args) = self.unfold_apps_rev();
        if let Const { name, levels, .. } = fun.as_ref() {
            let constructor_name = tc.env.read().get_first_constructor_name(name)?;
            Some(mk_const(constructor_name, levels.clone()).foldl_apps(args.iter().take(num_params).copied()))
        } else {
            None
        }

    }


    #[trace(tc.trace_mgr, ToCnstrWhenK(self, ConstantInfo::RecursorInfo(rval.clone())))]
    pub fn to_cnstr_when_K(&self, rval : &RecursorVal, tc : &mut TypeChecker<impl Tracer>) -> Option<Expr> {
        let app_type = self.infer_type(tc)
                           .whnf(tc);
        if (app_type.unfold_apps_fn().get_const_name()? != rval.get_induct()) {
            None
        } else {
            let new_cnstr_app = app_type.mk_nullary_cnstr(rval.nparams, tc)?;
            let new_type = new_cnstr_app.infer_type(tc);
            if (app_type.check_def_eq(&new_type, tc) == NeqShort) {
                None
            } else {
                Some(new_cnstr_app)
            }
        }
    }

    #[trace(tc.trace_mgr, TryEtaExpansion(self, other))]
    pub fn try_eta_expansion(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> bool {
        self.try_eta_expansion_core(other, tc)
        || other.try_eta_expansion_core(self, tc)
    }

    #[trace(tc.trace_mgr, TryEtaExpansionCore(self, other))]
    pub fn try_eta_expansion_core(&self, other : &Expr, tc : &mut TypeChecker<impl Tracer>) -> bool {
        if ((self.as_ref().is_lambda()) && (!other.as_ref().is_lambda())) {
            let other_type = other.infer_type(tc) 
                                  .whnf(tc);
            if let Pi { binder, .. } = other_type.as_ref() {
                let other_1 = mk_app(other.clone(), mk_var(0));
                let binding = Binder::mk(binder.pp_name.clone(), binder.type_.clone(), binder.style);
                let new_other = mk_lambda(binding, other_1);
                if (self.check_def_eq(&new_other, tc) == NeqShort) {
                    false
                } else {
                    true
                }
            } else {
                false
            }
        } else {
            if !self.as_ref().is_lambda() {
                false
            } else {
                assert!(other.as_ref().is_lambda());
                false
            }
        }
    }


}

