use crate::level::Level;
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::* };
use crate::tc::infer::InferFlag::*;
use crate::utils::{ Ptr, Tc, List::* };
                    
use ShortCircuit::*;
use DeltaResult::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShortCircuit {
    EqShort,
    NeqShort
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeltaResult<'a> {
    Short(ShortCircuit),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}

pub fn args_eq<'t, 'l : 't, 'e : 'l>(
    lhs : ExprsPtr<'l>, 
    rhs : ExprsPtr<'l>, 
    tc : &mut Tc<'t, 'l, 'e>
) -> bool {
    if lhs.len(tc) == rhs.len(tc) {
        args_eq_aux(lhs, rhs, tc)
    } else {
        false
    }
}

pub fn args_eq_aux<'t, 'l : 't, 'e : 'l>(
    lhs : ExprsPtr<'l>, 
    rhs : ExprsPtr<'l>, 
    tc : &mut Tc<'t, 'l, 'e>
) -> bool {
    match (lhs.read(tc), rhs.read(tc)) {
        (Cons(x, xs), Cons(y, ys)) if x.def_eq(y, tc) == EqShort => args_eq_aux(xs, ys, tc),
        (Nil, Nil) => true,
        _ => false
    }
}


impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
    fn is_sort_zero(self, tc : &mut Tc<'t, 'l, 'e>) -> bool {
        match self.whnf(tc).read(tc) {
            Sort { level } => level.read(tc) == Level::Zero,
            _ => false
        }
    }

    fn is_proposition(self, tc : &mut Tc<'t, 'l, 'e>) -> (bool, ExprPtr<'l>) {
        let infd = self.infer(InferOnly, tc);
        (infd.is_sort_zero(tc), infd)
    }

    fn is_proof(self, tc : &mut Tc<'t, 'l, 'e>) -> (bool, ExprPtr<'l>) {
        let infd = self.infer(InferOnly, tc);
        (infd.is_proposition(tc).0, infd)
    }

    fn proof_irrel_eq(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> bool {
        match self.is_proof(tc) {
            (false, _) => false,
            (true, l_type) => match other.is_proof(tc) {
                (false, _) => false,
                (true, r_type) => l_type.def_eq(r_type, tc) == EqShort
            }
        }
    }
    
    fn def_eq_app(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        match (self.read(tc), other.read(tc)) {
            (App {..}, App {..}) => {
                let (f1, args1) = self.unfold_apps(tc);
                let (f2, args2) = other.unfold_apps(tc);
                match f1.def_eq(f2, tc) {
                    NeqShort => Some(NeqShort),
                    EqShort => match args_eq(args1, args2, tc) {
                        true => Some(EqShort),
                        false => Some(NeqShort)
                    }
                }
            },
            _ => None
        }
    }

    fn def_eq_local(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        match (self.read(tc), other.read(tc)) {
            (Local { serial:s1, .. }, Local { serial:s2, .. }) if s1 == s2 => Some(EqShort),
            _ => None
        }
    }

    fn def_eq_const(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        match (self.read(tc), other.read(tc)) {
            (Const { name:n1, levels:ls1 }, Const { name:n2, levels:ls2 }) => {
                if n1 == n2 && (ls1.eq_antisymm_many(ls2, tc)) {
                    Some(EqShort)
                } else {
                    Some(NeqShort)
                }
            },
            _ => None
        }
    }

    fn def_eq_sort(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        match (self.read(tc), other.read(tc)) {
            (Sort { level:l }, Sort { level:r }) if l.eq_antisymm(r, tc) => Some(EqShort),
            _ => None
        }
    }

    fn def_eq_pi(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        if let (Pi {..}, Pi {..}) = (self.read(tc), other.read(tc)) {
            self.def_eq_pi_aux(other, tc)
        } else {
            None
        }
    } 

    fn def_eq_pi_aux(mut self, mut other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        let mut local_doms = Nil::<Expr>.alloc(tc);
        
        while let (Pi { b_name:n1, b_type:t1, b_style:s1, body:b1, .. },
             Pi { b_type:t2, body:b2, .. }) = (self.read(tc), other.read(tc)) {
                let t1 = t1.inst(local_doms, tc);
                let t2 = t2.inst(local_doms, tc);
                if t1.def_eq(t2, tc) == NeqShort {
                    return Some(NeqShort)
                }
                let local = tc.get_local(n1, t1, s1);

                self = b1;
                other = b2;
                local_doms = Cons(local, local_doms).alloc(tc);
        }

        let out = self.inst(local_doms, tc).def_eq(other.inst(local_doms, tc), tc);
        while let Cons(l, ls) = local_doms.read(tc) {
            local_doms = ls;
            tc.replace_local(l);
        }
        Some(out)
    }

    fn def_eq_lambda(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        if let (Lambda {..}, Lambda {..}) = (self.read(tc), other.read(tc)) {
            self.def_eq_lambda_aux(other, tc)
        } else {
            None
        }
    } 
    
    fn def_eq_lambda_aux(mut self, mut other : Self, tc : &mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        let mut local_doms = Nil::<Expr>.alloc(tc);
        
        while let (Lambda { b_name:n1, b_type:t1, b_style:s1, body:b1, .. },
             Lambda { b_type:t2, body:b2, .. }) = (self.read(tc), other.read(tc)) {
                let t1 = t1.inst(local_doms, tc);
                let t2 = t2.inst(local_doms, tc);
                if t1.def_eq(t2, tc) == NeqShort {
                    return Some(NeqShort)
                }
                let local = tc.get_local(n1, t1, s1);

                self = b1;
                other = b2;
                local_doms = Cons(local, local_doms).alloc(tc);
        }

        let out = self.inst(local_doms, tc).def_eq(other.inst(local_doms, tc), tc);
        while let Cons(l, ls) = local_doms.read(tc) {
            local_doms = ls;
            tc.replace_local(l);
        }
        Some(out)
    }    


    
    fn try_eta_expansion(self, other : Self, tc :&mut Tc<'t, 'l, 'e>) -> Option<ShortCircuit> {
        match self.read(tc) {
            Lambda {..} => match other.read(tc) {
                Lambda {..} => None,
                _ => match other.infer(InferOnly, tc).whnf(tc).read(tc) {
                    Pi { b_name, b_style, b_type, .. } => {
                        let new_body = other.new_app(<Ptr<Expr>>::new_var(0, tc), tc);
                        let new_lambda = <ExprPtr>::new_lambda(b_name, b_type, b_style, new_body, tc);
                        Some(self.def_eq(new_lambda, tc))
                    },
                    _ => None
                }
            },
            _ => None,
        }
    }


    fn rec_check(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> DeltaResult<'l> {
        if let Some(ss) = self.def_eq_sort(other, tc) {
            Short(ss)
        } else if let Some(ss) = self.def_eq_pi(other, tc) {
            Short(ss)
        } else if let Some(ss) = self.def_eq_lambda(other, tc) {
            Short(ss)
        } else {
            self.delta_step(other, tc)
        }
    }    

    fn delta_step(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> DeltaResult<'l> {
        let r1 = self.is_delta(tc);
        let r2 = other.is_delta(tc);
        match (r1, r2) {
            (None, None) => Exhausted(self, other),
            (Some(..), None) => {
                let lhs = self.unfold_def(tc).unwrap().whnf_core(tc);
                let rhs = other;
                lhs.rec_check(rhs, tc)
            }
            (None, Some(..)) => {
                let lhs = self;
                let rhs = other.unfold_def(tc).unwrap().whnf_core(tc);
                lhs.rec_check(rhs, tc)

            }
            (Some(l_def), Some(r_def)) if l_def.get_hint() < r_def.get_hint() => {
                let lhs = self;
                let rhs = other.unfold_def(tc).unwrap().whnf_core(tc);
                lhs.rec_check(rhs, tc)

            }
            (Some(l_def), Some(r_def)) if l_def.get_hint() > r_def.get_hint() => {
                let lhs = self.unfold_def(tc).unwrap().whnf_core(tc);
                let rhs = other;
                lhs.rec_check(rhs, tc)
            }
            (Some(l_def), Some(r_def))  => {
                assert_eq!(l_def.get_hint(), r_def.get_hint());
                match (self.read(tc), other.read(tc)) {
                    (App {..}, App {..}) if (l_def == r_def) => {
                        let (l_fun, l_args) = self.unfold_apps(tc);
                        let (r_fun, r_args) = other.unfold_apps(tc);
                        match (l_fun.try_const_info(tc), r_fun.try_const_info(tc)) {
                            (Some((_, l_levels)), Some((_, r_levels))) 
                                if args_eq(l_args, r_args, tc) 
                                && l_levels.eq_antisymm_many(r_levels, tc) => {
                                Short(EqShort)
                            },
                            _ => {
                                let lhs = self.unfold_def(tc).unwrap().whnf_core(tc);
                                let rhs = other.unfold_def(tc).unwrap().whnf_core(tc);
                                lhs.rec_check(rhs, tc)
                            }
                        }

                    },
                    _ => {
                                let lhs = self.unfold_def(tc).unwrap().whnf_core(tc);
                                let rhs = other.unfold_def(tc).unwrap().whnf_core(tc);
                                lhs.rec_check(rhs, tc)
                    }
                }
            }
        }
    }    

    pub fn assert_def_eq(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) {
        assert!(self.def_eq(other, tc) == EqShort)
    }

    pub fn def_eq(self, other : Self, tc : &mut Tc<'t, 'l, 'e>) -> ShortCircuit {
        if self == other {
            return EqShort
        } else if let Some(cached) = tc.cache.eq_cache.get(&(self, other)).copied() { 
            return cached
        } else {
            let t_n = self.whnf_core(tc);
            let s_n = other.whnf_core(tc);

            let ss = if let Some(ss) = t_n.def_eq_pi(s_n, tc) {
                ss
            } else if let Some(ss) = t_n.def_eq_lambda(s_n, tc) {
                ss
            } else if let Some(ss) = t_n.def_eq_sort(s_n, tc) {
                ss
            } else if t_n.proof_irrel_eq(s_n, tc) {
                EqShort
            } else {            
                match t_n.delta_step(s_n, tc) {
                    Short(ss) => ss,
                    Exhausted(l, r) => {
                        if let Some(ss) = l.def_eq_const(r, tc) {
                            ss
                        } else if let Some(ss) = l.def_eq_local(r, tc) {
                            ss
                        } else if let Some(ss) = l.def_eq_app(r, tc) {
                            ss
                        } else if let Some(ss) = l.try_eta_expansion(r, tc) {
                            ss
                        } else if let Some(ss) = r.try_eta_expansion(l, tc) {
                            ss
                        } else {
                            NeqShort
                        }
                    }
                }                
            };
            tc.cache.eq_cache.insert((self, other), ss);
            ss
        }
    }
}



