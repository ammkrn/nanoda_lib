use crate::{ ret_none_if, name, param, arrow, sort, app };
use crate::name::{ NamePtr, NamesPtr, Name, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::*, BinderStyle, BinderStyle::* };
use crate::trace::{ IsTracer };
use crate::trace::steps::*;
use crate::utils::{ 
    Ptr,
    List::*,
    ListPtr,
    Env,
    IsLiveCtx,
    IsTc,
    Tc,
    Pfinder,
    HasNanodaDbg 
};
                    
                    
use InferFlag::*;                    



#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferFlag {
    InferOnly,
    Check
}                


impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
    pub fn infer_sort_of(
        self,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (LevelPtr<'l>, Step<InferSortOf<'l>>) {
        let (infd, h1) = self.infer(flag, tc);
        let (whnfd, h2) = infd.whnf(tc);
        match whnfd.read(tc) {
            Sort { level } => {
                InferSortOf::Base {
                    e : self,
                    e_type : infd,
                    level,
                    h1,
                    h2,
                }.step(tc)
            },
            owise => unreachable!(
                "infer_sort failed to produce a sort! got : {}", owise.nanoda_dbg(tc)
            )
        }
    }

    pub fn ensure_sort(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (LevelPtr<'l>, Step<EnsureSort<'l>>) {
        match self.read(tc) {
            Sort { level } => {
                EnsureSort::Base {
                    level,
                    ind_arg1 : self
                }.step(tc)
            },
            _ => {
                let (whnfd, h1) = self.whnf(tc);
                match whnfd.read(tc) {
                    Sort { level } => {
                        EnsureSort::Reduce {
                            e : self,
                            level,
                            h1
                        }.step(tc)
                    },
                    _ => unreachable!("ensure_sort could not produce a sort.")
                }
            }
        }
    }

    pub fn ensure_type(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (LevelPtr<'l>, Step<EnsureType<'l>>) {
        let (e_type, h1) = self.infer(InferOnly, tc);
        let (sort_level, h2) = e_type.ensure_sort(tc);
        EnsureType::Base {
            e : self,
            e_type,
            sort_level,
            h1,
            h2,
        }.step(tc)
    }

    
    pub fn ensure_pi(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<EnsurePi<'l>>) {
        match self.read(tc) {
            Pi {..} => {
                let (b, h1) = self.is_pi(tc);
                assert!(b);
                EnsurePi::Base { 
                    e : self,
                    h1,
                }.step(tc)
            },
            _ => {
                let (whnfd, h1) = self.whnf(tc);
                match whnfd.read(tc) {
                    Pi {..} => {
                        let (b, h2) = whnfd.is_pi(tc);
                        assert!(b);
                        EnsurePi::Reduce {
                            e : self,
                            reduced : whnfd,
                            h1,
                            h2,
                        }.step(tc)
                    },
                    _ => unreachable!("ensure_pi failed to produce a Pi")
                }
            }
        }
    }

    pub fn infer(
        self,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<Infer<'l>>) {
        if let Some((inferred, h1)) = tc.check_infer_cache(self, flag) {
            Infer::CacheHit {
                e : self,
                flag,
                inferred,
                h1,
            }.step(tc)
        } else {
            let (result, step) = match self.read(tc) {
                Sort { level } => {
                    let (inferred, h1) = self.infer_sort(level, flag, tc);
                    Infer::Sort {
                        e : self,
                        flag,
                        inferred,
                        h1
                    }.step(tc)
                }
                Const { name, levels } => {
                    let (inferred, h1) = self.infer_const(name, levels, flag, tc);
                    Infer::Const {
                        e : self,
                        flag,
                        inferred,
                        h1
                    }.step(tc)
                },
                App {..} => {
                    let ((fun, args), h1) = self.unfold_apps(tc);
                    let (fun_type, h2) = fun.infer(flag, tc);
                    let (inferred, h3) = fun_type.infer_app(
                        args,
                        Nil::<Expr>.alloc(tc),
                        flag,
                        tc
                    );                    
                    Infer::App {
                        fun,
                        args,
                        flag,
                        inferred,
                        h1,
                        h2,
                        h3,
                        ind_arg1 : self,
                    }.step(tc)
                },
                Pi {..} => {
                    
                    let (inferred, h1) = self.infer_pi(
                        Nil::<Expr>.alloc(tc),
                        Nil::<Level>.alloc(tc),
                        flag,
                        tc
                    );
                    Infer::Pi {
                        e : self,
                        flag,
                        inferred,
                        h1
                    }.step(tc)
                },
                Lambda {..} => {
                    let (inferred, h1) = self.infer_lambda(
                        Nil::<Expr>.alloc(tc),
                        Nil::<Expr>.alloc(tc),
                        flag,
                        tc
                    );
                    Infer::Lambda {
                        e : self,
                        flag,
                        inferred,
                        h1
                    }.step(tc)
                },
                Let { b_name, b_type, b_style, val, body, .. } => {
                    let (inferred, h1) = self.infer_let(
                        b_name,
                        b_type,
                        b_style,
                        val,
                        body,
                        flag,
                        tc
                    );
                    Infer::Let {
                        e : self,
                        flag,
                        inferred,
                        h1
                    }.step(tc)
                },
                Local { b_name, b_type, b_style, .. } => {
                    let (inferred, h1) = self.infer_local(
                        b_name,
                        b_type,
                        b_style,
                        tc
                    );
                    Infer::Local {
                        e : self,
                        flag,
                        inferred,
                        h1
                    }.step(tc)
                }
                _ => unimplemented!("Cannot infer the type of a bound variable by itself!")
            };

            tc.insert_infer_cache(self, flag, result, step);
            (result, step)
        }
    }

    pub fn infer_const(
        self,
        c_name : NamePtr<'l>,
        c_levels : LevelsPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferConst<'l>>) {
        let (dec, h1) = match tc.get_declar(c_name) {
            Some((d, h1)) => (d, h1),
            _ => panic!(
                "Cannot infer type of undeclared declaration \
                {}", c_name.nanoda_dbg(tc)
            )
        };

        let (dec_uparams, dec_type) = (dec.uparams(tc), dec.type_(tc));

        match flag {
            InferOnly => {
                let (inferred, h2) = dec_type.subst(dec_uparams, c_levels, tc);
                InferConst::InferOnly {
                    c_name,
                    c_levels,
                    flag,
                    dec,
                    dec_uparams,
                    dec_type,
                    inferred,
                    ind_arg1 : self,
                    h1,
                    h2,
                }.step(tc)
            },
            Check => {
                let (b, h2) = c_levels.params_defined_many(tc.dec_uparams(), tc);
                assert!(b);
                let (inferred, h3) = dec_type.subst(dec_uparams, c_levels, tc);
                InferConst::Checked {
                    c_name,
                    c_levels,
                    flag,
                    dec,
                    dec_uparams,
                    dec_type,
                    inferred,
                    ind_arg1 : self,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
        }
    }

    fn infer_sort(
        self,
        l : LevelPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferSort<'l>>) {
        match flag {
            InferOnly => {
                let inferred = l.new_succ(tc).new_sort(tc);
                InferSort::InferOnly {
                    l,
                    inferred,
                    ind_arg1 : self,
                }.step(tc)
            },
            Check => {
                let (b, h1) = l.params_defined(tc.dec_uparams(), tc);
                assert!(b);
                let inferred = l.new_succ(tc).new_sort(tc);
                InferSort::Checked {
                    l,
                    inferred,
                    h1,
                    ind_arg1 : self,
                }.step(tc)
            }
        }
    }

    // For the base case, the state of `flag` doesn't
    // make a difference.
    fn infer_app(
        self,
        args : ExprsPtr<'l>,
        context : ExprsPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferApp<'l>>) {
        match (self.read(tc), args.read(tc), flag) {
            (_, Nil, _) => {
                let (inferred, h1) = self.inst(context, tc);
                InferApp::Base {
                    f_type : self,
                    context,
                    flag,
                    inferred,
                    h1,
                    ind_arg2 : args
                }.step(tc)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl), InferOnly) => {
                let (inferred, h1) = body.infer_app(
                    tl,
                    Cons(hd, context).alloc(tc),
                    flag,
                    tc
                );
                InferApp::StepPiInferOnly {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    args,
                    context,
                    inferred,
                    h1,
                    ind_arg1 : self,
                }.step(tc)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl), Check) => {
                let (b_type_prime, h1) = b_type.inst(context, tc);
                let (arg_type, h2) = hd.infer(Check, tc);
                let h3 = b_type_prime.def_eq(arg_type, tc).expect("app binder and arg types were not equal!");
                let (inferred, h4) = body.infer_app(
                    tl,
                    Cons(hd, context).alloc(tc),
                    flag,
                    tc
                );
                InferApp::StepPiChecked {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    hd_arg : hd,
                    tl_args : tl,
                    context,
                    b_type_prime,
                    arg_type,
                    inferred,
                    h1,
                    h2,
                    h3,
                    h4,
                    ind_arg1 : self,
                    ind_arg2 : args,
                }.step(tc)                
            },
            (_, Cons(..), _) => {
                let (f_type_prime, h1) = self.inst(context, tc);
                let (as_pi, h2) = f_type_prime.ensure_pi(tc);
                match as_pi.read(tc) {
                    Pi { b_name, b_type, b_style, body, .. } => {
                        let (inferred, h3) = as_pi.infer_app(
                            args,
                            Nil::<Expr>.alloc(tc),
                            flag,
                            tc
                        );
                        InferApp::StepNotPi {
                            f_type : self,
                            args,
                            context,
                            f_type_prime,
                            b_name,
                            b_type,
                            b_style,
                            body,
                            flag,
                            inferred,
                            h1,
                            h2,
                            h3,
                        }.step(tc)
                    },
                    owise => unreachable!(
                        "Infer app could not infer the left hand side as a function type. \
                        found {}", owise.nanoda_dbg(tc)
                    )

                }
            }
        }
    }

    fn infer_pi(
        self,
        local_binders : ExprsPtr<'l>,
        levels : LevelsPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferPi<'l>>) {
        match self.read(tc) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let (b_type_prime, h1) = b_type.inst(local_binders, tc);
                let (inferred_level, h2) = b_type_prime.infer_sort_of(flag, tc);
                let local = <ExprPtr>::new_local(b_name, b_type_prime, b_style, tc);
                let (inferred, h3) = body.infer_pi(
                    Cons(local, local_binders).alloc(tc),
                    Cons(inferred_level, levels).alloc(tc),
                    flag,
                    tc
                );

                InferPi::Step {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    local_binders,
                    levels,
                    flag,
                    b_type_prime,
                    inferred_level,
                    local,
                    inferred,
                    h1,
                    h2,
                    h3,
                    ind_arg1 : self
                }.step(tc)
            },
            _ => {
                let (b, h1) = self.is_pi(tc);
                assert!(!b);
                let (instd, h2) = self.inst(local_binders, tc);
                let (inferred_level, h3) = instd.infer_sort_of(flag, tc);
                let (folded, h4) = levels.fold_imaxs(inferred_level, tc);
                let inferred = folded.new_sort(tc);
                InferPi::Base {
                    e : self,
                    local_binders,
                    levels,
                    flag,
                    instd,
                    inferred_level,
                    folded,
                    h1,
                    h2,
                    h3,
                    h4,
                    ind_arg5 : inferred
                }.step(tc)
            }
        }
    }

    fn infer_lambda(
        self,
        b_types : ExprsPtr<'l>,
        local_binders : ExprsPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferLambda<'l>>) {
        match (self.read(tc), flag) {
            (Lambda { b_name, b_type, b_style, body, .. }, InferOnly) => {
                let (b_type_prime, h1) = b_type.inst(local_binders, tc);
                let local = <ExprPtr>::new_local(b_name, b_type_prime, b_style, tc);
                let (inferred, h2) = body.infer_lambda(
                    Cons(b_type, b_types).alloc(tc),
                    Cons(local, local_binders).alloc(tc),
                    flag,
                    tc
                );

                InferLambda::StepInferOnly {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    b_types,
                    local_binders,
                    flag,
                    b_type_prime,
                    inferred,
                    h1,
                    h2,
                }.step(tc)

            }

            (Lambda { b_name, b_type, b_style, body, .. }, Check) => {
                let (b_type_prime, h1) = b_type.inst(local_binders, tc);
                let (b_type_sort, h2) = b_type_prime.infer_sort_of(flag, tc);
                let local = <ExprPtr>::new_local(b_name, b_type_prime, b_style, tc);
                let (inferred, h3) = body.infer_lambda(
                    Cons(b_type, b_types).alloc(tc),
                    Cons(local, local_binders).alloc(tc),
                    flag,
                    tc
                );

                InferLambda::StepChecked {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    b_types,
                    local_binders,
                    flag,
                    b_type_prime,
                    b_type_sort,
                    inferred,
                    h1,
                    h2,                    
                    h3,
                }.step(tc)


            },
            _ => {
                let (b, h1) = self.is_lambda(tc);
                assert!(!b);
                let (instd, h2) = self.inst(local_binders, tc);
                let (inferred_inner, h3) = instd.infer(flag, tc);
                let (abstrd, h4) = inferred_inner.abstr(local_binders, tc);
                let (folded, h5) = fold_pis_once(local_binders, b_types, abstrd, tc);

                InferLambda::Base {
                    e : self,
                    local_binders,
                    b_types,
                    flag,
                    instd,
                    inferred_inner,
                    abstrd,
                    folded,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5
                }.step(tc)
            }
        }
    }

    fn infer_let(
        self,
        b_name : NamePtr<'l>,
        b_type : ExprPtr<'l>,
        b_style : BinderStyle,
        val : ExprPtr<'l>,
        body : ExprPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferLet<'l>>) {
        match flag {
            InferOnly => {
                let (instd, h1) = body.inst1(val, tc);
                let (inferred, h2) = instd.infer(flag, tc);
                InferLet::InferOnly {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body,
                    flag,
                    b_prime : instd,
                    h1,
                    h2,
                    inferred,
                    ind_arg1 : self,
                }.step(tc)
            },
            Check => {
                let (b_type_sort, h1) = b_type.infer_sort_of(flag, tc);
                let (val_type, h2) = val.infer(flag, tc);
                let h3 = val_type.def_eq(b_type, tc).expect("Infer_let go a value and binder that were not equal!");
                let (instd, h4) = body.inst1(val, tc);
                let (inferred, h5) = instd.infer(flag, tc);
                InferLet::Checked {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body,
                    flag,
                    b_type_sort,
                    val_type,
                    b_prime : instd,
                    inferred,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5,
                    ind_arg1 : self,
                }.step(tc)
            }
        }
    }

    fn infer_local(
        self,
        b_name : NamePtr<'l>,
        b_type : ExprPtr<'l>,
        b_style : BinderStyle,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferLocal<'l>>) {
        InferLocal::Base {
            b_name,
            b_type,
            b_style,
            ind_arg1 : self
        }.step(tc)
    }


}


pub fn fold_pis_once<'a>(
    local_binders : ExprsPtr<'a>,
    b_types : ExprsPtr<'a>,
    body : ExprPtr<'a>, 
    ctx : &mut impl IsLiveCtx<'a>
) -> (ExprPtr<'a>, Step<FoldPisOnce<'a>>) {
    match (local_binders.read(ctx), b_types.read(ctx)) {
        (Nil, Nil) => {
            FoldPisOnce::Base {
                out : body,
                ind_arg1 : local_binders,
                ind_arg2 : b_types,
            }.step(ctx)
        },
        (Cons(l, ls), Cons(t, ts)) => {
            match l.read(ctx) {
                Local { b_name, b_style, b_type : unused_t, .. } => {
                    let combined = <ExprPtr>::new_pi(b_name, t, b_style, body, ctx);
                    let (out, h1) = fold_pis_once(ls, ts, combined, ctx);
                    FoldPisOnce::Step {
                        n : b_name,
                        unused_t,
                        s : b_style,
                        t,
                        ls,
                        ts,
                        body,
                        combined,
                        out,
                        h1,
                        ind_arg1 : local_binders,
                        ind_arg2 : b_types,
                    }.step(ctx)
                },
                _ => unreachable!("unreachable pattern match; fold_pis_once")
            }
        },
        _ => unreachable!("Uneven list lengths in fold_pis_once")
    }
}    
