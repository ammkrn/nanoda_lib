use crate::name::NamePtr;
use crate::level::{ LevelPtr, LevelsPtr, Level };
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::*, BinderStyle };
use crate::trace::steps::*;
use crate::utils::{ 
    List::*,
    IsLiveCtx,
    IsTc,
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
    ) -> (LevelPtr<'l>, Step<InferSortOfZst>) {
        let (inferred, h1) = self.infer(flag, tc);
        let (whnfd, h2) = inferred.whnf(tc);
        match whnfd.read(tc) {
            Sort { level } => {
                InferSortOf::Base {
                    e : self,
                    inferred,
                    level,
                    e_prime : whnfd,
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
    ) -> (LevelPtr<'l>, Step<EnsureSortZst>) {
        match self.read(tc) {
            Sort { level } => {
                EnsureSort::Base {
                    level,
                    e : self
                }.step(tc)
            },
            _ => {
                let (whnfd, h1) = self.whnf(tc);
                match whnfd.read(tc) {
                    Sort { level } => {
                        EnsureSort::Reduce {
                            e : self,
                            level,
                            e_prime : whnfd,
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
    ) -> (LevelPtr<'l>, Step<EnsureTypeZst>) {
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
    ) -> (Self, Step<EnsurePiZst>) {
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
    ) -> (ExprPtr<'l>, Step<InferZst>) {
        if let Some(cached) = tc.check_infer_cache(self, flag) {
            cached
        } else {
            let result = match self.read(tc) {
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

            tc.insert_infer_cache(self, flag, result);
            result
        }
    }

    fn infer_sort(
        self,
        l : LevelPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferSortZst>) {
        match flag {
            InferOnly => {
                let inferred = l.new_succ(tc).new_sort(tc);
                InferSort::InferOnly {
                    l,
                    e : self,
                    e_prime : inferred,
                }.step(tc)
            },
            Check => {
                let (b, h1) = l.params_defined(tc.dec_uparams(), tc);
                assert!(b);
                let inferred = l.new_succ(tc).new_sort(tc);
                InferSort::Checked {
                    l,
                    e : self,
                    e_prime : inferred,
                    h1,
                }.step(tc)
            }
        }
    }    

    pub fn infer_const(
        self,
        c_name : NamePtr<'l>,
        c_levels : LevelsPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferConstZst>) {
        let (d_view, h_admitted) = match tc.get_declar_view(c_name) {
            Some(tup) => tup,
            _ => panic!(
                "Cannot infer type of unadmitted Declar item \
                {}", c_name.nanoda_dbg(tc)
            )
        };
        let h1 = (c_name, h_admitted, d_view);

        match flag {
            InferOnly => {
                let (inferred, h2) = d_view.type_.subst(d_view.uparams, c_levels, tc);
                InferConst::InferOnly {
                    c_name,
                    c_levels,
                    d_uparams : d_view.uparams,
                    d_type : d_view.type_,
                    d_val : d_view.val,
                    inferred,
                    flag,
                    e : self,
                    declar_view : d_view,
                    h1,
                    h2,
                }.step(tc)
            },
            Check => {
                let (b, h2) = c_levels.params_defined_many(tc.dec_uparams(), tc);
                assert!(b);
                let (inferred, h3) = d_view.type_.subst(d_view.uparams, c_levels, tc);
                InferConst::Checked {
                    c_name,
                    c_levels,
                    tc_uparams : tc.dec_uparams(),
                    d_uparams : d_view.uparams,
                    d_type : d_view.type_,
                    d_val : d_view.val,
                    inferred,
                    flag,
                    e : self,
                    declar_view : d_view,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
        }
    }



    fn infer_app(
        self,
        args : ExprsPtr<'l>,
        context : ExprsPtr<'l>,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferAppZst>) {
        match (self.read(tc), args.read(tc), flag) {
            (_, Nil, _) => {
                let (inferred, h1) = self.inst(context, tc);
                InferApp::Base {
                    e_type : self,
                    context,
                    flag,
                    inferred,
                    h1,
                    ind_arg2 : args
                }.step(tc)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl), InferOnly) => {
                let context_prime = Cons(hd, context).alloc(tc);
                let (inferred, h1) = body.infer_app(
                    tl,
                    context_prime,
                    flag,
                    tc
                );
                InferApp::StepPiInferOnly {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    hd,
                    args_tl : tl,
                    context,
                    inferred,
                    e : self,
                    args,
                    context_prime,
                    h1,
                }.step(tc)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl), Check) => {
                let (b_type_prime, h1) = b_type.inst(context, tc);
                let (arg_type, h2) = hd.infer(Check, tc);
                let h3 = b_type_prime.assert_def_eq(arg_type, tc);

                let context_prime = Cons(hd, context).alloc(tc);
                let (inferred, h4) = body.infer_app(
                    tl,
                    context_prime,
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
                    e : self,
                    context_prime,
                    args,
                    h1,
                    h2,
                    h3,
                    h4,
                }.step(tc)                
            },
            (_, Cons(..), _) => {
                let (e_prime, h1) = self.inst(context, tc);
                let (as_pi, h2) = e_prime.ensure_pi(tc);
                match as_pi.read(tc) {
                    Pi { b_name, b_type, b_style, body, .. } => {
                        let (inferred, h3) = as_pi.infer_app(
                            args,
                            Nil::<Expr>.alloc(tc),
                            flag,
                            tc
                        );
                        InferApp::StepNotPi {
                            e : self,
                            e_prime,
                            args,
                            context,
                            flag,
                            b_name,
                            b_type,
                            b_style,
                            body,
                            inferred,
                            as_pi,
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
    ) -> (Self, Step<InferPiZst>) {
        match self.read(tc) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let (b_type_prime, h1) = b_type.inst(local_binders, tc);
                let (inferred_level, h2) = b_type_prime.infer_sort_of(flag, tc);
                let local = <ExprPtr>::new_local(b_name, b_type_prime, b_style, tc);
                let localsA = Cons(local, local_binders).alloc(tc);
                let levelsA = Cons(inferred_level, levels).alloc(tc);
                let (inferred, h3) = body.infer_pi(
                    localsA,
                    levelsA,
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
                    inferred,
                    b_type_prime,
                    inferred_level,
                    serial : local.local_serial_infal(tc),
                    e : self,
                    levelsA,
                    local,
                    localsA,
                    h1,
                    h2,
                    h3,
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
    ) -> (Self, Step<InferLambdaZst>) {
        match (self.read(tc), flag) {
            (Lambda { b_name, b_type, b_style, body, .. }, InferOnly) => {
                let (b_type_prime, h1) = b_type.inst(local_binders, tc);
                let local = <ExprPtr>::new_local(b_name, b_type_prime, b_style, tc);
                let b_typesA = Cons(b_type, b_types).alloc(tc);
                let localsA = Cons(local, local_binders).alloc(tc);
                let (inferred, h2) = body.infer_lambda(
                    b_typesA,
                    localsA,
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
                    b_type_prime,
                    inferred,
                    serial : local.local_serial_infal(tc),
                    e : self,
                    local_expr : local,
                    b_typesA,
                    localsA,
                    h1,
                    h2,
                }.step(tc)

            }

            (Lambda { b_name, b_type, b_style, body, .. }, Check) => {
                let (b_type_prime, h1) = b_type.inst(local_binders, tc);
                let (b_type_sort, h2) = b_type_prime.infer_sort_of(flag, tc);
                let local = <ExprPtr>::new_local(b_name, b_type_prime, b_style, tc);
                let b_typesA = Cons(b_type, b_types).alloc(tc);
                let localsA = Cons(local, local_binders).alloc(tc);
                let (inferred, h3) = body.infer_lambda(
                    b_typesA,
                    localsA,
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
                    inferred,
                    b_type_prime,
                    b_type_sort,
                    serial : local.local_serial_infal(tc),
                    e : self,
                    local_expr : local,
                    b_typesA,
                    localsA ,
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
                let (folded, h5) = fold_pis_once(b_types, local_binders, abstrd, tc);

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
    ) -> (Self, Step<InferLetZst>) {
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
                    e : self,
                    h1,
                    h2,
                    inferred,
                }.step(tc)
            },
            Check => {
                let (b_type_sort, h1) = b_type.infer_sort_of(flag, tc);
                let (val_type, h2) = val.infer(flag, tc);
                let h3 = val_type.assert_def_eq(b_type, tc);
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
                    e : self,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5,
                }.step(tc)
            }
        }
    }

    fn infer_local(
        self,
        n : NamePtr<'l>,
        t : ExprPtr<'l>,
        s : BinderStyle,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (Self, Step<InferLocalZst>) {
        InferLocal::Base {
            n ,
            t,
            s,
            e : self,
        }.step(tc)
    }


}


pub fn fold_pis_once<'a>(
    b_types : ExprsPtr<'a>,
    local_binders : ExprsPtr<'a>,
    body : ExprPtr<'a>, 
    ctx : &mut impl IsLiveCtx<'a>
) -> (ExprPtr<'a>, Step<FoldPisOnceZst>) {
    match (b_types.read(ctx), local_binders.read(ctx)) {
        (Nil, Nil) => {
            FoldPisOnce::Base {
                out : body,
                b_types,
                local_binders,
            }.step(ctx)
        },
        (Cons(t, ts), Cons(l, ls)) => {
            match l.read(ctx) {
                Local { b_name, b_style, b_type : unused_t, serial } => {
                    let folded_pi = <ExprPtr>::new_pi(b_name, t, b_style, body, ctx);
                    let (out, h1) = fold_pis_once(ts, ls, folded_pi, ctx);
                    FoldPisOnce::Step {
                        n : b_name,
                        t,
                        s : b_style,
                        body,
                        serial,
                        ts,
                        unused_t,
                        local_binders : ls,
                        out,
                        local_expr : l,
                        local_binders_prime : local_binders,
                        ts_prime : b_types,
                        folded_pi,
                        h1,
                    }.step(ctx)
                },
                _ => unreachable!("unreachable pattern match; fold_pis_once")
            }
        },
        _ => unreachable!("Uneven list lengths in fold_pis_once")
    }
}    
