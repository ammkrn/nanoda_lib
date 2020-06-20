use std::fs::File;
use std::io::{ Error as IoError, Result as IoResult };
use std::io::{ stdout, Stdout };
use std::io::{ BufWriter, Write };
use crate::mk_trace_step;
use crate::utils::{ Ptr, List, List::*, ListPtr, IsCtx,  };
use crate::name::{ NamePtr, NamesPtr, Name, StringPtr, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle };
use crate::tc::eq::{ EqResult, DeltaResult };
use crate::trace::items::{ HasPtrRepr, HasPrefix };
use crate::trace::steps::*;
use crate::env::{ 
    RecRulePtr, 
    RecRulesPtr, 
    RecRule, 
    Declar, 
    Declar::*, 
    DeclarPtr, 
    DeclarsPtr, 
    ReducibilityHint 
};

pub mod items;
pub mod steps;

/*
IsTracer::write should probably write to some kind of BufWriter,
where the user-defined implementation of `write` dictates when
to flush the buffer.
*/
#[derive(Debug)]
pub struct TraceMgr<T : IsTracer> {
    tracer : T,
    next_step_idx : usize,
    errors : Vec<IoError>
}

impl<T : IsTracer> TraceMgr<T> {
    pub fn new(tracer : T) -> Self {
        TraceMgr {
            tracer,
            next_step_idx : 0usize,
            errors : Vec::new(),
        }
    }

    pub fn next_step_idx(&mut self) -> StepIdx {
        let this_step_idx = StepIdx::new(self.next_step_idx);
        self.next_step_idx += 1;
        this_step_idx
    }

    pub fn write_line(&mut self, bytes : &[u8]) {
        self.write(bytes);
        self.write("\n".as_bytes());
    }

    pub fn write(&mut self, bytes : &[u8]) {
        let write_result = self.tracer.write(bytes);
        match (<T as IsTracer>::TERM_ON_IO_ERR, write_result) {
            (true, Err(e)) => {
                panic!("Fatal IO Error : {}\n", e);
            },
            (false, Err(e)) => {
                self.errors.push(e);
            },
            _ => ()
        }
    }
}



#[macro_export]
macro_rules! mk_trace_step {
    ( $fun_name:ident, $short:lifetime, $generic:ident, $step:ty ) => {
        //fn $fun_name<$short, $generic : HasPrefix>(step : $step<$short, $generic>, ctx : &mut impl IsCtx<$short>) -> StepIdx {
        //fn $fun_name<$short, $generic : HasPrefix>(step : $step<$short, $generic>, ctx : &mut impl IsCtx<$short>) -> StepIdx {
        fn $fun_name<$short, $generic : HasPrefix>(step : $step, ctx : &mut impl IsCtx<$short>) -> StepIdx {
            let (step_idx, trace_repr) = step.default_trace_repr(ctx);
            ctx.mut_mgr().write_line(trace_repr.as_bytes());
            step_idx
        }
    };

    ( $fun_name:ident, $short:lifetime, $step:ty ) => {
        fn $fun_name<$short>(step : $step, ctx : &mut impl IsCtx<$short>) -> StepIdx {
            let (step_idx, trace_repr) = step.default_trace_repr(ctx);
            ctx.mut_mgr().write_line(trace_repr.as_bytes());
            step_idx
        }

    };
}


/*
Simialr to the `syn` crate's strategy for allowing use-defined implementations
of visit/fold, the formatting for trace items is done as part of `IsTracer`,
and defaults are provided. You can choose to override any or all of them
by redefining the formatting for your trait implementation. The API you have
access to (without digging deeper into the library) is `Ptr::in_env()` to 
determine whether a given element is in the environment or the local
context, and `IsTracer::ptr_index(ptr)` to get the arena position of a 
pointer as a usize.
You can also use `<item>.nanoda_dbg(ctx)` to get a human-readable 
(though not pretty printed) representation of any of the items used in 
the library (except for meta items like Tc and IndBlock)
*/
pub trait IsTracer {
    const NOOP : bool;
    const TERM_ON_IO_ERR : bool;

    fn write(&mut self, s : &[u8]) -> IoResult<usize>;

    fn trace_string<'a>(s : StringPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = s.ptr_repr();
        sink.push_str(format!(".{}", s.read(ctx)).as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }

    fn trace_name<'a>(n : NamePtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = n.ptr_repr();
        let suffix = match n.read(ctx) {
            Anon => {
                format!("_")
            }
            Str(pfx, sfx) => {
                format!("s.{}.{}", pfx.ptr_repr(), sfx.ptr_repr())
            },
            Num(pfx, sfx) => {
                format!("n.{}.{}", pfx.ptr_repr(), sfx.ptr_repr())
            }
        };

        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }

    fn trace_level<'a>(l : LevelPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = l.ptr_repr();
        let suffix = match l.read(ctx) {
            Zero => format!("z"),
            Succ(pred) => format!("s.{}", pred.ptr_repr()),
            Max(x, y) => format!("m.{}.{}", x.ptr_repr(), y.ptr_repr()),
            Imax(x, y) => format!("i.{}.{}", x.ptr_repr(), y.ptr_repr()),
            Param(n) => format!("p.{}", n.ptr_repr()),
        };

        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }
    
    fn trace_expr<'a>(e : ExprPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = e.ptr_repr();
        let suffix = match e.read(ctx) {
            Var { dbj } => format!("{}", dbj.ptr_repr()),
            Sort { level } => format!("s.{}", level.ptr_repr()),
            Const { name, levels } => format!("c.{}.{}", name.ptr_repr(), levels.ptr_repr()),
            App { fun, arg, .. } => format!("a.{}.{}", fun.ptr_repr(), arg.ptr_repr()),
            Pi { b_type, b_name, b_style, body, .. } => format!("p.{}.{}.{}.{}", b_name.ptr_repr(), b_type.ptr_repr(), b_style.ptr_repr(), body.ptr_repr()),
            Lambda { b_type, b_name, b_style, body, .. } => format!("l.{}.{}.{}.{}", b_name.ptr_repr(), b_type.ptr_repr(), b_style.ptr_repr(), body.ptr_repr()),
            Let { b_type, b_name, b_style, body, .. } => format!("z.{}.{}.{}.{}", b_name.ptr_repr(), b_type.ptr_repr(), b_style.ptr_repr(), body.ptr_repr()),
            Local { b_type, b_name, b_style, serial, .. } => format!("x.{}.{}.{}.{}", b_name.ptr_repr(), b_type.ptr_repr(), b_style.ptr_repr(), serial.ptr_repr()),
        };

        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }

    fn trace_rec_rule<'a>(rr : RecRulePtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = rr.ptr_repr();
        let rr_ = rr.read(ctx);
        let inner = format!(".{}.{}.{}", rr_.ctor_name.ptr_repr(), rr_.num_fields.ptr_repr(), rr_.val.ptr_repr());
        sink.push_str(inner.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }

    fn trace_declar<'a>(d : DeclarPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = d.ptr_repr();
        let d_ = d.read(ctx);
        let name = d_.name().ptr_repr();
        let uparams = d_.uparams().ptr_repr();
        let type_ = d_.type_().ptr_repr();
        let suffix = match d_ {
            Axiom { is_unsafe, .. } => {
                format!("a.{}.{}.{}.{}", name, uparams, type_, is_unsafe)
            },
            Definition { val, hint, is_unsafe, .. } => {
                format!("d.{}.{}.{}.{}.{}.{}", 
                name, 
                uparams, 
                type_, 
                val.ptr_repr(), 
                hint.ptr_repr(), 
                is_unsafe
                )
            },
            Inductive { 
                num_params, 
                all_ind_names, 
                all_ctor_names, 
                is_unsafe,
                .. 
            } => {
                format!(
                "i.{}.{}.{}.{}.{}.{}.{}", 
                name, 
                uparams, 
                type_, 
                num_params, 
                all_ind_names.ptr_repr(),
                all_ctor_names.ptr_repr(),
                is_unsafe,
               )
            }
            Constructor { 
                parent_name, 
                num_fields, 
                minor_idx, 
                num_params, 
                is_unsafe,
                ..
            } => {
                format!(
                    "c.{}.{}.{}.{}.{}.{}.{}.{}",
                    name,
                    uparams,
                    type_,
                    parent_name.ptr_repr(),
                    num_fields,
                    minor_idx,
                    num_params,
                    is_unsafe,
                )
            },
            Recursor { 
                all_names, 
                num_params, 
                num_indices,
                num_motives,
                num_minors,
                major_idx,
                rec_rules,
                is_k,
                is_unsafe,
                ..
            } => {
                format!(
                    "r.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}",
                    name,
                    uparams,
                    type_,
                    all_names.ptr_repr(),
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    major_idx,
                    rec_rules.ptr_repr(),
                    is_k,
                    is_unsafe,
                )

            }
            Quot { .. } => format!("q.{}.{}.{}", name, uparams, type_),
            | Theorem {..}
            | Opaque {..} => unimplemented!()


        };
        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }

    
    // unforunately we can't derive the list versions for a number of reasons
    // that stem from earlier limitations of Rust's type system.
    fn trace_name_list<'a>(ns : NamesPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = ns.ptr_repr();

        let suffix = match ns.read(ctx) {
            Nil => format!("n"),
            Cons(hd, tl) => {
                format!(".{}.{}", hd.ptr_repr(), tl.ptr_repr())
            }
        };
        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }

    fn trace_level_list<'a>(l : LevelsPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = l.ptr_repr();

        let suffix = match l.read(ctx) {
            Nil => format!("n"),
            Cons(hd, tl) => {
                format!(".{}.{}", hd.ptr_repr(), tl.ptr_repr())
            }
        };
        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }    

    fn trace_expr_list<'a>(l : ExprsPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = l.ptr_repr();

        let suffix = match l.read(ctx) {
            Nil => format!("n"),
            Cons(hd, tl) => {
                format!(".{}.{}", hd.ptr_repr(), tl.ptr_repr())
            }
        };
        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }    
     
 
    fn trace_rec_rule_list<'a>(l : RecRulesPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = l.ptr_repr();

        let suffix = match l.read(ctx) {
            Nil => format!("n"),
            Cons(hd, tl) => {
                format!(".{}.{}", hd.ptr_repr(), tl.ptr_repr())
            }
        };
        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }    

    fn trace_declar_list<'a>(l : DeclarsPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let mut sink = l.ptr_repr();

        let suffix = match l.read(ctx) {
            Nil => format!("n"),
            Cons(hd, tl) => {
                format!(".{}.{}", hd.ptr_repr(), tl.ptr_repr())
            }
        };
        sink.push_str(suffix.as_str());
        ctx.mut_mgr().write_line(sink.as_bytes())
    }       

    // Example of a step trace
    //fn trace_pos<'a, A : HasPrefix>(step : Pos<'a, A>, ctx : &mut impl IsCtx<'a>) -> StepIdx {
    //    let (step_idx, trace_repr) = step.default_trace_repr(ctx);
    //    ctx.mut_mgr().write_line(trace_repr.as_bytes());
    //    step_idx
    //}    

    mk_trace_step! { trace_try_succ, 'a, TrySucc }
    mk_trace_step! { trace_mem, 'a, A, Mem<'a, A> }
    mk_trace_step! { trace_pos, 'a, A, Pos<'a, A> }
    mk_trace_step! { trace_is_subset, 'a, A, IsSubset<'a, A> }
    mk_trace_step! { trace_skip, 'a, A, Skip<'a, A> }
    mk_trace_step! { trace_take, 'a, A, Take<'a, A> }
    mk_trace_step! { trace_no_dupes, 'a, A, NoDupes<'a, A> }
    mk_trace_step! { trace_get, 'a, A, Get<'a, A> }
    mk_trace_step! { trace_len, 'a, A, Len<'a, A> }
    mk_trace_step! { trace_concat, 'a, A, Concat<'a, A> }

    mk_trace_step! { trace_get_prefix, 'a, GetPrefix<'a> }

    mk_trace_step! { trace_is_zero_lit, 'a, IsZeroLit<'a> }
    mk_trace_step! { trace_is_succ, 'a, IsSucc<'a> }
    mk_trace_step! { trace_is_any_max, 'a, IsAnyMax<'a> }
    mk_trace_step! { trace_is_param, 'a, IsParam<'a> }
    mk_trace_step! { trace_combining, 'a, Combining<'a> }
    mk_trace_step! { trace_simplify, 'a, Simplify<'a> }
    mk_trace_step! { trace_params_defined, 'a, ParamsDefined<'a> }
    mk_trace_step! { trace_subst_l, 'a, SubstL<'a> }
    mk_trace_step! { trace_leq_core, 'a, LeqCore<'a> }
    mk_trace_step! { trace_leq, 'a, Leq<'a> }
    mk_trace_step! { trace_eq_antisymm, 'a, EqAntisymm<'a> }
    mk_trace_step! { trace_is_zero, 'a, IsZero<'a> }
    mk_trace_step! { trace_is_nonzero, 'a, IsNonzero<'a> }
    mk_trace_step! { trace_maybe_zero, 'a, MaybeZero<'a> }
    mk_trace_step! { trace_maybe_nonzero, 'a, MaybeNonzero<'a> }

    mk_trace_step! { trace_params_defined_many, 'a, ParamsDefinedMany<'a> }
    mk_trace_step! { trace_subst_l_many, 'a, SubstLMany<'a> }
    mk_trace_step! { trace_eq_antisymm_many, 'a, EqAntisymmMany<'a> }
    mk_trace_step! { trace_fold_imaxs, 'a, FoldImaxs<'a> }

    mk_trace_step! { trace_is_lambda, 'a, IsLambda<'a> }
    mk_trace_step! { trace_is_pi, 'a, IsPi<'a> }
    mk_trace_step! { trace_is_app, 'a, IsApp<'a> }
    mk_trace_step! { trace_is_const, 'a, IsConst<'a> }
    mk_trace_step! { trace_inst, 'a, Inst<'a> }
    mk_trace_step! { trace_inst_aux, 'a, InstAux<'a> }
    mk_trace_step! { trace_abstr, 'a, Abstr<'a> }
    mk_trace_step! { trace_abstr_aux, 'a, AbstrAux<'a> }
    mk_trace_step! { trace_subst_e, 'a, SubstE<'a> }
    mk_trace_step! { trace_has_ind_occ, 'a, HasIndOcc<'a> }
    mk_trace_step! { trace_apply_pi, 'a, ApplyPi<'a> }
    mk_trace_step! { trace_apply_lambda, 'a, ApplyLambda<'a> }
    mk_trace_step! { trace_fold_pis, 'a, FoldPis<'a> }
    mk_trace_step! { trace_fold_lambdas, 'a, FoldLambdas<'a> }
    mk_trace_step! { trace_foldl_apps, 'a, FoldlApps<'a> }
    mk_trace_step! { trace_unfold_apps_aux, 'a, UnfoldAppsAux<'a> }
    mk_trace_step! { trace_telescope_size, 'a, TelescopeSize<'a> }

    mk_trace_step! { trace_whnf_lambda, 'a, WhnfLambda<'a> }
    mk_trace_step! { trace_whnf_sort, 'a, WhnfSort<'a> }
    mk_trace_step! { trace_whnf_let, 'a, WhnfLet<'a> }
    mk_trace_step! { trace_reduce_quot_lift, 'a, ReduceQuotLift<'a> }
    mk_trace_step! { trace_reduce_quot_ind, 'a, ReduceQuotInd<'a> }
    mk_trace_step! { trace_reduce_ind_rec, 'a, ReduceIndRec<'a> }
    mk_trace_step! { trace_mk_nullary_ctor, 'a, MkNullaryCtor<'a> }
    mk_trace_step! { trace_to_ctor_when_k, 'a, ToCtorWhenK<'a> }
    mk_trace_step! { trace_get_rec_rule, 'a, GetRecRule<'a> }
    mk_trace_step! { trace_get_rec_rule_aux, 'a, GetRecRuleAux<'a> }
    mk_trace_step! { trace_whnf_core, 'a, WhnfCore<'a> }
    mk_trace_step! { trace_whnf, 'a, Whnf<'a> }
    mk_trace_step! { trace_unfold_def, 'a, UnfoldDef<'a> }
    mk_trace_step! { trace_is_delta, 'a, IsDelta<'a> }

    mk_trace_step! { trace_def_eq, 'a, DefEq<'a> }
    mk_trace_step! { trace_def_eq_sort, 'a, DefEqSort<'a> }
    mk_trace_step! { trace_def_eq_pi, 'a, DefEqPi<'a> }
    mk_trace_step! { trace_def_eq_lambda, 'a, DefEqLambda<'a> }
    mk_trace_step! { trace_is_sort_zero, 'a, IsSortZero<'a> }
    mk_trace_step! { trace_is_proposition, 'a, IsProposition<'a> }
    mk_trace_step! { trace_is_proof, 'a, IsProof<'a> }
    mk_trace_step! { trace_proof_irrel_eq, 'a, ProofIrrelEq<'a> }
    mk_trace_step! { trace_args_eq, 'a, ArgsEq<'a> }
    mk_trace_step! { trace_args_eq_aux, 'a, ArgsEqAux<'a> }
    mk_trace_step! { trace_lazy_delta_step, 'a, LazyDeltaStep<'a> }
    mk_trace_step! { trace_def_eq_const, 'a, DefEqConst<'a> }
    mk_trace_step! { trace_def_eq_local, 'a, DefEqLocal<'a> }
    mk_trace_step! { trace_def_eq_app, 'a, DefEqApp<'a> }
    mk_trace_step! { trace_def_eq_eta, 'a, DefEqEta<'a> }

    mk_trace_step! { trace_ensure_sort, 'a, EnsureSort<'a> }
    mk_trace_step! { trace_ensure_pi, 'a, EnsurePi<'a> }
    mk_trace_step! { trace_ensure_type, 'a, EnsureType<'a> }
    mk_trace_step! { trace_infer, 'a, Infer<'a> }
    mk_trace_step! { trace_infer_const, 'a, InferConst<'a> }
    mk_trace_step! { trace_infer_sort, 'a, InferSort<'a> }
    mk_trace_step! { trace_infer_app, 'a, InferApp<'a> }
    mk_trace_step! { trace_infer_sort_of, 'a, InferSortOf<'a> }
    mk_trace_step! { trace_infer_pi, 'a, InferPi<'a> }
    mk_trace_step! { trace_infer_lambda, 'a, InferLambda<'a> }
    mk_trace_step! { trace_fold_pis_once, 'a, FoldPisOnce<'a> }
    mk_trace_step! { trace_infer_let, 'a, InferLet<'a> }
    mk_trace_step! { trace_infer_local, 'a, InferLocal<'a> }


    mk_trace_step! { trace_admit_declar, 'a, AdmitDeclar<'a> }


    fn ptr_index<'a, A>(ptr : Ptr<'a, A>) -> usize {
        match ptr {
            | Ptr::E(index, ..)
            | Ptr::L(index, ..)
            | Ptr::P(index, ..) => index
        }
    }
}




// String, BinderStyle, and ReducibilityHint have one-off
// implementations since they're either not Copy (String)
//  or are both Copy and non-recursive, so we don't need an arena
// to track them, so we just print them inline.
impl<'a> StringPtr<'a> {

    pub fn repr(self, ctx : &impl IsCtx<'a>) -> String {
        let pfx = self.ptr_repr();
        let sfx = self.read(ctx);
        format!("{}.{}", pfx, sfx)
    }
}



impl IsTracer for () {
    const NOOP : bool = true;
    const TERM_ON_IO_ERR : bool = false;
    fn write(&mut self, _ : &[u8]) -> IoResult<usize> {
        Ok(0)
    }
}

#[derive(Debug)]
pub struct StdoutTracer {
    inner : BufWriter<Stdout>
}

impl StdoutTracer {
    pub fn new() -> Self {
        StdoutTracer {
            inner : BufWriter::new(stdout())
        }
    }
}

impl IsTracer for StdoutTracer {
    const NOOP : bool = false;
    const TERM_ON_IO_ERR : bool = false;
    fn write(&mut self, bytes : &[u8]) -> IoResult<usize> {
        self.inner.write(bytes)
    }
}

#[derive(Debug)]
pub struct FileTracer {
    inner : BufWriter<File>,
}

impl FileTracer {
    pub fn new(file : File) -> Self {
        FileTracer {
            inner : BufWriter::new(file)
        }
    }
}

impl IsTracer for FileTracer {
    const NOOP : bool = false;
    const TERM_ON_IO_ERR : bool = false;
    fn write(&mut self, bytes : &[u8]) -> IoResult<usize> {
        self.inner.write(bytes)
    }
}

