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
use crate::trace::items::HasPrefix;
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
    pub tracer : T,
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

    pub fn finish_write(&mut self, io_result : IoResult<()>) {
        match (<T as IsTracer>::TERM_ON_IO_ERR, io_result) {
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
        fn $fun_name<$short, $generic : HasPrefix>(step : $step, ctx : &mut impl IsCtx<$short>) -> StepIdx {
            let (step_idx, result) = step.default_trace_repr(ctx);
            ctx.mut_mgr().finish_write(result);
            step_idx
        }
    };

    ( $fun_name:ident, $short:lifetime, $step:ty ) => {
        fn $fun_name<$short>(step : $step, ctx : &mut impl IsCtx<$short>) -> StepIdx {
            let (step_idx, result) = step.default_trace_repr(ctx);
            ctx.mut_mgr().finish_write(result);
            step_idx
        }

    };
}


/*
`IsTrace` is implemented as a supertrait of std::io::Write. See `NoopTracer` for an example
of how to implement `IsTracer` for something that's not actually supposed to have any
writing behavior.
if `NOOP` is true, the typechecker runs basically as if there was no tracing
happening.
if `TERM_ON_IO_ERR` is `true`, any attempt to write to the trace file that throws
an error will cause the program to panic. If it's `false`, the error will be 
pushed to a Vec<std::io::Result<()>> that you can read from later.
You probably want this to be `true` since typechecking takes a non-trivial amount
of time, and it's highly likely that any write error is going to result in
an output file that won't be accepted by a verifier.

The scheme for allowing user-defined implementations of trace representations/formats
is similar to that of the `syn` crate's for allowing user-defined traversals of syntax trees;
the `IsTracer` trait has a unique for every item and step that says how its supposed to be formatted
in the output, and we provide a default which corresponds to the provided grammar. When users
implement `IsTracer`, they can choose to override one or all of these behaviors with their own
formatting. The API currently exposed for use in writing implementations is 
`Ptr::in_env()` which returns a bool indicating whether a given element is in the environment
or local to a typechecking context, `IsTracer::ptr_index(ptr)` which returns the element's unique
index as a usize, and `<item>`.nanoda_dbg(ctx)` which will return a human-readable but not pretty-printed
string representation of any of the items of interest.
You can access the buffer of IO errors if you choose not to terminate on error
via `ctx.mut_mgr().errors`
*/
pub trait IsTracer : std::io::Write {
    const NOOP : bool;
    const TERM_ON_IO_ERR : bool;

    // Having to clone here is temporary until I figure out a better
    // solution. The problem is that `ctx` owns both the tracer
    // and the arena holding all the strings, and since we're using
    // functions as getters for both the arena and the tracer,
    // the compiler can't tell that the borrows don't interfere when
    // we call `write!`
    fn trace_string<'a>(s : StringPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let s_contents = s.read(ctx).clone();
        let result = write!(ctx.tracer(), "{}.{}\n", s, s_contents);
        ctx.mut_mgr().finish_write(result);
    }

    fn trace_name<'a>(n : NamePtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match n.read(ctx) {
            Anon => write!(ctx.tracer(), "{}a\n", n),
            Str(pfx, sfx) => write!(ctx.tracer(), "{}s.{}.{}\n", n, pfx, sfx),
            Num(pfx, sfx) => write!(ctx.tracer(), "{}n.{}.{}\n", n, pfx, sfx),
        };
        ctx.mut_mgr().finish_write(result);
    }

    fn trace_level<'a>(l : LevelPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match l.read(ctx) {
            Zero => write!(ctx.tracer(), "{}z\n", l),
            Succ(pred) => write!(ctx.tracer(), "{}s.{}\n", l, pred),
            Max(x, y) => write!(ctx.tracer(), "{}m.{}.{}\n", l, x, y),
            Imax(x, y) => write!(ctx.tracer(), "{}i.{}.{}\n", l, x, y),
            Param(n) => write!(ctx.tracer(), "{}p.{}\n", l, n)
        };
        ctx.mut_mgr().finish_write(result);
    }
    
    fn trace_expr<'a>(e : ExprPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match e.read(ctx) {
            Var { dbj } => write!(ctx.tracer(), "{}v{}\n", e, dbj),
            Sort { level } => write!(ctx.tracer(), "{}s.{}\n", e, level),
            Const { name, levels } => write!(ctx.tracer(), "{}c.{}.{}\n", e, name, levels),
            App { fun, arg, .. } => write!(ctx.tracer(), "{}a.{}.{}\n", e, fun, arg),
            Pi { b_type, b_name, b_style, body, .. } => write!(ctx.tracer(), "{}p.{}.{}.{}.{}\n", e, b_name, b_type, b_style, body),
            Lambda { b_type, b_name, b_style, body, .. } => write!(ctx.tracer(), "{}l.{}.{}.{}.{}\n", e, b_name, b_type, b_style, body),
            Let { b_type, b_name, b_style, body, .. } => write!(ctx.tracer(), "{}z.{}.{}.{}.{}\n", e, b_name, b_type, b_style, body),
            Local { b_type, b_name, b_style, serial, .. } => write!(ctx.tracer(), "{}x.{}.{}.{}.{}\n", e, b_name, b_type, b_style, serial),
        };

        ctx.mut_mgr().finish_write(result);
    }

    fn trace_rec_rule<'a>(rr : RecRulePtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match rr.read(ctx) {
            RecRule { ctor_name, num_fields, val } => {
                write!(ctx.tracer(), "{}.{}.{}.{}\n", rr, ctor_name, num_fields, val)

            }
        };
        ctx.mut_mgr().finish_write(result);
    }

    fn trace_declar<'a>(dptr : DeclarPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let d = dptr.read(ctx);
        let result = match d {
            Axiom { is_unsafe, .. } => {
                write!(
                    ctx.tracer(), 
                    "{}a.{}.{}.{}.{}\n", 
                    dptr, 
                    d.name(), 
                    d.uparams(), 
                    d.type_(), 
                    is_unsafe
                )
            },
            Definition { val, hint, is_unsafe, .. } => {
                write!(
                ctx.tracer(), 
                    "{}d.{}.{}.{}.{}.{}.{}\n", 
                    dptr,
                    d.name(), 
                    d.uparams(), 
                    d.type_(), 
                    val,
                    hint,
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
                write!(
                ctx.tracer(),
                "{}i.{}.{}.{}.{}.{}.{}.{}\n", 
                dptr,
                d.name(), 
                d.uparams(), 
                d.type_(), 
                num_params, 
                all_ind_names,
                all_ctor_names,
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
                write!(
                    ctx.tracer(),
                    "{}c.{}.{}.{}.{}.{}.{}.{}.{}\n",
                    dptr,
                    d.name(),
                    d.uparams(),
                    d.type_(),
                    parent_name,
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
                write!(
                    ctx.tracer(),
                    "{}r.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}.{}\n",
                    dptr,
                    d.name(),
                    d.uparams(),
                    d.type_(),
                    all_names,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    major_idx,
                    rec_rules,
                    is_k,
                    is_unsafe,
                )

            }
            Quot { .. } => {
                write!(
                    ctx.tracer(), 
                    "{}q.{}.{}.{}\n", 
                    dptr, 
                    d.name(), 
                    d.uparams(), 
                    d.type_()
                )
            }
            | Theorem {..}
            | Opaque {..} => unimplemented!()


        };

        ctx.mut_mgr().finish_write(result);
    }

    
    // Implemented as separate functions so that users
    // can elect to implement separate trace formats.
    fn trace_name_list<'a>(l : NamesPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match l.read(ctx) {
            Nil => write!(ctx.tracer(), "{}_\n", l),
            Cons(hd, tl) => write!(ctx.tracer(), "{}.{}.{}\n", l, hd, tl),
        };
        ctx.mut_mgr().finish_write(result);
    }

    fn trace_level_list<'a>(l : LevelsPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match l.read(ctx) {
            Nil => write!(ctx.tracer(), "{}_\n", l),
            Cons(hd, tl) => write!(ctx.tracer(), "{}.{}.{}\n", l, hd, tl),
        };
        ctx.mut_mgr().finish_write(result);
    }    

    fn trace_expr_list<'a>(l : ExprsPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match l.read(ctx) {
            Nil => write!(ctx.tracer(), "{}_\n", l),
            Cons(hd, tl) => write!(ctx.tracer(), "{}.{}.{}\n", l, hd, tl),
        };
        ctx.mut_mgr().finish_write(result);
    }    
     
 
    fn trace_rec_rule_list<'a>(l : RecRulesPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match l.read(ctx) {
            Nil => write!(ctx.tracer(), "{}_\n", l),
            Cons(hd, tl) => write!(ctx.tracer(), "{}.{}.{}\n", l, hd, tl),
        };
        ctx.mut_mgr().finish_write(result);
    }    

    fn trace_declar_list<'a>(l : DeclarsPtr<'a>, ctx : &mut impl IsCtx<'a>) {
        let result = match l.read(ctx) {
            Nil => write!(ctx.tracer(), "{}_\n", l),
            Cons(hd, tl) => write!(ctx.tracer(), "{}.{}.{}\n", l, hd, tl),
        };
        ctx.mut_mgr().finish_write(result);
    }       

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
    mk_trace_step! { trace_calc_height_aux, 'a, CalcHeightAux<'a> }

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

    mk_trace_step! { trace_check_vitals, 'a, CheckVitals<'a> }

    mk_trace_step! { trace_mk_local_params, 'a, MkLocalParams<'a> }
    mk_trace_step! { trace_mk_local_indices1, 'a, MkLocalIndices1<'a> }
    mk_trace_step! { trace_mk_local_indices_aux, 'a, MkLocalIndicesAux<'a> }

    mk_trace_step! { trace_admit_declar, 'a, AdmitDeclar<'a> }


    fn ptr_index<'a, A>(ptr : Ptr<'a, A>) -> usize {
        match ptr {
            | Ptr::E(index, ..)
            | Ptr::L(index, ..)
            | Ptr::P(index, ..) => index
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NoopTracer;

impl std::io::Write for NoopTracer {
    fn write(&mut self, buf : &[u8]) -> IoResult<usize> {
        Ok(0)
    }
    fn flush(&mut self) -> IoResult<()> {
        Ok(())
    }
}

impl IsTracer for NoopTracer {
    const NOOP : bool = true;
    const TERM_ON_IO_ERR : bool = true;
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

impl std::io::Write for StdoutTracer {
    fn write(&mut self, buf : &[u8]) -> IoResult<usize> {
        self.inner.write(buf)
    }

    fn flush(&mut self) -> IoResult<()> {
        self.inner.flush()
    }
}

impl IsTracer for StdoutTracer {
    const NOOP : bool = false;
    const TERM_ON_IO_ERR : bool = true;
}


#[derive(Debug)]
pub struct FileTracer {
    inner : BufWriter<File>,
}

impl std::io::Write for FileTracer {
    fn write(&mut self, buf : &[u8]) -> IoResult<usize> {
        self.inner.write(buf)
    }

    fn flush(&mut self) -> IoResult<()> {
        self.inner.flush()
    }
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
    const TERM_ON_IO_ERR : bool = true;
}

