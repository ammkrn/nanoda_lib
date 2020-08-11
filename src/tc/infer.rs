use crate::name::NamePtr;
use crate::level::{ LevelPtr, LevelsPtr, Level };
use crate::expr::{ Expr, ExprPtr, Expr::* };
use crate::utils::{ List::*, Tc, IsCtx, HasNanodaDbg };
                    
                    
use InferFlag::*;                    


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferFlag {
    InferOnly,
    Check
}                    

impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
    fn infer_const(
        self, 
        c_name : NamePtr<'l>, 
        c_levels : LevelsPtr<'l>, 
        flag : InferFlag, 
        tc : &mut Tc<'t, 'l, 'e>
    ) -> Self {
        let (env_dec_ups, env_dec_type) = match tc.get_declar(&c_name) {
            Some(d) if d.is_unsafe() && tc.safe_only => unreachable!("infer_const; safe_only + unsafe declar : {}", c_name.nanoda_dbg(tc)),
            Some(d) => (d.uparams(), d.type_()),
            None => unreachable!("infer_const nonexistant declar : \n{}\nquot status", c_name.nanoda_dbg(tc)),
        };

        if let (Check, Some(root_uparams)) = (flag, tc.dec_uparams) {
            assert!(c_levels.all_params_defined_many(root_uparams, tc));
        }

        env_dec_type.subst(env_dec_ups, c_levels, tc)    
    }

    pub fn infer_sort_of(self, flag : InferFlag, tc : &mut Tc<'t, 'l, 'e>) -> LevelPtr<'l> {
        let infd = self.infer(flag, tc);
        let whnfd = infd.whnf(tc);
        
        match whnfd.read(tc) {
                  Sort { level } => level,
                  _owise => unreachable!("infer_sort failed to produce a sort!"),
              }
    }    

    fn infer_sort_core(
        self, 
        level : LevelPtr<'l>,
        flag : InferFlag, 
        tc : &mut Tc<'t, 'l, 'e>
    ) -> Self {
        if let (Some(uparams), Check) = (tc.dec_uparams, flag) {
            assert!(level.all_params_defined(uparams, tc));
        }

        level.new_succ(tc).new_sort(tc)
    }    

    // Only makes sure that the Expr tree has the shape "some number of pis
    // applied to an appropriate number of arguments". Since we know `flag` is
    // InferOnly, we don't bother to check that the Pi's binder type
    // is equal to the type of the argument.
    pub fn infer_app(self, flag : InferFlag, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        let (mut fun, mut args) = self.unfold_apps(tc);
        fun = fun.infer(flag, tc);
        let mut context = Nil::<Expr>.alloc(tc);

        while let Cons(hd, tl) = args.read(tc) {
            match fun.read(tc) {
                Pi { b_type, body, .. } => {
                    if flag == Check {
                        let arg_type = hd.infer(flag, tc);
                        b_type.inst(context, tc).assert_def_eq(arg_type, tc);
                    }

                    context = Cons(hd, context).alloc(tc);
                    args = tl;
                    fun = body;
                },
                _ => {
                    let as_pi = fun.inst(context, tc).ensure_pi(tc);
                    match as_pi.read(tc) {
                        Pi {..} => {
                            context = Nil::<Expr>.alloc(tc);
                            fun = as_pi;
                        },
                        _ => unreachable!("infer app could not produce a pi") 
                    }
                }
            }
        }
        fun.inst(context, tc)
    }    

    fn infer_pi(self, flag : InferFlag, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        let mut locals = Nil::<Expr>.alloc(tc);
        let mut universes = Nil::<Level>.alloc(tc);
        let mut cursor = self;

        while let Pi { b_name, b_type, b_style, body, .. } = cursor.read(tc) {
            let b_type = b_type.inst(locals, tc);
            let dom_univ = b_type.infer_sort_of(flag, tc);
            universes = Cons(dom_univ, universes).alloc(tc);
            let local = tc.get_local(b_name, b_type, b_style);
            locals = Cons(local, locals).alloc(tc);
            cursor = body;
        }

        let instd = cursor.inst(locals, tc);
        let mut infd = instd.infer_sort_of(flag, tc);
        loop {
            match (universes.read(tc), locals.read(tc)) {
                (Cons(u, us), Cons(l, ls)) => {
                    universes = us;
                    locals = ls;
                    infd = <LevelPtr>::new_imax(u, infd, tc);
                    tc.replace_local(l);
                },
                (Nil, Nil) => return infd.new_sort(tc),
                _ => unreachable!("Uneven list lens in infer_pis")
            }
        }
    }        

    fn infer_lambda(self, flag : InferFlag, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        let mut b_types = Nil::<Expr>.alloc(tc);
        let mut locals = Nil::<Expr>.alloc(tc);
        let mut cursor = self;

        while let Lambda { b_name, b_type, b_style, body, .. } = cursor.read(tc) {
            b_types = Cons(b_type, b_types).alloc(tc);

            let b_type = b_type.inst(locals, tc);
            if let Check = flag {
                b_type.infer_sort_of(flag, tc);
            }

            let local = tc.get_local(b_name, b_type, b_style);
            locals = Cons(local, locals).alloc(tc);
            cursor = body;
        }

        let instd = cursor.inst(locals, tc);
        let infd = instd.infer(flag, tc);
        let mut abstrd = infd.abstr(locals, tc);

        while let (Cons(t, ts), Cons(l, ls)) = (b_types.read(tc), locals.read(tc)) {
            b_types = ts;
            locals = ls;
            match l.read(tc) {
                Local { b_name, b_style, .. } => {
                    abstrd = <ExprPtr>::new_pi(b_name, t, b_style, abstrd, tc);
                    tc.replace_local(l);
                },
                _ => unreachable!("unreachable pattern match in infer_lambda")
            }
        }

        abstrd
    }

    fn infer_let(
        self, 
        b_type : ExprPtr<'l>,
        val : ExprPtr<'l>,
        body : ExprPtr<'l>,
        flag : InferFlag, 
        tc : &mut Tc<'t, 'l, 'e>
    ) -> Self {
        if flag == Check {
            b_type.infer_sort_of(flag, tc);
            val.infer(flag, tc).assert_def_eq(b_type, tc);
        }

        body.inst1(val, tc).infer(flag, tc)
    }
        
    pub fn ensure_type(self, tc : &mut Tc<'t, 'l, 'e>) -> LevelPtr<'l> {
        self.infer(InferOnly, tc).ensure_sort(tc)
    }

    pub fn ensure_sort(self, tc : &mut Tc<'t, 'l, 'e>) -> LevelPtr<'l> {
        match self.read(tc) {
            Sort { level } => level,
            _ => {
                let whnfd = self.whnf(tc);
                match whnfd.read(tc) {
                    Sort { level } => level,
                    _ => unreachable!("ensur_sort could not produce a sort!")
                }
            }
        }
    }


    fn ensure_pi(self, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        match self.read(tc) {
            Pi {..} => self,
            _ => {
                let whnfd = self.whnf(tc);
                match whnfd.read(tc) {
                    Pi {..} => whnfd,
                    _ => unreachable!("ensure_pi could not produce a pi.")
                }
            }
        }
    }


    pub fn infer(self, flag : InferFlag, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        if let Some(cached) = tc.cache.infer_cache.get(&(self, flag)).copied() {
            return cached
        }

        let r = match self.read(tc) {
            Sort { level } => self.infer_sort_core(level, flag, tc),
            Const { name, levels } => self.infer_const(name, levels, flag, tc),
            App {..} => self.infer_app(flag, tc),
            Pi {..} => self.infer_pi(flag, tc),
            Lambda { .. } => self.infer_lambda(flag, tc), 
            Let { b_type, val, body, .. } => self.infer_let(b_type, val, body, flag, tc),
            Local { b_type, .. } => b_type,
            Var {..} => unimplemented!("Cannot infer the type of a bound variable!"),
        };

        tc.cache.infer_cache.insert((self, flag), r);
        r
    }
}
