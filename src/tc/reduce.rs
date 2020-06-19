use crate::ret_none_if;
use crate::name::NamePtr;
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::* };
use crate::env::{ Declar, Declar::* };
use crate::utils::{ List::*, Tc, IsCtx };

use crate::tc::eq::ShortCircuit::*;
use crate::tc::infer::InferFlag::*;
                    

impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {

    // This will always return an Expr<Ptr>
    pub fn whnf_core(self, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        let (fun, args) = self.unfold_apps(tc);
        match (fun.read(tc), args.read(tc)) {
            (Sort { level }, _) => level.simplify(tc).new_sort(tc),
            (Lambda {..}, Cons(..)) => fun.whnf_lambda(args, tc),
            (Let { val, body, .. }, _) => {
                body.inst1(val, tc)
                .foldl_apps(args, tc)
                .whnf_core(tc)
            },
            _ => {
                self.reduce_quot_lift(tc)
                .or_else(|| self.reduce_quot_ind(tc))
                .or_else(|| self.reduce_ind_rec(tc)) 
                .unwrap_or(self)
            }
        }
    }


    pub fn whnf_lambda(mut self, mut args : ExprsPtr<'l>, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        let mut acc = Nil::<Expr>.alloc(tc);
        while let (Lambda { body, .. }, Cons(hd, tl)) = (self.read(tc), args.read(tc)) {
            acc = Cons(hd, acc).alloc(tc);
            args = tl;
            self = body;
        }

        self.inst(acc, tc).foldl_apps(args, tc).whnf_core(tc)
    }    


    pub fn whnf(self, tc : &mut Tc<'t, 'l, 'e>) -> Self {
        if let Some(cached) = tc.cache.whnf_cache.get(&self).copied() {
            cached
        } else {
            let mut cursor = self;
            loop {
                let whnfd = cursor.whnf_core(tc);
                if let Some(next_term) = whnfd.unfold_def(tc) {
                    cursor = next_term;
                } else {
                    tc.cache.whnf_cache.insert(self, whnfd);
                    return whnfd
                }
            }
        }
    }    

    pub fn is_delta(self, tc : &mut Tc<'t, 'l, 'e>) -> Option<Declar<'l>> {
        let (fun, _) = self.unfold_apps(tc);
        let (c_name, _) = fun.try_const_info(tc)?;
        match tc.get_declar(&c_name) {
            Some(d @ Definition {..}) => Some(d),
            _ => None
        }
    }


    pub fn unfold_def(self, tc : &mut Tc<'t, 'l, 'e>) -> Option<Self> {
        let (fun, args) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        match tc.get_declar(&c_name)? {
            Definition { uparams, val, .. } 
            if c_levels.len(tc) == uparams.len(tc) => {
                let def_val = val.subst(uparams, c_levels, tc);
                Some(def_val.foldl_apps(args, tc))
            },
            _ => None
        }
    }


    fn reduce_quot_lift(self, tc : &mut Tc<'t, 'l, 'e>) -> Option<Self> {
        let (fun, args) = self.unfold_apps(tc);
        let (c_name, _) = fun.try_const_info(tc)?;
        let (qmk_n, qlift_n, _) = tc.quot_names()?;
        let (qmk_pos, arg_pos) = if c_name == qlift_n { (5, 3) } else { return None };
        let qmk_e = args.get(qmk_pos, tc)?.whnf(tc);
        ret_none_if! { qmk_n != qmk_e.unfold_apps_fun(tc).try_const_info(tc)?.0 };


        let app_lhs = args.get(arg_pos, tc)?;
        let appd = match qmk_e.read(tc) {
            App { arg : f_arg, .. } => app_lhs.new_app(f_arg, tc),
            _ => unreachable!("bad quot_rec (lift) app")
        };

        let skipped = args.skip(qmk_pos + 1, tc);
        let r = appd.foldl_apps(skipped, tc);

        Some(r.whnf_core(tc))
    }    

    


    fn reduce_quot_ind(self, tc : &mut Tc<'t, 'l, 'e>) -> Option<Self> {
        let (fun, args) = self.unfold_apps(tc);
        let (c_name, _) = fun.try_const_info(tc)?;
        let (qmk_n, _, qind_n) = tc.quot_names()?;
        let (qmk_pos, arg_pos) = if c_name == qind_n { (4, 3) } else { return None };

        let qmk_e = args.get(qmk_pos, tc)?.whnf(tc);
        ret_none_if! { qmk_n != qmk_e.unfold_apps_fun(tc).try_const_info(tc)?.0 };

        let f_appd = match qmk_e.read(tc) {
            App { arg : f_arg, .. } => args.get(arg_pos, tc)?.new_app(f_arg, tc),
            _ => unreachable!("bad quot_rec (ind) app")
        };

        let r = f_appd.foldl_apps(args.skip(qmk_pos + 1, tc), tc);
        Some(r.whnf_core(tc))
    }    
    

    
    fn mk_nullary_cnstr(self, num_params : u16, tc : &mut Tc<'t, 'l, 'e>) -> Option<Self> {
        let (fun, args) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        let cnstr_name = match tc.get_declar(&c_name)? {
            Inductive { all_cnstr_names, .. } => all_cnstr_names.get(0, tc),
            _ => None
        }?;
        let new_const = <ExprPtr>::new_const(cnstr_name, c_levels, tc);
        Some(new_const.foldl_apps(args.take(num_params as usize, tc), tc))
    }
    

    
    fn to_cnstr_when_k(
        self,
        rec_name : NamePtr<'l>,
        rec_is_k : bool,
        rec_num_params : u16,
        tc : &mut Tc<'t, 'l, 'e>
    ) -> Option<Self> {
        ret_none_if! { !rec_is_k };
        let app_type = self.infer(InferOnly, tc).whnf(tc);
        ret_none_if! { app_type.unfold_apps_fun(tc).try_const_info(tc)?.0 != rec_name.get_prefix(tc) };
        let new_cnstr_app = app_type.mk_nullary_cnstr(rec_num_params, tc)?;
        let new_type = new_cnstr_app.infer(InferOnly, tc);

        if let EqShort = app_type.def_eq(new_type, tc) {
            Some(new_cnstr_app)
        } else {
            None
        }
    }
    


    fn reduce_ind_rec(self, tc : &mut Tc<'t, 'l, 'e>) -> Option<Self> {
        let (fun, args) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;

        
        let recursor = match tc.get_declar(&c_name)? {
            r @ Recursor {..} => r,
            _ => return None
        };

        let take_size = recursor.rec_num_params()?
                      + recursor.rec_num_motives()?
                      + recursor.rec_num_minors()?;

        ret_none_if! { recursor.rec_major_idx()? as usize >= args.len(tc) };
        ret_none_if! { c_levels.len(tc) != recursor.uparams().len(tc) };

        let major = args.get(recursor.rec_major_idx()? as usize, tc)?;
        let major = major.to_cnstr_when_k(
            recursor.name(), 
            recursor.rec_is_k()?, 
            recursor.rec_num_params()?, 
            tc
        ).unwrap_or(major);

        let major = major.whnf(tc);
        
        let (_, major_args) = major.unfold_apps(tc);

        let rule = recursor.get_rec_rule(major, tc)?.read(tc);

        let num_params = major_args.len(tc).checked_sub(rule.num_fields as usize)?;
        let end_apps = major_args.skip(num_params, tc).take(rule.num_fields as usize, tc);

        let r = rule.val
            .subst(recursor.uparams(), c_levels, tc)
            .foldl_apps(args.take(take_size as usize, tc), tc)
            .foldl_apps(end_apps, tc)
            .foldl_apps(args.skip((recursor.rec_major_idx()? + 1) as usize, tc), tc);
        Some(r.whnf_core(tc))
    }    

}