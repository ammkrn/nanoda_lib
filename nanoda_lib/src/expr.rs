use crate::utils::{ IsCtx, IsLiveCtx, List, List::*, Ptr, ListPtr, Store, Env, Live, EnvZst, LiveZst, HasMkPtr, Set, HasNanodaDbg };
use crate::name::{ NamePtr, NamesPtr };
use crate::level::{ LevelPtr, Level, LevelsPtr };
use crate::env::{ Declar::*, ReducibilityHint::* };
use crate::trace::IsTracer;
use crate::trace::items::{ HasTraceItem };
use crate::trace::steps::*;

pub type ExprPtr<'a> = Ptr<'a, Expr<'a>>;
pub type ExprsPtr<'a> = ListPtr<'a, Expr<'a>>;


use Level::*;
use Expr::*;
use BinderStyle::*;


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalSerial(pub u64);


pub fn safe_pred(n : u16) -> u16 {
    if n == 0 {
        n
    } else {
        n - 1
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderStyle {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expr<'a> {
    Var { 
        dbj : u16
    },
    Sort {
        level : LevelPtr<'a>,
    },
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
    },
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial
    }

}


impl<'a> Expr<'a> {
    pub fn insert_env<'e>(self, env : &mut Env<'e, impl 'e + IsTracer>, live : &Store<LiveZst>) -> ExprPtr<'e> {
        let r = match self {
            Var { dbj } => <ExprPtr>::new_var(dbj, env),
            Sort { level } => level.insert_env(env, live).new_sort(env),
            Const { name, levels } => {
                let name = name.insert_env(env, live);
                let levels = levels.insert_env(env, live);
                <ExprPtr>::new_const(name, levels, env)
            },
            App { fun, arg, .. } => {
                let fun = fun.insert_env(env, live);
                let arg = arg.insert_env(env, live);
                fun.new_app(arg, env)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                let body = body.insert_env(env, live);
                <ExprPtr>::new_pi(b_name, b_type, b_style, body, env)
            },
            Lambda { b_name, b_type, b_style, body, .. } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                let body = body.insert_env(env, live);
                <ExprPtr>::new_lambda(b_name, b_type, b_style, body, env)
            },
            Let { b_name, b_type, b_style, val, body, .. } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                let val = val.insert_env(env, live);
                let body = body.insert_env(env, live);
                <ExprPtr>::new_let(b_name, b_type, b_style, val, body, env)
            },
            Local { b_name, b_type, b_style, serial } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                Local { b_name, b_type, b_style, serial }.alloc(env)
            }
        };
        assert!(r.in_env());
        r
    }    
}

fn fmt_binder<'a>(b_name : NamePtr<'a>, b_type : ExprPtr<'a>, b_style : BinderStyle, ctx : &impl IsCtx<'a>) -> String {
    let b_name = b_name.nanoda_dbg(ctx);
    let b_type = b_type.nanoda_dbg(ctx);
    match b_style {
        Default => {
            format!("({} : {})", b_name, b_type)
        },
        Implicit => {
            format!("{{{} : {}}}", b_name, b_type)

        },
        StrictImplicit => {
            format!("{{{{{} : {}}}}}", b_name, b_type)

        },
        InstImplicit => {
            format!("[{} : {}]", b_name, b_type)

        }
    }
}

impl<'a> ExprPtr<'a> {
    // This is for testing only.
    pub fn eq_mod_locals(self, other : Self, ctx : &impl IsCtx<'a>) -> bool {
        match (self.read(ctx), other.read(ctx)) {
            _ if self == other => true,
            (Var {..}, Var{..})
            | (Sort {..}, Sort {..})
            | (Const {..}, Const {..}) => self == other,
            (App { fun:f1, arg:a1, ..}, App { fun:f2, arg:a2, .. }) => {
                f1.eq_mod_locals(f2, ctx)
                &&
                a1.eq_mod_locals(a2, ctx)
            },
            | (Pi { b_type:t1, body:b1, .. }, Pi { b_type:t2, body:b2, .. }) 
            | (Lambda { b_type:t1, body:b1, .. }, Lambda { b_type:t2, body:b2, .. }) => {
                t1.eq_mod_locals(t2, ctx)
                && b1.eq_mod_locals(b2, ctx)
            }
            (Let { b_type:t1, val:v1, body:b1, .. }, 
             Let { b_type:t2, val:v2, body:b2, .. }) => {
                t1.eq_mod_locals(t2, ctx)
                && v1.eq_mod_locals(v2, ctx)
                && b1.eq_mod_locals(b2, ctx)
            }
            (Local { b_type:t1, .. }, Local { b_type:t2, .. }) => {
                t1.eq_mod_locals(t2, ctx)
            },
            _ => false
        }
    }

    pub fn var_bound(self, ctx : &impl IsCtx<'a>) -> u16 {
        match self.read(ctx) {
            Var { dbj } => (dbj + 1),
            | Sort {..} | Const {..} | Local {..} => 0,
            | App { var_bound, .. }
            | Pi { var_bound, ..} 
            | Lambda { var_bound, ..}
            | Let { var_bound, .. } => var_bound,
        }
    }

    pub fn has_locals(self, ctx : &impl IsCtx<'a>) -> bool {
        match self.read(ctx) {
            Var {..} => false,
            | Sort {..} | Const {..} => false,
            | App { locals, .. }
            | Pi { locals, ..} 
            | Lambda { locals, ..}
            | Let { locals, .. } => locals,
            | Local {..} => true
        }
    }


    pub fn try_const_info(self, ctx : &impl IsLiveCtx<'a>) -> Option<(NamePtr<'a>, LevelsPtr<'a>)> {
        match self.read(ctx) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None
        }
    }


    pub fn telescope_size(
        self, 
        ctx : &mut impl IsCtx<'a>
    ) -> (u16, Step<TelescopeSize<'a>>) {
        match self.read(ctx) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let (inner_size, h1) = body.telescope_size(ctx);
                TelescopeSize::Pi {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    inner_size,
                    h1,
                    size : inner_size + 1
                }.step(ctx)
            }
            _ => {
                let (b, h1) = self.is_pi(ctx);
                assert!(!b);
                TelescopeSize::Owise {
                    e : self,
                    h1,
                    size : 0u16
                }.step(ctx)
            }
        }
    }

    pub fn local_serial_infal(self, ctx : &impl IsLiveCtx<'a>) -> LocalSerial {
        match self.read(ctx) {
            Local { serial, .. } => serial,
            _ => panic!("can't take serial of a non-local expr")
        }
    }

    pub fn local_type_infal(self, ctx : &impl IsCtx<'a>) -> Self {
        match self.read(ctx) {
            Local { b_type, .. } => b_type,
            _ => panic!("Can't take local type from non-local!")
        }
    }

    pub fn new_var(dbj : u16, ctx : &mut impl IsCtx<'a>) -> Self {
        Var { dbj }.alloc(ctx)
    }

    pub fn new_const(
        name : NamePtr<'a>, 
        levels : LevelsPtr<'a>, 
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        Const {
            name,
            levels
        }.alloc(ctx)
    }

    pub fn new_app(self, arg : Self, ctx : &mut impl IsCtx<'a>) -> Self {
        App {
            fun : self,
            arg,
            var_bound : self.var_bound(ctx).max(arg.var_bound(ctx)),
            locals : self.has_locals(ctx) || arg.has_locals(ctx),
        }.alloc(ctx)
    }

    pub fn new_pi(
        b_name : NamePtr<'a>,
        b_type : Self,
        b_style : BinderStyle,
        body : Self,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        Pi {
            b_name,
            b_type,
            b_style,
            body,
            var_bound : b_type.var_bound(ctx).max(safe_pred(body.var_bound(ctx))),
            locals : b_type.has_locals(ctx) || body.has_locals(ctx)
        }.alloc(ctx)
    }    

    pub fn new_lambda(
        b_name : NamePtr<'a>,
        b_type : Self,
        b_style : BinderStyle,
        body : Self,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        Lambda {
            b_name,
            b_type,
            b_style,
            body,
            var_bound : b_type.var_bound(ctx).max(safe_pred(body.var_bound(ctx))),
            locals : b_type.has_locals(ctx) || body.has_locals(ctx)
        }.alloc(ctx)
    }
    
    pub fn new_let(
        b_name : NamePtr<'a>,
        b_type : Self,
        b_style : BinderStyle,
        val : Self,
        body : Self,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
          Let {
              b_name,
              b_type,
              b_style,
              val,
              body,
              var_bound : b_type.var_bound(ctx)
                          .max(val.var_bound(ctx))
                          .max(safe_pred(body.var_bound(ctx))),
            locals : b_type.has_locals(ctx) || body.has_locals(ctx) || val.has_locals(ctx)
        }.alloc(ctx)              
    }
    
    pub fn new_local(
        b_name : NamePtr<'a>, 
        b_type : Self,
        b_style : BinderStyle,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> ExprPtr<'a> {
        let l = Local {
            b_name,
            b_type,
            b_style,
            serial : ctx.next_local()
        }.alloc(ctx);
        assert!(!l.in_env());
        l
    }
}

impl<'a> ExprPtr<'a> {

    pub fn is_app(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsApp<'a>>) {
        match self.read(ctx) {
            Var { dbj } => {
                IsApp::Var {
                    dbj,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Sort { level } => {
                IsApp::Sort {
                    level,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Const { name, levels } => {
                IsApp::Const {
                    name,
                    levels,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            App { fun, arg, .. } => {
                IsApp::App{
                    fun,
                    arg,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                IsApp::Pi {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Lambda { b_name, b_type, b_style, body, .. } => {
                IsApp::Lambda {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Let { b_name, b_type, b_style, val, body, .. } => {
                IsApp::Let {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Local { b_name, b_type, b_style, serial } => {
                IsApp::Local {
                    b_name,
                    b_type,
                    b_style,
                    serial,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
        }
    }

    pub fn is_pi(self, ctx : &mut impl IsCtx<'a>) -> (bool, Step<IsPi<'a>>) {
        match self.read(ctx) {
            Var { dbj } => {
                IsPi::Var {
                    dbj,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Sort { level } => {
                IsPi::Sort {
                    level,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Const { name, levels } => {
                IsPi::Const {
                    name,
                    levels,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            App { fun, arg, .. } => {
                IsPi::App{
                    fun,
                    arg,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                IsPi::Pi {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            }
            Lambda { b_name, b_type, b_style, body, .. } => {
                IsPi::Lambda {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Let { b_name, b_type, b_style, val, body, .. } => {
                IsPi::Let {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Local { b_name, b_type, b_style, serial } => {
                IsPi::Local {
                    b_name,
                    b_type,
                    b_style,
                    serial,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
        }
    }    

    pub fn is_lambda(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsLambda<'a>>) {
        match self.read(ctx) {
            Var { dbj } => {
                IsLambda::Var {
                    dbj,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Sort { level } => {
                IsLambda::Sort {
                    level,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Const { name, levels } => {
                IsLambda::Const {
                    name,
                    levels,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            App { fun, arg, .. } => {
                IsLambda::App{
                    fun,
                    arg,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                IsLambda::Pi {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Lambda { b_name, b_type, b_style, body, .. } => {
                IsLambda::Lambda {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            }
            Let { b_name, b_type, b_style, val, body, .. } => {
                IsLambda::Let {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
            Local { b_name, b_type, b_style, serial } => {
                IsLambda::Local {
                    b_name,
                    b_type,
                    b_style,
                    serial,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
        }
    }


    pub fn has_ind_occ(
        self,
        ind_names : NamesPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<HasIndOcc<'a>>) {
        if let Some((cached, h1)) = ctx.expr_cache().find_cache.get(&self).copied() {
            HasIndOcc::CacheHit {
                e : self,
                ind_names,
                b : cached,
                h1,
            }.step(ctx)
        } else {
            match self.read(ctx) {
                Var { dbj } => {
                    HasIndOcc::Var {
                        dbj,
                        ind_names,
                        ind_arg1 : self,
                        ind_arg3 : false,
                    }.step(ctx)
                },
                Sort { level } => {
                    HasIndOcc::Sort {
                        l : level,
                        ind_names,
                        ind_arg1 : self,
                        ind_arg3 : false,
                    }.step(ctx)
                },
                Const { name, levels } => {
                    let (b, h1) = name.mem(ind_names, ctx);
                    HasIndOcc::Const {
                        name,
                        levels,
                        ind_names,
                        b,
                        h1,
                        ind_arg1 : self,
                    }.step(ctx)
                },
                App { fun, arg, .. } => {
                    let (b1, h1) = fun.has_ind_occ(ind_names, ctx);
                    let (b2, h2) = arg.has_ind_occ(ind_names, ctx);
                    HasIndOcc::App {
                        fun,
                        arg,
                        ind_names,
                        b1,
                        b2,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg3 : (b1 || b2)
                    }.step(ctx)
                },
                Pi { b_name, b_type, b_style, body, .. } => {
                    let (b1, h1) = b_type.has_ind_occ(ind_names, ctx);
                    let (b2, h2) = body.has_ind_occ(ind_names, ctx);
                    HasIndOcc::Pi {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        b1,
                        b2,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg3 : b1 || b2
                    }.step(ctx)
                }
                Lambda { b_name, b_type, b_style, body, .. } => {
                    let (b1, h1) = b_type.has_ind_occ(ind_names, ctx);
                    let (b2, h2) = body.has_ind_occ(ind_names, ctx);
                    HasIndOcc::Lambda {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        b1,
                        b2,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg3 : (b1 || b2)
                    }.step(ctx)
                }                
                Let { b_name, b_type, b_style, val, body, .. } => {
                    let (b1, h1) = b_type.has_ind_occ(ind_names, ctx);
                    let (b2, h2) = val.has_ind_occ(ind_names, ctx);
                    let (b3, h3) = body.has_ind_occ(ind_names, ctx);
                    HasIndOcc::Let {
                        b_name,
                        b_type,
                        b_style,
                        val,
                        body,
                        b1,
                        b2,
                        b3,
                        h1,
                        h2,
                        h3,
                        ind_arg1 : self,
                        ind_arg3 : (b1 || b2)
                    }.step(ctx)
                },
                Local { b_name, b_type, b_style, serial } => {
                    let (b, h1) = b_type.has_ind_occ(ind_names, ctx);
                    HasIndOcc::Local {
                        b_name,
                        b_type,
                        b_style,
                        serial,
                        h1,
                        ind_arg1 : self,
                        ind_arg3 : b,
                    }.step(ctx)
                }                            
            }
        }
    }

    pub fn subst(
        self,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<SubstE<'a>>) {
        if let Some((e_prime, h1)) = ctx.expr_cache().subst_cache.get(&(self, ks, vs)).copied() {
            SubstE::CacheHit {
                e : self,
                ks,
                vs,
                e_prime,
                h1,
            }.step(ctx)
        } else {
            let calcd = match self.read(ctx) {
                Var { dbj } => {
                    SubstE::Var {
                        dbj,
                        ks,
                        vs,
                        ind_arg1 : self
                    }.step(ctx)
                }
                Sort { level } => {
                    let (l_prime, h1) = level.subst(ks, vs, ctx);
                    SubstE::Sort {
                        l : level,
                        ks,
                        vs,
                        l_prime,
                        h1,
                        ind_arg1 : self,
                        ind_arg4 : l_prime.new_sort(ctx)
                    }.step(ctx)
                },
                Const { name, levels } => {
                    let (levels_prime, h1) = levels.subst_many(ks, vs, ctx);
                    SubstE::Const {
                        name,
                        levels,
                        ks,
                        vs,
                        levels_prime,
                        h1,
                        ind_arg1 : self,
                        ind_arg4 : <Self>::new_const(name, levels_prime, ctx)
                    }.step(ctx)
                },
                App { fun, arg, .. } => {
                    let (fun_prime, h1) = fun.subst(ks, vs, ctx);
                    let (arg_prime, h2) = arg.subst(ks, vs, ctx);
                    let e_prime = <Self>::new_app(fun_prime, arg_prime, ctx);
                    SubstE::App {
                        fun,
                        arg,
                        ks,
                        vs,
                        fun_prime,
                        arg_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)
                },
                Pi { b_name, b_type, b_style, body, .. } => {
                    let (b_type_prime, h1) = b_type.subst(ks, vs, ctx);
                    let (body_prime, h2) = body.subst(ks, vs, ctx);
                    let e_prime = <Self>::new_pi(b_name, b_type_prime, b_style, body_prime, ctx);
                    SubstE::Pi {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        ks,
                        vs,
                        b_type_prime,
                        body_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)
                }
                Lambda { b_name, b_type, b_style, body, .. } => {
                    let (b_type_prime, h1) = b_type.subst(ks, vs, ctx);
                    let (body_prime, h2) = body.subst(ks, vs, ctx);
                    let e_prime = <Self>::new_lambda(b_name, b_type_prime, b_style, body_prime, ctx);
                    SubstE::Lambda {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        ks,
                        vs,
                        b_type_prime,
                        body_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)
                }                
                Let { b_name, b_type, b_style, val, body, .. } => {
                    let (b_type_prime, h1) = b_type.subst(ks, vs, ctx);
                    let (val_prime, h2) = val.subst(ks, vs, ctx);
                    let (body_prime, h3) = body.subst(ks, vs, ctx);
                    let e_prime = <Self>::new_let(b_name, b_type_prime, b_style, val_prime, body_prime, ctx);
                    SubstE::Let {
                        b_name,
                        b_type,
                        b_style,
                        val,
                        body,
                        ks,
                        vs,
                        b_type_prime,
                        val_prime,
                        body_prime,
                        h1,
                        h2,
                        h3,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)
                },
                Local { b_name, b_type, b_style, serial } => {
                    let (b_type_prime, h1) = b_type.subst(ks, vs, ctx);
                    let e_prime = <Self>::new_local(b_name, b_type_prime, b_style, ctx);
                    let serial_prime = e_prime.local_serial_infal(ctx);
                    SubstE::Local {
                        b_name,
                        b_type,
                        b_style,
                        ks,
                        vs,
                        b_type_prime,
                        serial_prime,
                        h1,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)
                }                        
            };

            ctx.expr_cache().subst_cache.insert((self, ks, vs), calcd);
            calcd
        }
    }


    pub fn inst1(
        self,
        sub : ExprPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<Inst<'a>>) {
        let l = Cons(sub, Nil::<Expr>.alloc(ctx)).alloc(ctx);
        self.inst(l, ctx)
    }

    pub fn inst(
        self, 
        subs : ExprsPtr<'a>, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<Inst<'a>>) {
        if self.var_bound(ctx) == 0 {
            Inst::NoBound {
                e : self,
                subs,
                h1 : self.var_bound(ctx) == 0,
            }.step(ctx)
        } else {
            let (e_prime, h1) = self.inst_aux(subs, 0u16, ctx);
            ctx.expr_cache().inst_cache.clear();
            Inst::ByAux {
                e : self,
                subs,
                e_prime,
                h1
            }.step(ctx)
        }
    }            
    
    fn inst_aux(
        self, 
        subs : ExprsPtr<'a>, 
        offset : u16, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<InstAux<'a>>) {
        if self.var_bound(ctx) <= offset {
            InstAux::NoBound {
                e : self,
                subs, 
                offset,
                h1 : self.var_bound(ctx) <= offset,
            }.step(ctx)
        } else if let Some((cached, h1)) = ctx.expr_cache().inst_cache.get(&(self, offset)).copied() {
            InstAux::CacheHit {
                e : self,
                subs,
                offset,
                e_prime : cached,
                h1,
            }.step(ctx)
        } else {
            let calcd = match self.read(ctx) {
                Var { dbj } => {
                    match subs.get((dbj as usize) - (offset as usize), ctx) {
                        (Some(e_prime), h1) => {
                            InstAux::VarHit {
                                dbj,
                                subs,
                                offset,
                                e_prime,
                                h1,
                                ind_arg1 : self,
                            }.step(ctx)
                        },
                        (None, h1) => {
                            InstAux::VarMiss {
                                dbj,
                                subs,
                                offset,
                                h1,
                                ind_arg1 : self
                            }.step(ctx)
                        }
                    }
                },
                App { fun,  arg, .. } => {
                    let (fun_prime, h1) = fun.inst_aux(subs, offset, ctx);
                    let (arg_prime, h2) = arg.inst_aux(subs, offset, ctx);
                    let e_prime = fun_prime.new_app(arg_prime, ctx);
                    InstAux::App {
                        fun,
                        arg,
                        subs,
                        offset,
                        fun_prime,
                        arg_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime,
                    }.step(ctx)
                },
                Pi { b_name, b_type, b_style, body, .. } => {
                    let (b_type_prime, h1) = b_type.inst_aux(subs, offset, ctx);
                    let (body_prime, h2) = body.inst_aux(subs, offset + 1, ctx);
                    let e_prime = <ExprPtr>::new_pi(b_name, b_type_prime, b_style, body_prime, ctx);
                    InstAux::Pi {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        subs,
                        offset,
                        b_type_prime,
                        body_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime,
                    }.step(ctx)
                }
                Lambda { b_name, b_type, b_style, body, .. } => {
                    let (b_type_prime, h1) = b_type.inst_aux(subs, offset, ctx);
                    let (body_prime, h2) = body.inst_aux(subs, offset + 1, ctx);
                    let e_prime = <ExprPtr>::new_lambda(b_name, b_type_prime, b_style, body_prime, ctx);
                    InstAux::Lambda {
                        b_name,
                        b_style,
                        b_type,
                        body,
                        subs,
                        offset,
                        b_type_prime,
                        body_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)                    
                }
                Let { b_name, b_type, b_style, val, body, .. } => {
                    let (b_type_prime, h1) = b_type.inst_aux(subs, offset, ctx);
                    let (val_prime, h2) = val.inst_aux(subs, offset, ctx);
                    let (body_prime, h3) = body.inst_aux(subs, offset + 1, ctx);
                    let e_prime = <ExprPtr>::new_let(b_name, b_type_prime, b_style, val_prime, body_prime, ctx);
                    InstAux::Let {
                        b_name,
                        b_style,
                        b_type,
                        val,
                        body,
                        subs,
                        offset,
                        b_type_prime,
                        val_prime,
                        body_prime,
                        h1,
                        h2,
                        h3,
                        ind_arg1 : self,
                        ind_arg4 : e_prime
                    }.step(ctx)                     
                }
                owise => unreachable!("Unreachable path in inst_aux : {}", owise.nanoda_dbg(ctx))
            };
            ctx.expr_cache().inst_cache.insert((self, offset), calcd.clone());
            calcd
        }
    }            


    pub fn abstr1(
        self,
        local : ExprPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (Self, Step<Abstr<'a>>) {
        let l = Cons(local, Nil::<Expr>.alloc(ctx)).alloc(ctx);
        self.abstr(l, ctx)
    }

    pub fn abstr(
        self,
        locals : ExprsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (Self, Step<Abstr<'a>>) {
        if !self.has_locals(ctx) {
            Abstr::NoLocals {
                e : self,
                locals,
            }.step(ctx)
        } else {
            let (e_prime, h1) = self.abstr_aux(locals, 0u16, ctx);
            ctx.expr_cache().abstr_cache.clear();
            Abstr::ByAux {
                e : self,
                locals,
                h1,
                ind_arg3 : e_prime
            }.step(ctx)
        }
    }

    pub fn abstr_aux(
        self,
        locals : ExprsPtr<'a>,
        offset : u16,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (Self, Step<AbstrAux<'a>>) {
        if !self.has_locals(ctx) {
            AbstrAux::NoLocals {
                e : self,
                locals,
                offset,
                h1 : self.has_locals(ctx)
            }.step(ctx)
        } else if let Some((e_prime, h1)) = ctx.expr_cache().abstr_cache.get(&(self, offset)).copied() {
            AbstrAux::CacheHit {
                e : self,
                locals,
                offset,
                e_prime,
                h1,
            }.step(ctx)
        } else {
            let calcd = match self.read(ctx) {
                Local { b_name, b_type, b_style, serial } => {
                    match self.pos(locals, ctx) {
                        (Some(pos), h1) => {
                            AbstrAux::LocalHit {
                                b_name,
                                b_type,
                                b_style,
                                serial,
                                locals,
                                offset,
                                pos,
                                h1,
                                ind_arg1 : self,
                                ind_arg4 : <Self>::new_var(pos as u16 + offset, ctx),
                            }.step(ctx)
                        },
                        (None, h1) => {
                            AbstrAux::LocalMiss {
                                b_name,
                                b_type,
                                b_style,
                                serial,
                                locals,
                                offset,
                                h1,
                                ind_arg1 : self,
                            }.step(ctx)
                        }
                    }
                }
                App { fun,  arg, .. } => {
                    let (fun_prime, h1) = fun.abstr_aux(locals, offset, ctx);
                    let (arg_prime, h2) = arg.abstr_aux(locals, offset, ctx);
                    let e_prime = <Self>::new_app(fun_prime, arg_prime, ctx);
                    AbstrAux::App {
                        fun,
                        arg,
                        locals,
                        offset,
                        fun_prime,
                        arg_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime,
                    }.step(ctx)
                },
                Pi { b_name, b_type, b_style, body, .. } => {
                    let (b_type_prime, h1) = b_type.abstr_aux(locals, offset, ctx);
                    let (body_prime, h2) = body.abstr_aux(locals, offset + 1, ctx);
                    let e_prime = <Self>::new_pi(b_name, b_type_prime, b_style, body_prime, ctx);
                    AbstrAux::Pi {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        b_type_prime,
                        body_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime,
                    }.step(ctx)
                }
                Lambda { b_name, b_type, b_style, body, .. } => {
                    let (b_type_prime, h1) = b_type.abstr_aux(locals, offset, ctx);
                    let (body_prime, h2) = body.abstr_aux(locals, offset + 1, ctx);
                    let e_prime = <Self>::new_lambda(b_name, b_type_prime, b_style, body_prime, ctx);
                    AbstrAux::Lambda {
                        b_name,
                        b_type,
                        b_style,
                        body,
                        b_type_prime,
                        body_prime,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg4 : e_prime,
                    }.step(ctx)
                }
                Let { b_name, b_type, b_style, val, body, .. } => {
                    let (b_type_prime, h1) = b_type.abstr_aux(locals, offset, ctx);
                    let (val_prime, h2) = val.abstr_aux(locals, offset, ctx);
                    let (body_prime, h3) = body.abstr_aux(locals, offset + 1, ctx);
                    let e_prime = <Self>::new_let(b_name, b_type_prime, b_style, val_prime, body_prime, ctx);
                    AbstrAux::Let {
                        b_name,
                        b_type,
                        b_style,
                        val,
                        body,
                        b_type_prime,
                        val_prime,
                        body_prime,
                        h1,
                        h2,
                        h3,
                        ind_arg1 : self,
                        ind_arg4 : e_prime,
                    }.step(ctx)
                }
                owise => unreachable!("unreachable path in abstr_aux : {}", owise.nanoda_dbg(ctx))
            };
    
            ctx.expr_cache().abstr_cache.insert((self, offset), calcd);
            calcd
        }
    }    

    pub fn apply_pi(
        self,
        body : Self,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<ApplyPi<'a>>) {
        match self.read(ctx) {
            Local { b_name, b_type, b_style, serial } => {
                let (body_prime, h1) = body.abstr1(self, ctx);
                let e_prime = <Self>::new_pi(b_name, b_type, b_style, body_prime, ctx);
                ApplyPi::Base {
                    b_name,
                    b_type,
                    b_style,
                    serial : self.local_serial_infal(ctx),
                    body,
                    body_prime,
                    local_dom : self,
                    h1,
                    ind_arg4 : e_prime 
                }.step(ctx)
            },
            owise => unreachable!("Cannot apply pi with a non-local! {}", owise.nanoda_dbg(ctx))
        }
    }

    pub fn apply_lambda(
        self,
        body : Self,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<ApplyLambda<'a>>) {
        match self.read(ctx) {
            Local { b_name, b_type, b_style, serial } => {
                let (body_prime, h1) = body.abstr1(self, ctx);
                let e_prime = <Self>::new_lambda(b_name, b_type, b_style, body_prime, ctx);
                ApplyLambda::Base {
                    b_name,
                    b_type,
                    b_style,
                    serial : self.local_serial_infal(ctx),
                    body,
                    body_prime,
                    local_dom : self,
                    h1,
                    ind_arg4 : e_prime 
                }.step(ctx)
            },
            owise => unreachable!("Cannot apply lambda with a non-local! {}", owise.nanoda_dbg(ctx))
        }
    }    




    pub fn unfold_apps_aux(
        self, 
        sink : ExprsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> ((Self, ExprsPtr<'a>), Step<UnfoldAppsAux<'a>>) {
        match self.read(ctx) {
            App { fun, arg, .. } => {
                let sink_prime = Cons(arg, sink).alloc(ctx);
                let ((base_f, all_args), h1) = fun.unfold_apps_aux(sink_prime, ctx);
                UnfoldAppsAux::App {
                    fun,
                    arg,
                    sink,
                    base_f,
                    all_args,
                    h1,
                    ind_arg1 : self,
                    out : (base_f, all_args)
                }.step(ctx)
            },
            _ => {
                let (b, h1) = self.is_app(ctx);
                assert!(!b);
                UnfoldAppsAux::Base {
                    f : self,
                    args : sink,
                    h1,
                    out : (self, sink)
                }.step(ctx)
            }

        }
    }

    pub fn unfold_apps(
        self, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> ((Self, ExprsPtr<'a>), Step<UnfoldAppsAux<'a>>) {
        self.unfold_apps_aux(Nil::<Expr>.alloc(ctx), ctx)
    }          

    pub fn foldl_apps(
        self,
        args : ExprsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (Self, Step<FoldlApps<'a>>) {
        match args.read(ctx) {
            Nil => {
                FoldlApps::Nil {
                    base : self,
                    ind_arg1 : args,
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let mk_app = self.new_app(hd, ctx);
                let (folded, h1) = mk_app.foldl_apps(tl, ctx);
                FoldlApps::Cons {
                    base : self,
                    hd,
                    tl,
                    folded,
                    h1,
                    ind_arg2 : args,
                }.step(ctx)
            }
        }
    }

}

impl<'a> ExprsPtr<'a> {
    pub fn fold_pis(
        self,
        body : ExprPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (ExprPtr<'a>, Step<FoldPis<'a>>) {
        match self.read(ctx) {
            Nil => {
                FoldPis::Nil {
                    ind_arg1 : self,
                    body,
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let (sink, h1) = tl.fold_pis(body, ctx);
                let (out, h2) = hd.apply_pi(sink, ctx);
                FoldPis::Cons {
                    hd,
                    tl,
                    body,
                    sink,
                    out,
                    h1,
                    h2,
                    ind_arg1 : self,
                }.step(ctx)
            }
        }
    }

    pub fn fold_lambdas(
        self,
        body : ExprPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (ExprPtr<'a>, Step<FoldLambdas<'a>>) {
        match self.read(ctx) {
            Nil => {
                FoldLambdas::Nil {
                    ind_arg1 : self,
                    body,
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let (sink, h1) = tl.fold_lambdas(body, ctx);
                let (out, h2) = hd.apply_lambda(sink, ctx);
                FoldLambdas::Cons {
                    hd,
                    tl,
                    body,
                    sink,
                    out,
                    h1,
                    h2,
                    ind_arg1 : self,
                }.step(ctx)
            }
        }
    }
}

impl<'a> HasNanodaDbg<'a> for Expr<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String {
        match self {
            Var { dbj } => format!("Var{}", dbj),
            Sort { level } => format!("Sort {}", level.nanoda_dbg(ctx)),
            Const { name, levels } => {
                let name = name.nanoda_dbg(ctx);
                let levels = levels.nanoda_dbg(ctx);
                format!("Const ({}, {})", name, levels)
            }
            App { fun, arg, .. } => {
                let fun = fun.nanoda_dbg(ctx);
                let arg = arg.nanoda_dbg(ctx);
                format!("App ({}, {})", fun, arg)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let body = body.nanoda_dbg(ctx);
                format!("Π {}, ({})", binder, body)
            }
            Lambda { b_name, b_type, b_style, body, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let body = body.nanoda_dbg(ctx);
                format!("λ {}, ({})", binder, body)
            }
            Let { b_name, b_type, b_style, val, body, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let body = body.nanoda_dbg(ctx);
                let val = val.nanoda_dbg(ctx);
                format!("Let {} := {} in {}", binder, val, body)
            },
            Local { b_name, b_type, b_style, serial, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let serial = match serial {
                    LocalSerial(n) => n
                };
                format!("ser({}) of {}", serial, binder)
            }
        }
    }
}