use crate::chain;
use crate::name::Name;
use crate::level::{ mk_param, };
use crate::env::{ ConstantBase, QuotVal };
use crate::expr::{ BinderStyle::*, 
                   mk_prop, 
                   mk_local, 
                   mk_const, 
                   mk_app, 
                   mk_sort };

/*
The 'builtin' flag on all of the quot ConstantBases should be set to true.
*/
pub struct Quot {
    pub inner : Vec<QuotVal>
}

impl Quot {
    pub fn new() -> Self {
        let prop = mk_prop();
        let param_u = || mk_param("u");
        let param_v = || mk_param("v");
        let params_u = || vec![param_u()];
        let params_uv = || vec![param_u(), param_v()];
        let sort_u = mk_sort(mk_param("u"));
        let _A = mk_local("A", mk_sort(param_u()), Implicit);
        let _B = mk_local("B", mk_sort(mk_param("v")), Implicit);
        let _R = mk_local("R", _A.mk_arrow(&_A.mk_arrow(&prop)), Default); 
        let _f = mk_local("f", _A.mk_arrow(&_B), Default);
        let _a = mk_local("a", _A.clone(), Default);
        let _b = mk_local("b", _A.clone(), Default);


        let quot_const_univ_u = || mk_const("quot", vec![param_u()]);
        let quot_mk_const_univ_u = || mk_const(Name::from("quot").extend_str("mk"), vec![param_u()]);
        let quot_pi_app = sort_u.fold_pis(chain![&_A, &_R]);

        // First introduction rule. in Lean : 
        // quot : Π {α : Sort u}, (α → α → Prop) → Sort u
        let quot = ConstantBase::new(Name::from("quot"),
                                        params_u().clone(),
                                        quot_pi_app);

        let quot_mk_f_a = mk_const("quot", params_u()).foldl_apps(vec![&_A, &_R]);

        let quot_mk_f = _A.mk_arrow(&quot_mk_f_a);
            
        // Second introduction rule. In lean : 
        // quot.mk : Π {α : Sort u} (r : α → α → Prop), α → @quot α r
        let quot_mk = ConstantBase::new(
            Name::from("quot").extend_str("mk"),
            params_u().clone(),
            quot_mk_f.fold_pis(chain![&_A, &_R]),
        );

        let eq_const = mk_const("eq", vec![param_v()]);
        let app1 = mk_app(_f.clone(), _a.clone());
        let app2 = mk_app(_f.clone(), _b.clone());
        let eq_app = eq_const.foldl_apps(vec![&_B, &app1, &app2]);
        let eq_lhs = _R.foldl_apps(vec![&_a, &_b]);

        let inner_app = eq_lhs.mk_arrow(&eq_app);
        let lower_const = quot_const_univ_u();
        let lower_apps = lower_const.foldl_apps(vec![&_A, &_R]);
        let lhs_pis = inner_app.fold_pis(chain![&_a, &_b]);
        let triple_arrow = lhs_pis.mk_arrow(&(lower_apps.mk_arrow(&_B)));
        let pis_together = triple_arrow.fold_pis(chain![&_A, &_R, &_B, &_f]);


        // Third introduction rule. In lean : 
        // quot.lift : Π {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β), 
        //               (∀ (a b : α), r a b → f a = f b) → quot r → β
        let quot_lift = ConstantBase::new(
            quot.name.extend_str("lift"),
            params_uv().clone(),
            pis_together,
        );

        let B2_arrows_lhs = quot_const_univ_u().foldl_apps(vec![&_A, &_R]);
        let _B2 = mk_local("B",
                                 B2_arrows_lhs.mk_arrow(&prop),
                                 Implicit);
        let _q = mk_local("q",
                                quot_const_univ_u().foldl_apps(vec![&_A, &_R]),
                                Default);

        let ind_pi_1_inner = quot_mk_const_univ_u().foldl_apps(vec![&_A, &_R, &_a]);
        let ind_pi_1_mid = _B2.foldl_apps(Some(&ind_pi_1_inner));
        let ind_pi_1 = ind_pi_1_mid.fold_pis(chain![&_a]);
        let B2_q = _B2.foldl_apps(vec![&_q]);
        let ind_pi_2 = B2_q.fold_pis(chain![&_q]);
        let ind_arrows = ind_pi_1.mk_arrow(&ind_pi_2);

        // Last introduction rule. In Lean : 
        // quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : @quot α r → Prop},
        //            (∀ (a : α), β (@quot.mk α r a)) → ∀ (q : @quot α r), β q
        let quot_ind = ConstantBase::new(
            quot.name.extend_str("ind"),
            params_u().clone(),
            ind_arrows.fold_pis(chain![&_A, &_R, &_B2]),
        );

        let const_eq_v = mk_const("eq", vec![param_v()]);


        let _h = mk_local("h",
                                const_eq_v.foldl_apps(vec![&_b, &app1, &app2]),
                                Default);

        let quot_items = vec![
            QuotVal::from_const_val(quot),
            QuotVal::from_const_val(quot_mk),
            QuotVal::from_const_val(quot_ind),
            QuotVal::from_const_val(quot_lift),
        ];
        Quot {
            inner : quot_items
        }
    }

}