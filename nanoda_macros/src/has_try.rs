use quote::format_ident;
use syn::{ 
    parse_quote, 
    parse::Parse,
    parse::ParseStream,
    parse::Result as ParseResult,
};

pub struct TryMethod {
    tc_call : syn::Expr,
    pfinder_call : syn::Expr,
}

impl TryMethod {
    pub fn as_try_some(self, mut fun : syn::ItemFn) -> syn::ItemFn {
        fun.attrs.clear();
        let pub_vis : syn::Visibility = parse_quote!(pub);
        fun.vis = pub_vis;
        let base_fun_ident = fun.sig.ident.clone();
        let try_fun_ident = format_ident!("try_{}", base_fun_ident);
        fun.sig.ident = try_fun_ident;       

        let tc_call = self.tc_call;
        let pfinder_call = self.pfinder_call;

        let try_block : syn::Block = parse_quote!(
            {
                let mut pfinder = tc.as_pfinder();
                let result = #pfinder_call;

                if result.is_some() {
                    let result = #tc_call;
                    assert!(result.is_some());
                    result
                } else {
                    None
                }
            }
        );

        fun.block = Box::new(try_block);
        fun       
    }

    pub fn as_try_bool(self, mut fun : syn::ItemFn) -> syn::ItemFn {
        fun.attrs.clear();
        let pub_vis : syn::Visibility = parse_quote!(pub);
        fun.vis = pub_vis;
        let base_fun_ident = fun.sig.ident.clone();
        let try_fun_ident = format_ident!("try_{}", base_fun_ident);
        fun.sig.ident = try_fun_ident;       

        let tc_call = self.tc_call;
        let pfinder_call = self.pfinder_call;

        let try_block : syn::Block = parse_quote!(
            {
                let mut pfinder = tc.as_pfinder();
                let result = #pfinder_call;

                match result {
                    (false, _) => result,
                    (true, _) => {
                        let eq_result = #tc_call;
                        assert!(eq_result.0);
                        eq_result
                    }
                }
            }
        );

        fun.block = Box::new(try_block);
        fun       

    }

    pub fn as_try_eq(self, mut fun : syn::ItemFn) -> syn::ItemFn {
        fun.attrs.clear();
        let pub_vis : syn::Visibility = parse_quote!(pub);
        fun.vis = pub_vis;
        let base_fun_ident = fun.sig.ident.clone();
        let try_fun_ident = format_ident!("try_{}", base_fun_ident);
        fun.sig.ident = try_fun_ident;       

        let tc_call = self.tc_call;
        let pfinder_call = self.pfinder_call;

        let try_block : syn::Block = parse_quote!(
            {
                let mut pfinder = tc.as_pfinder();
                let result = #pfinder_call;

                match result {
                    (crate::tc::eq::EqResult::NeShort, _) => result,
                    (crate::tc::eq::EqResult::EqShort, _) => {
                        let eq_result = #tc_call;
                        assert_eq!(eq_result.0, crate::tc::eq::EqResult::EqShort);
                        eq_result
                    }
                }
            }
        );

        fun.block = Box::new(try_block);
        fun       

    }


}


fn mk_pfinder_call(parsed_call : &syn::Expr) -> syn::Expr {
    let target_tc_arg : syn::Expr = parse_quote!(tc);
    let pfinder_arg : syn::Expr = parse_quote!(&mut pfinder);       

    let mut pfinder_call = parsed_call.clone();
    let pfinder_call_args = match &mut pfinder_call {
        | syn::Expr::Call(syn::ExprCall { ref mut args, .. })
        | syn::Expr::MethodCall(syn::ExprMethodCall { ref mut args, .. }) => args,
        _ => panic!(
            "has_try_X macro must receive either a syn::Expr::Call, or \
            syn::Expr::MethodCall item as its string lit."
        )
    };

    match pfinder_call_args.last_mut() {
        None => panic!("call to typechecker must have at least one argument"),
        Some(last_arg) => {
            assert_eq!(std::mem::replace(last_arg, pfinder_arg), target_tc_arg);
            let try_tok : syn::Expr = parse_quote!(crate::utils::TryToken);
            pfinder_call_args.push(try_tok);
        }
    }

    pfinder_call
}

// Parse the top level #[is_step(..)] key value pairs.
// Includes the step's tag, the return type, and the name of the trace formatting
// function to be used from the `IsTracer` trait.
impl Parse for TryMethod {
    fn parse(input : ParseStream) -> ParseResult<TryMethod> {
        // not modified until after we make pfinder_call
        let mut parsed = match syn::MetaNameValue::parse(input) {
            Ok(syn::MetaNameValue { lit : syn::Lit::Str(lit_str), .. }) => {
                match lit_str.parse::<syn::Expr>() {
                    Ok(method_call) => method_call,
                    Err(e) => panic!("Failed to parse method call from str lit : {}\n", e),
                }
            },
            Err(e) => panic!("Failed to parse Trace Attribute as #[trace(trace_loc, step)]. Error : {}", e),
            _ => panic!("Failed to parse string lit in method call parser"),
        };        

        let pfinder_call = mk_pfinder_call(&parsed);
        let try_tok : syn::Expr = parse_quote!(crate::utils::TryToken);
        match &mut parsed {
            syn::Expr::Call(syn::ExprCall { ref mut args, .. }) => {
                args.push(try_tok);
            },
            syn::Expr::MethodCall(syn::ExprMethodCall { ref mut args, .. }) => {
                args.push(try_tok)
            },
            _ => panic!(
               "has_try_X macro must receive either a syn::Expr::Call, or \
               syn::Expr::MethodCall item as its string lit."
            )           
        }

        Ok(TryMethod { tc_call : parsed, pfinder_call })

    }
}

