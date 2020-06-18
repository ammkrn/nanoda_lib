#![allow(unused_parens)]

extern crate proc_macro;

use std::collections::HashMap;
use std::sync::{ Arc, Mutex };
use proc_macro::TokenStream;
use once_cell::sync::Lazy;

static USED_IDS : Lazy<Arc<Mutex<HashMap<String, String>>>> = Lazy::new(|| {
    Arc::new(Mutex::new(HashMap::new()))
});

use quote::{ quote, format_ident };
use syn::{ 
    parse_macro_input, 
    parse_quote, 
    parse::Parse,
    parse::ParseStream,
    parse::Result as ParseResult,
    Ident,
    ItemEnum,
    Expr,
    Variant,
    punctuated::Punctuated,
    token::Comma,
    token::Semi,
};

struct StepKv {
    step_tag : String,
    result_type : Option<syn::Type>,
    fun_name : syn::Ident,
}

impl StepKv {

    fn new(
        step_tag : String,
        result_type : Option<syn::Type>,
        fun_name : syn::Ident,
    ) -> Self {
        StepKv {
            step_tag,
            result_type,
            fun_name,
        }
    }



}

fn mk_tag_str_fun(
    tag_string : &String,
    enum_ident : &syn::Ident, 
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics
) -> syn::ItemImpl {

    match USED_IDS.lock() {
        Ok(mut guard) => {
            match guard.get(tag_string) {
                Some(overloaded_enum_string) =>  {
                    panic!(
                        "Step identifier {} was found to be overloaded.
                        When assigning it to step {}, it was also assigned \
                        to {}", tag_string, enum_ident.to_string(), overloaded_enum_string
                    );

                },
                None => { guard.insert(tag_string.clone(), enum_ident.to_string()); }
            }
        }
        Err(e) => {
            panic!(
                "Failed to get mutex guard (used to ensure step IDs are not \
                overloaded. Error : {}", e
            );
        }
    }


    let impl_block = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            fn tag(&self) -> &'static str {
                #tag_string
            }
        }
    };
    impl_block
}


// Parse the top level #[is_step(..)] key value pairs.
// Includes the step's tag, the return type, and the name of the trace formatting
// function to be used from the `IsTracer` trait.
impl Parse for StepKv {
    fn parse(input : ParseStream) -> ParseResult<StepKv> {
        let parsed = match Punctuated::<syn::MetaNameValue, Comma>::parse_terminated(input) {
            Ok(p) => p.into_iter(),
            Err(e) => panic!("Failed to parse Trace Attribute as #[trace(trace_loc, step)]. Error : {}", e)
        };        

        let mut step_tag : Option<String> = None;
        let mut result_type : Option<syn::Type> = None;
        let mut fun_ident : Option<syn::Ident> = None;




        let tag_key : syn::Path = parse_quote!(tag);
        let result_type_key : syn::Path = parse_quote!(result_type);
        let fun_key : syn::Path = parse_quote!(fun);

        for meta_kv in parsed {
            match meta_kv.path {
                p if p == tag_key => {
                    match meta_kv.lit {
                        syn::Lit::Str(lit_str) => {
                            step_tag = Some(lit_str.value());
                        },
                        _ => unreachable!("tag key had a non string value")
                    }
                },
                p if p == result_type_key => {
                    match meta_kv.lit {
                        syn::Lit::Str(lit_str) => {
                            let parsed_type = lit_str.parse::<syn::Type>()?;
                            result_type = Some(parsed_type);
                        },
                        _ => unreachable!("result_type needs a string lit value")
                    }
                },
                p if p == fun_key => {
                    match meta_kv.lit {
                        syn::Lit::Str(lit_str) => {
                            let parsed_ident = lit_str.parse::<syn::Ident>()?;
                            fun_ident = Some(parsed_ident);
                        },
                        _ => unreachable!("fun key needs a string list value")
                    }
                }
                owise => unimplemented!("bad meta kv key value. Expected 'tag' and 'result_type', got : {:#?}\n", owise)
            }
        }

        let step_tag = step_tag.expect("Failed to get step tag from macro attribute");
        //let result_type = result_type.expect("Failed to get result type from macro attribute");
        let fun_ident = fun_ident.expect("Failed to get fun ident from macro attribute");

        Ok(StepKv::new(step_tag, result_type, fun_ident))
    }
}





fn mk_get_result_fun(
    variants : &mut Punctuated<Variant, Comma>,
    enum_ident : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
) -> syn::ItemImpl {

    // Collect match arm expressions of enum match path |-> result field ident
    // WhnfCore::Lambda |-> `ind_arg3`
    let mut sink = HashMap::<Expr, syn::Ident>::new();
    let target_attr_path : syn::Path = parse_quote!(result);
    let mut result_type : Option<syn::Type> = None;


    for variant in variants.iter_mut() {
        // Enum variant's ident; IE `WhnfLambda`
        let ident = variant.ident.clone();

    
        // IE `WhnfCore::WhnfLambda`
        let match_path : syn::Path = parse_quote!(#enum_ident::#ident);
    
        // match_path as an expression; needed to make the match arm
        //, so we have `WhnfCore::Lambda` : Expr
        let variant_match_expr : Expr = parse_quote!(#match_path);


        match &mut variant.fields {
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => {
                let mut result_field_name : Option<Ident> = None;
                for field in named.iter_mut() {
                    if field.attrs.len() > 1 {
                        panic!("step enum fields can only have at most 1 attr (the result attr)")
                    }
                    for attr in &field.attrs {
                        if &attr.path == &target_attr_path {
                            match result_field_name.is_none() {
                                false => panic!("Only one step enum field can have the `#[result]` attribute"),
                                true => match &field.ident {
                                    None => panic!("Step enums must have named fields. {} didn't", ident.to_string()),
                                    Some(ident) => {
                                        result_field_name = Some(ident.clone());
                                        result_type = Some(field.ty.clone());
                                    }
                                }
                            }
                        }
                    }

                    std::mem::replace(&mut field.attrs, Vec::new());
                }

                // ensure that we actually got one.
                match (result_field_name, &result_type) {
                    (Some(ref ident), _) => { sink.insert(variant_match_expr, ident.clone()); },
                    _ => panic!("All step enum variants must tag one field with the `#[result]` attribute. \
                                    Steps with no explicit result should have a `result : ()` field tagged."),
                }
            },
            _ => panic!("Steps must be enums with named fields! {} was not", ident.to_string()),
        }
        
    }

    // Clear the remaining attributes.

    let to_match_arm = |variant_pat, result_field_name| {
        let inner : syn::Arm = parse_quote! {
            #variant_pat { #result_field_name, .. } => {
                *(#result_field_name)
            }
        };
        inner
    };

    let mut match_arms = Punctuated::<syn::Arm, Comma>::new();

    for (match_lhs, result_field_ident) in sink {
        match_arms.push(to_match_arm(match_lhs, result_field_ident));
    }



    let result_type_unwrapped = result_type.expect(
        "is_step macro couldn't figure out what the result type \
        of the step is supposed to be (it couldn't find one. \
        use the `#[result]` minor attribute to tag one field of each variant)");


    let item_impl : syn::ItemImpl = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            pub fn get_result(&self) -> #result_type_unwrapped {
                match self {
                    #match_arms
                }
            }
        }
    };

    item_impl
}

// Collect the constructor tag minor attributes
// and the result minor attributes
fn collect_minor_attrs(
    variants : &mut Punctuated<Variant,Comma>,
    enum_ident : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
) -> syn::ItemImpl {
    // Collect match arm expressions something like
    // WhnfCore::Lambda |-> "WL"
    let mut sink = HashMap::<Box<Expr>, String>::new();

    for variant in variants.iter() {
        if variant.attrs.len() != 1 {
            panic!("All Step enum variants must exactly one minor attribute \
                    specifying their trace representation. (like #[NIL]). \
                    Variant {} had {} minor attributes"
                    , variant.ident.to_string(), variant.attrs.len());
        }

        // Enum variant's ident; IE `WhnfLambda`
        let ident = variant.ident.clone();

        // IE `WhnfCore::WhnfLambda`
        let match_path : syn::Path = parse_quote!(#enum_ident::#ident);

        // match_path as an expression; needed to make the match arm
        let variant_match_expr : Expr = parse_quote!(#match_path);


        // Short tag variant; the Q in #[Q]
        let first_attr = variant.attrs.first().cloned().expect("Failed to get checked first attr");

        // Attribute struct has more fields we need to get through to get to the string repr.
        // of the minor tag.
        let path = first_attr.path;
        let minor_ident = path.get_ident().expect("Failed to get minor path ident");
        let minor_string = minor_ident.to_string();

        sink.insert(Box::new(variant_match_expr), minor_string);
    }


    for variant in variants.iter_mut() {
        variant.attrs.clear();
    }

    // (Box<Expr>, String) -> Arm
    let to_match_arm = |match_pat, string_val| {
        let arm : syn::Arm = parse_quote! {
            #match_pat {..} => {
                #string_val
            }
        };
        arm
    };

    let match_arms = sink.into_iter().map(|(k, v)| to_match_arm(k, v));
    //let arm_iter = match_arms.into_iter();

    let impl_block = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            fn ctor_tag(&self) -> &'static str {
                match self {
                    #(#match_arms)*
                }
            }
        }

    };


    impl_block
}

#[derive(Debug)]
struct VariantInfo {
    var_ident : syn::Ident,
    full_ident : syn::Path,
    ctor_name : String,
    num_fields : usize,
    field_info : Vec<(syn::Ident, syn::Type)>,
    match_lhs : Expr,
}

impl VariantInfo {
    pub fn new(v : &syn::Variant, enum_ident : &syn::Ident) -> Self {
        let var_ident = v.ident.clone();
        let match_lhs : syn::Expr = parse_quote!(#enum_ident::#var_ident);
        let num_fields = v.fields.len();
        let mut field_info = Vec::new();
        match &v.fields {
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => {
                for f in named.iter() {
                    field_info.push((f.ident.clone().expect("Need a named fields enum"), f.ty.clone()));
                }
            },
            _ => unreachable!("Need a named fields struct")
        }

        let full_ident : syn::Path = parse_quote!(#enum_ident::#var_ident);


        let mut ctor_name = format!("mk_{}", var_ident.to_string());
        ctor_name.make_ascii_lowercase();
        VariantInfo {
            var_ident,
            full_ident,
            ctor_name,
            num_fields,
            field_info,
            match_lhs
        }
    }
}



fn mk_match_arm1(variant_info : &VariantInfo) -> syn::Arm {
    let full_path = &variant_info.full_ident;
    let sink_ident = format_ident!("sink__");
    let step_idx_ident = format_ident!("step_idx__");

    // We need to skip this here.
    let dot_expr : Expr = parse_quote! {
        #sink_ident.push('.')
    };

    // These are just for creaing the pattern match
    // arm { .. } part
    let mut field_idents = Punctuated::<Ident, Comma>::new();
    for (ident, _) in variant_info.field_info.iter() {
        field_idents.push(ident.clone());
    }


    
    // Now we make the string push statements, excluding `step_idx`
    let idents_vec = variant_info.field_info.clone();

    let mut push_stmts = Punctuated::<Expr, Semi>::new();
    for ident in idents_vec.into_iter().map(|tup| tup.0) {
        push_stmts.push(dot_expr.clone());
        let this_expr : Expr = parse_quote! {
            #sink_ident.push_str(#ident.ptr_repr().as_str())
        };
        push_stmts.push(this_expr);
    }
    
    // step_idx is in the enclosing scope where we're going to quote this.
    let arm : syn::Arm = parse_quote! {
        #full_path { #field_idents } => {
            let mut #sink_ident = format!("{}", #step_idx_ident.ptr_repr());
            #sink_ident.push('.');
            #sink_ident.push_str(self.tag());
            #sink_ident.push('.');
            #sink_ident.push_str(self.ctor_tag());            
            {
            #push_stmts
            }
            #sink_ident
        }
    };    

    arm
}

fn mk_match_arms(variant_infos : &Vec<VariantInfo>) -> Punctuated<syn::Arm, Comma> {
    let mut sink = Punctuated::<syn::Arm, Comma>::new();
    for variant_info in variant_infos.iter() {
        sink.push(mk_match_arm1(variant_info));
    }

    sink
}

fn mk_default_trace(
    parsed_enum : &syn::ItemEnum, 
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
    has_lifetime : bool,
) -> syn::ItemImpl {
    let enum_ident = parsed_enum.ident.clone();
    let variant_infos = parsed_enum.variants.iter().map(|v| VariantInfo::new(v, &parsed_enum.ident)).collect::<Vec<VariantInfo>>();
    let match_arms = mk_match_arms(&variant_infos);


    let generics : syn::Generics = match has_lifetime {
        false => {
            let g : syn::Generics = parse_quote!(<'a, CTX : IsCtx<'a>>);
            g
        },
        true => {
            let g : syn::Generics = parse_quote!(<CTX : IsCtx<'a>>);
            g
        }
    };


    let step_idx_ident = format_ident!("step_idx__");
    let trace_repr_string_ident = format_ident!("trace_repr_string__");
    let fn_impl : syn::ItemImpl = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            //pub fn default_trace_repr<CTX : IsCtx<'a>>(self, ctx : &mut CTX) -> (StepIdx, String) {
            pub fn default_trace_repr#generics(self, ctx : &mut CTX) -> (StepIdx, String) {
                let #step_idx_ident = ctx.mut_mgr().next_step_idx();
                let #trace_repr_string_ident = match self {
                    #match_arms
                };
                (#step_idx_ident, #trace_repr_string_ident)
            }
        }
    };

    fn_impl
}

// need a minor attribute that creates a function `get_result()` for 
// each enum variant.
//fn mk_step_fun(
//    
//    parsed_enum : &syn::ItemEnum, 
//    // IE ExprPtr<'a>
//    return_type : Option<&syn::Type>,
//    // IE `trace_combining()`
//    trace_fun_name : &syn::Ident,
//    enum_generics : &syn::Generics,
//    nobound_generics : &syn::Generics,
//    has_lifetime : bool,
//) -> syn::ItemImpl {
//    match return_type {
//        None => mk_step_fun_no_result(
//            parsed_enum,
//            trace_fun_name,
//            enum_generics,
//            nobound_generics,
//            has_lifetime
//        ),
//        Some(return_type) => mk_step_fun_with_result(
//            parsed_enum,
//            return_type,
//            trace_fun_name,
//            enum_generics,
//            nobound_generics,
//            has_lifetime
//        )
//    }
//}

fn mk_step_fun_no_result(
    parsed_enum : &syn::ItemEnum, 
    trace_fun_name : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
    has_lifetime : bool,
) -> syn::ItemImpl {
    let enum_ident = parsed_enum.ident.clone();

    let generics : syn::Generics = match has_lifetime {
        false => {
            let g : syn::Generics = parse_quote!(<'a, CTX : IsCtx<'a>>);
            g
        },
        true => {
            let g : syn::Generics = parse_quote!(<CTX : IsCtx<'a>>);
            g
        }
    };

    let step_idx_ident = format_ident!("step_idx__");
    let item_impl : syn::ItemImpl = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            pub fn step_only#generics(self, ctx : &mut CTX) -> Step<Self> {
                if (<CTX as IsCtx>::IS_PFINDER || <CTX as IsCtx>::Tracer::NOOP) {
                    Step::new_pfind()
                } else {
                    // the trace function returns the step_idx since that :
                    // 1. Prevents us from needing to coordinate two copies, (which would
                    //    be the case since it needs to be used in two distinct locations
                    // 2. Allows for users to decide how/when it's going to be set
                    //    since the location we're setting it now is an overridable
                    //    default trait method.
                    let #step_idx_ident = <CTX as IsCtx>::Tracer::#trace_fun_name(self, ctx);
                    Step::new_live(#step_idx_ident)
                }
            }
        }
    };

    item_impl
}


fn mk_step_fun_with_result(
    parsed_enum : &syn::ItemEnum, 
    // IE ExprPtr<'a>
    return_type : &syn::Type,
    // IE `trace_combining()`
    trace_fun_name : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
    has_lifetime : bool,
) -> syn::ItemImpl {
    let enum_ident = parsed_enum.ident.clone();
    
    // IE (LevelPtr<'a>, Step<Combining<'a>>);
    //let result_type : syn::Type = parse_quote!((#return_type, Step<Self>));
    //let variant_infos = parsed_enum.variants.iter().map(|v| VariantInfo::new(v, &parsed_enum.ident)).collect::<Vec<VariantInfo>>();

    //let ctor_arg_sets = create_ctor_args(&variant_infos);
    //let comma_sep_field_idents = create_field_name_commas(&variant_infos);

    let generics : syn::Generics = match has_lifetime {
        false => {
            let g : syn::Generics = parse_quote!(<'a, CTX : IsCtx<'a>>);
            g
        },
        true => {
            let g : syn::Generics = parse_quote!(<CTX : IsCtx<'a>>);
            g
        }
    };

    let step_idx_ident = format_ident!("step_idx__");
    let item_impl : syn::ItemImpl = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            pub fn step#generics(self, ctx : &mut CTX) -> (#return_type, Step<Self>) {
                if (<CTX as IsCtx>::IS_PFINDER || <CTX as IsCtx>::Tracer::NOOP) {
                    (self.get_result(), Step::new_pfind())
                } else {
                    // the trace function returns the step_idx since that :
                    // 1. Prevents us from needing to coordinate two copies, (which would
                    //    be the case since it needs to be used in two distinct locations
                    // 2. Allows for users to decide how/when it's going to be set
                    //    since the location we're setting it now is an overridable
                    //    default trait method.
                    let #step_idx_ident = <CTX as IsCtx>::Tracer::#trace_fun_name(self, ctx);
                    (self.get_result(), Step::new_live(#step_idx_ident))
                }
            }
        }
    };

    item_impl
}


fn remove_generic_bounds(mut g : syn::Generics) -> syn::Generics {
    for elem in g.params.iter_mut() {
        match elem {
            syn::GenericParam::Type(type_param) => {
                type_param.colon_token = None;
                type_param.bounds.clear();
                type_param.eq_token = None;
                type_param.default = None;
            },
            _ => continue
        }
    }
    g
}

fn has_lifetime(item_enum : &syn::ItemEnum) -> bool {
    item_enum
    .generics
    .params
    .iter()
    .any(|generic_param| {
        match generic_param {
            syn::GenericParam::Lifetime(..) => true,
            _ => false,
        }
    })
}



#[proc_macro_attribute]
pub fn is_step(attr : TokenStream, input : TokenStream) -> TokenStream {
    // gives the step tag and the result type

    // Parse the enum's general tag, and return type.
    let parsed_kvs = parse_macro_input!(attr as StepKv);

    match parsed_kvs.result_type {
        Some(result_type) => handle_macro_with_return(
            parsed_kvs.step_tag, 
            result_type, 
            parsed_kvs.fun_name,
            input
        ),
        None => handle_macro_no_return(
            parsed_kvs.step_tag, 
            parsed_kvs.fun_name,
            input
        )
    }



}

fn handle_macro_with_return(
    step_tag : String,
    result_type : syn::Type,
    fun_name : syn::Ident,
    input : TokenStream,
) -> TokenStream {
    
    let mut parsed_enum = parse_macro_input!(input as ItemEnum);
    let nobound_generics = remove_generic_bounds(parsed_enum.generics.clone());
    let has_lifetime = has_lifetime(&parsed_enum);
    // assert that the stated result type and the actual one decorated match.
    let result_fun = mk_get_result_fun(
        &mut parsed_enum.variants,
        &parsed_enum.ident,
        &parsed_enum.generics,
        &nobound_generics,
    );

    // remove minor attributes and create function that returns the
    // constructor's string tag.
    let ctor_tag_impl_block = collect_minor_attrs(
        &mut parsed_enum.variants, 
        &parsed_enum.ident,
        &parsed_enum.generics,
        &nobound_generics

    );


    // make the function that returns the enum tag as a string.
    let tag_str_impl = mk_tag_str_fun(
        &step_tag,
        &parsed_enum.ident, 
        &parsed_enum.generics,
        &nobound_generics
    );

    let default_trace = mk_default_trace(
        &parsed_enum,
        &parsed_enum.generics,
        &nobound_generics,
        has_lifetime,
    );

    let step_fun = mk_step_fun_with_result(
        &parsed_enum, 
        &result_type,
        &fun_name,
        &parsed_enum.generics,
        &nobound_generics,
        has_lifetime
    );

    TokenStream::from(quote! {
        #parsed_enum
        #result_fun
        #tag_str_impl
        #ctor_tag_impl_block
        #step_fun
        #default_trace
    })
}

fn handle_macro_no_return(
    step_tag : String,
    fun_name : syn::Ident,
    input : TokenStream,
) -> TokenStream {

    let mut parsed_enum = parse_macro_input!(input as ItemEnum);
    let nobound_generics = remove_generic_bounds(parsed_enum.generics.clone());
    let has_lifetime = has_lifetime(&parsed_enum);

    // assert that the stated result type and the actual one decorated match.

    // remove minor attributes and create function that returns the
    // constructor's string tag.
    let ctor_tag_impl_block = collect_minor_attrs(
        &mut parsed_enum.variants, 
        &parsed_enum.ident,
        &parsed_enum.generics,
        &nobound_generics
    );


    // make the function that returns the enum tag as a string.
    let tag_str_impl = mk_tag_str_fun(
        &step_tag,
        &parsed_enum.ident, 
        &parsed_enum.generics,
        &nobound_generics
    );

    let default_trace = mk_default_trace(
        &parsed_enum,
        &parsed_enum.generics,
        &nobound_generics,
        has_lifetime,
    );

    let step_fun = mk_step_fun_no_result(
        &parsed_enum, 
        &fun_name,
        &parsed_enum.generics,
        &nobound_generics,
        has_lifetime
    );

    TokenStream::from(quote! {
        #parsed_enum
        #tag_str_impl
        #ctor_tag_impl_block
        #step_fun
        #default_trace
    })    

}

struct TryMethod {
    method_call : syn::ExprMethodCall
}

impl TryMethod {
}

// Parse the top level #[is_step(..)] key value pairs.
// Includes the step's tag, the return type, and the name of the trace formatting
// function to be used from the `IsTracer` trait.
impl Parse for TryMethod {
    fn parse(input : ParseStream) -> ParseResult<TryMethod> {
        let parsed = match syn::MetaNameValue::parse(input) {
            Ok(syn::MetaNameValue { lit : syn::Lit::Str(lit_str), .. }) => {
                match lit_str.parse::<syn::ExprMethodCall>() {
                    Ok(method_call) => method_call,
                    Err(e) => panic!("Failed to parse method call from str lit : {}\n", e),
                }
            },
            Err(e) => panic!("Failed to parse Trace Attribute as #[trace(trace_loc, step)]. Error : {}", e),
            _ => panic!("Failed to parse string lit in method call parser"),
        };        

        Ok(TryMethod { method_call : parsed })

    }
}

fn mk_try_fun(mut fun : syn::ItemFn, method_call : syn::ExprMethodCall) -> syn::ItemFn {
    fun.attrs.clear();
    fun.vis = syn::Visibility::Inherited;
    let base_fun_ident = fun.sig.ident.clone();
    let try_fun_ident = format_ident!("try_{}", base_fun_ident);
    fun.sig.ident = try_fun_ident;

    let target_tc_arg : syn::Expr = parse_quote!(tc);
    let pfinder_arg : syn::Expr = parse_quote!(&mut pfinder);
    let pfinder_method_call = {
        let mut pfinder_method_call = method_call.clone();
        let tc_arg = pfinder_method_call.args.last_mut().expect(
            "Failed to get last arg of try method call"
        );
        assert_eq!(&target_tc_arg, tc_arg);
        std::mem::replace(tc_arg, pfinder_arg);
        pfinder_method_call
    };

    let try_block : syn::Block = parse_quote!(
        {
            let mut pfinder = tc.as_pfinder();
            let maybe_result = #pfinder_method_call;

            if maybe_result.is_some() {
                let result = #method_call;
                assert!(result.is_some());
                result
            } else {
                pfinder.restore_snapshot();
                None
            }
        }
    );

    fun.block = Box::new(try_block);
    fun
}

#[proc_macro_attribute]
pub fn has_try(attr : TokenStream, input : TokenStream) -> TokenStream {
    let try_method = parse_macro_input!(attr as TryMethod);
    let base_fun = parse_macro_input!(input as syn::ItemFn);
    let try_fun = mk_try_fun(base_fun.clone(), try_method.method_call);

    TokenStream::from(quote! {
        #base_fun
        #try_fun
    })
}