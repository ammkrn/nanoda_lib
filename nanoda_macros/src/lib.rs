#![allow(unused_parens)]

extern crate proc_macro;

use std::path::PathBuf;
use std::fs::{ File, OpenOptions };
use std::io::{ Write, BufWriter };
use std::collections::HashMap;
use std::sync::{ Arc, Mutex };
use proc_macro::TokenStream;
use once_cell::sync::Lazy;
use crate::has_try::TryMethod;

mod has_try;


static USED_IDS : Lazy<Arc<Mutex<HashMap<String, String>>>> = Lazy::new(|| {
    Arc::new(Mutex::new(HashMap::new()))
});

static STEP_GRAMMAR : Lazy<Option<Arc<Mutex<BufWriter<File>>>>> = Lazy::new(|| {
    let path = PathBuf::from("../nanoda_lib/step_grammar.txt");
    let handle = 
    OpenOptions::new()
    .create(true)
    .truncate(true)
    .write(true)
    .open(&path);

     match handle {
        Ok(f) => Some(Arc::new(Mutex::new(BufWriter::new(f)))),
        Err(e) => {
            eprintln!("Failed to open step grammar file {:#?}\n Err : {}", path, e);
            None
        }
    }  
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

                    field.attrs = Vec::new();
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
fn collect_ctor_attrs(
    variants : &mut Punctuated<Variant,Comma>,
    enum_ident : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
) -> (syn::ItemImpl, Vec<String>) {
    // Collect match arm expressions something like
    // WhnfCore::Lambda |-> "WL"
    let mut ctor_tag_strings = Vec::<String>::new();
    let mut sink = HashMap::<Box<Expr>, String>::new();

    for variant in variants.iter() {
        if variant.attrs.len() != 1 {
            panic!("All Step enum variants must exactly one minor attribute \
                    specifying their trace representation. (like #[NIL]). \
                    Variant {} had {} minor attributes"
                    , variant.ident.to_string(), variant.attrs.len());
        }

        // Enum variant's ident; IE `WhnfLambda`
        let ident = &variant.ident;

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
        ctor_tag_strings.push(minor_string.clone());

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

    (impl_block, ctor_tag_strings)
}

#[derive(Debug)]
struct VariantInfo {
    variant_ident : syn::Ident,
    full_ident : syn::Path,
    ctor_name : String,
    num_fields : usize,
    field_info : Vec<(syn::Ident, syn::Type)>,
    match_lhs : Expr,
}

impl VariantInfo {
    pub fn new(v : &syn::Variant, enum_ident : &syn::Ident) -> Self {
        let variant_ident = v.ident.clone();
        let match_lhs : syn::Expr = parse_quote!(#enum_ident::#variant_ident);
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

        let full_ident : syn::Path = parse_quote!(#enum_ident::#variant_ident);


        let mut ctor_name = format!("mk_{}", variant_ident.to_string());
        ctor_name.make_ascii_lowercase();
        VariantInfo {
            variant_ident,
            full_ident,
            ctor_name,
            num_fields,
            field_info,
            match_lhs
        }
    }
}

fn is_option(type_ : &syn::Type) -> bool {
    match type_ {
        syn::Type::Path(syn::TypePath { path, .. }) => {
            match path.segments.first() {
                Some(p) if p.ident.to_string() == String::from("Option") => true,
                _ => false,
            }
        },
        _ => false
    }
}

fn is_pair(type_ : &syn::Type) -> bool {
    match type_ {
        syn::Type::Tuple(..) => true,
        _ => false
    }
}

fn mk_match_arm1(variant_info : &VariantInfo) -> syn::Arm {
    let full_path = &variant_info.full_ident;
    let step_idx_ident = format_ident!("step_idx__");
    let step_tag_ident = format_ident!("step_tag__");
    let step_ctor_tag_ident = format_ident!("step_ctor_tag__");

    if variant_info.field_info.len() == 0 {
        panic!("zero fields enum can't be handled by current macro");
    }

    let mut string_lit = String::from("{}.{}.{}.");
    let prefixes : Punctuated::<Ident, Comma> = parse_quote! {
        #step_idx_ident,
        #step_tag_ident,
        #step_ctor_tag_ident,
    };

    // has the prefixes and field idents
    let mut field_idents = Punctuated::<syn::Ident, Comma>::new();
    let mut write_args = Punctuated::<syn::Expr, Comma>::new();

    for (ident, type_) in variant_info.field_info.iter() {
        string_lit.push_str("{}.");
        field_idents.push(ident.clone());
        let as_expr : syn::Expr = if is_option(type_) {
            parse_quote!(crate::trace::items::NewtypeOption(#ident))
        } else if is_pair(type_) {
            parse_quote!(crate::trace::items::NewtypeTuple(#ident))
        } else {
            parse_quote!(#ident)
        };

        write_args.push(as_expr);
    }


    assert!(string_lit.pop() == Some('.'));
    string_lit.push_str("\n");

    let arm : syn::Arm = parse_quote! {
        #full_path { #field_idents } => {
            let #step_idx_ident = ctx.mut_mgr().next_step_idx();
            let #step_tag_ident = self.tag();
            let #step_ctor_tag_ident = self.ctor_tag();
            let result = write!(
                ctx.tracer(),
                #string_lit,
                #prefixes
                #write_args
            );

            (#step_idx_ident, result)
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

    let fn_impl : syn::ItemImpl = parse_quote! {
        impl#enum_generics #enum_ident#nobound_generics {
            pub fn default_trace_repr#generics(self, ctx : &mut CTX) -> (StepIdx, std::io::Result<()>) {
                match self {
                    #match_arms
                } 
            }
        }
    };

    fn_impl
}

fn mk_step_fun_no_result(
    parsed_enum : &syn::ItemEnum, 
    trace_fun_name : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
    has_lifetime : bool,
    zst_ident : &syn::Ident,
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
            pub fn step_only#generics(self, ctx : &mut CTX) -> Step<#zst_ident> {
                if (<CTX as IsCtx>::IS_PFINDER) {
                    Step::new_pfind(ctx)
                } else if <CTX as IsCtx>::Tracer::NOOP {
                    Step::new_noop(ctx)
                } else {
                    // the trace function returns the step_idx since that :
                    // 1. Prevents us from needing to coordinate two copies, (which would
                    //    be the case since it needs to be used in two distinct locations
                    // 2. Allows for users to decide how/when it's going to be set
                    //    since the location we're setting it now is an overridable
                    //    default trait method.
                    let #step_idx_ident = <CTX as IsCtx>::Tracer::#trace_fun_name(self, ctx);
                    Step::new_live(#step_idx_ident, ctx)
                }
            }
        }
    };

    item_impl
}


fn mk_step_fun_with_result(
    parsed_enum : &syn::ItemEnum, 
    trace_fun_name : &syn::Ident,
    enum_generics : &syn::Generics,
    nobound_generics : &syn::Generics,
    has_lifetime : bool,
    zst_ident : &syn::Ident,
    return_type : &syn::Type,
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
            pub fn step#generics(self, ctx : &mut CTX) -> (#return_type, Step<#zst_ident>) {

                if (<CTX as IsCtx>::IS_PFINDER) {
                    (self.get_result(), Step::new_pfind(ctx))
                } else if <CTX as IsCtx>::Tracer::NOOP {
                    (self.get_result(), Step::new_noop(ctx))
                } else {
                    // the trace function returns the step_idx since that :
                    // 1. Prevents us from needing to coordinate two copies, (which would
                    //    be the case since it needs to be used in two distinct locations
                    // 2. Allows for users to decide how/when it's going to be set
                    //    since the location we're setting it now is an overridable
                    //    default trait method.
                    let #step_idx_ident = <CTX as IsCtx>::Tracer::#trace_fun_name(self, ctx);
                    (self.get_result(), Step::new_live(#step_idx_ident, ctx))
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

fn mk_grammar_additions(
    step_enum_ident : &Ident,
    step_tag : &String,
    variant_idents : Vec<Ident>,
    ctor_tag_strings : Vec<String>,
    nums_children : Vec<usize>,
) {
    
    match STEP_GRAMMAR.as_ref() {
        None => (),
        Some(mutex) => match mutex.lock() {
            Err(e) => eprintln!("Failed to get mutex contents in writing to step grammar : {}\n", e),
            Ok(ref mut guard) => {
                for ((ctor_tag, variant_ident), num_children) 
                in ctor_tag_strings.into_iter().zip(variant_idents).zip(nums_children) {
                    let write_result = match num_children {
                        0 => {
                            write!(
                                guard,
                                "{}{} ::= nat \'.\' {} \'.\' {}\n", 
                                step_enum_ident, 
                                variant_ident,
                                step_tag, 
                                ctor_tag
                            )
                        },
                        _ => {
                            write!(
                                guard,
                                "{}{} ::= nat \'.\' {} \'.\' {} \'.\' {{ {} * child }}\n", 
                                step_enum_ident, 
                                variant_ident,
                                step_tag, 
                                ctor_tag,
                                num_children
                            )
                        }
                    };

                    if let Err(e) = write_result {
                        eprintln!("Failed to write to step grammar : {}\n", e);
                    }

                }               

            }
        }
    }


}


#[proc_macro_attribute]
pub fn has_try_eq(attr : TokenStream, input : TokenStream) -> TokenStream {
    let try_method = parse_macro_input!(attr as TryMethod);
    // only mutated AFTER try_fun; we mutate by pushing `()` as an argument.
    let mut base_fun = parse_macro_input!(input as syn::ItemFn);
    let try_fun = try_method.as_try_eq(base_fun.clone());
    let try_tok : syn::FnArg = parse_quote!(_ : crate::utils::TryToken);
    base_fun.sig.inputs.push(try_tok);

    TokenStream::from(quote! {
        #base_fun
        #try_fun
    })
}

#[proc_macro_attribute]
pub fn has_try_bool(attr : TokenStream, input : TokenStream) -> TokenStream {
    let try_method = parse_macro_input!(attr as TryMethod);
    // only mutated AFTER try_fun; we mutate by pushing `()` as an argument.
    let mut base_fun = parse_macro_input!(input as syn::ItemFn);
    let try_fun = try_method.as_try_bool(base_fun.clone());
    let try_tok : syn::FnArg = parse_quote!(_ : crate::utils::TryToken);
    base_fun.sig.inputs.push(try_tok);

    TokenStream::from(quote! {
        #base_fun
        #try_fun
    })
}

#[proc_macro_attribute]
pub fn has_try_some(attr : TokenStream, input : TokenStream) -> TokenStream {
    let try_method = parse_macro_input!(attr as TryMethod);
    // only mutated AFTER try_fun; we mutate by pushing `()` as an argument.
    let mut base_fun = parse_macro_input!(input as syn::ItemFn);
    let try_fun = try_method.as_try_some(base_fun.clone());
    let try_tok : syn::FnArg = parse_quote!(_ : crate::utils::TryToken);
    base_fun.sig.inputs.push(try_tok);

    TokenStream::from(quote! {
        #base_fun
        #try_fun
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
    let zst_ident = format_ident!("{}Zst", parsed_enum.ident);
    let enum_zst : syn::ItemStruct = parse_quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct #zst_ident;

    };

    let enum_zst_default_impl : syn::ItemImpl = parse_quote! {
        impl Default for #zst_ident {
            fn default() -> Self {
                #zst_ident
            }
        }
    };

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
    let (ctor_tag_impl_block, step_ctor_strings) = collect_ctor_attrs(
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
        &fun_name,
        &parsed_enum.generics,
        &nobound_generics,
        has_lifetime,
        &zst_ident,
        &result_type,
    );

    mk_grammar_additions(
        &parsed_enum.ident, 
        &step_tag,
        parsed_enum.variants.iter().map(|v| v.ident.clone()).collect::<Vec<Ident>>(),
        step_ctor_strings, 
        parsed_enum.variants.iter().map(|v| v.fields.len()).collect::<Vec<usize>>()
    );

        


    TokenStream::from(quote! {
        #enum_zst
        #enum_zst_default_impl
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
    
    let zst_ident = format_ident!("{}Zst", parsed_enum.ident);
    let enum_zst : syn::ItemStruct = parse_quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct #zst_ident;
    };
    
    let enum_zst_default_impl : syn::ItemImpl = parse_quote! {
        impl Default for #zst_ident {
            fn default() -> Self {
                #zst_ident
            }
        }
    };

    let nobound_generics = remove_generic_bounds(parsed_enum.generics.clone());
    let has_lifetime = has_lifetime(&parsed_enum);

    // assert that the stated result type and the actual one decorated match.

    // remove minor attributes and create function that returns the
    // constructor's string tag.
    let (ctor_tag_impl_block, step_ctor_strings) = collect_ctor_attrs(
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
        has_lifetime,
        &zst_ident,
    );

    mk_grammar_additions(
        &parsed_enum.ident, 
        &step_tag,
        parsed_enum.variants.iter().map(|v| v.ident.clone()).collect::<Vec<Ident>>(),
        step_ctor_strings, 
        parsed_enum.variants.iter().map(|v| v.fields.len()).collect::<Vec<usize>>(),
    );

    TokenStream::from(quote! {
        #enum_zst
        #enum_zst_default_impl
        #parsed_enum
        #tag_str_impl
        #ctor_tag_impl_block
        #step_fun
        #default_trace
    })    

}



