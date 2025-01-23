extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Fields, Ident, ItemEnum};

#[proc_macro_derive(NumVariants)]
pub fn num_variants_derive(input: TokenStream) -> TokenStream {
    let enum_ = parse_macro_input!(input as ItemEnum);
    let num_variants = enum_.variants.len();
    let ident = enum_.ident;

    quote! {
        impl #ident {
            pub const VARIANT_COUNT: usize = #num_variants;
        }
    }
    .into()
}

#[proc_macro_derive(EnumKind, attributes(enum_kind))]
pub fn enumkind_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let enum_ = syn::parse_macro_input!(input as ItemEnum);

    let enum_ident = enum_.ident;
    if enum_.attrs.is_empty() {
        panic!("Expected #[enum_kind] attribute");
    }
    let meta = &enum_.attrs.iter().find(|meta| meta.meta.path().is_ident("enum_kind")).unwrap();
    let new_name = meta.meta.require_list().unwrap();
    let new_ident: Ident = new_name.parse_args().unwrap();

    let vis = enum_.vis;
    let mut new_variants = quote! {};
    let mut from_branches = quote! {};
    for variant in enum_.variants {
        let ident = variant.ident;
        new_variants.extend(quote! { #ident,});
        let extend = match variant.fields {
            Fields::Unit => quote! { #enum_ident::#ident => #new_ident::#ident, },
            Fields::Unnamed(_) => quote! { #enum_ident::#ident(..) => #new_ident::#ident, },
            Fields::Named(_) => quote! { #enum_ident::#ident { .. } => #new_ident::#ident, },
        };
        from_branches.extend(extend);
    }

    quote! {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        #vis enum #new_ident {
            #new_variants
        }

        impl From<#enum_ident> for #new_ident {
            fn from(from: #enum_ident) -> #new_ident {
                match from {
                    #from_branches
                }
            }
        }
    }
    .into()
}
