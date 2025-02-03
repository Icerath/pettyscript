extern crate proc_macro;

use std::path::Path;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_macro_input, spanned::Spanned, Fields, Ident, ItemEnum};

#[proc_macro]
pub fn generate_integration_tests(input: TokenStream) -> TokenStream {
    assert!(input.is_empty());
    let mut tests = quote! {};
    for dir_entry in std::fs::read_dir("tests").unwrap() {
        let entry = dir_entry.unwrap();
        let src = Path::new("..").join(entry.path()).display().to_string();
        let test_name =
            Ident::new(&entry.path().file_stem().unwrap().to_str().unwrap(), Span::call_site());
        tests.extend(quote! {
            #[test]
            fn #test_name () {
                let src = include_str!(#src);
                let ast = parse(&src).unwrap();
                let ast = Ast { src: src, body: &ast };
                let code = codegen::codegen(ast).unwrap();
                exec_vm(&code);
            }
        });
    }
    tests.into()
}

#[proc_macro_derive(BcWrite)]
pub fn bc_write_derive(input: TokenStream) -> TokenStream {
    let enum_ = parse_macro_input!(input as ItemEnum);
    let ident = enum_.ident;

    let mut match_stmt = quote! {};
    for variant in enum_.variants {
        let variant_ident = variant.ident;

        let branch = match variant.fields {
            Fields::Unit => quote! { Op::#variant_ident => {} },
            Fields::Named(fields) => {
                let mut body = quote! {};
                let mut branch = quote! {};

                for field in fields.named {
                    let ident = field.ident;
                    branch.extend(quote! { #ident , });
                    body.extend(quote! { #ident.bc_write(&mut buf); });
                }
                quote! { Op::#variant_ident  { #branch } => { #body } }
            }
            Fields::Unnamed(fields) => {
                let mut body = quote! {};
                let mut branch = quote! {};

                for (i, field) in fields.unnamed.iter().enumerate() {
                    let ident = Ident::new(&format!("_{i}"), field.span());
                    branch.extend(quote! { #ident , });
                    body.extend(quote! { #ident.bc_write(&mut buf); });
                }
                quote! { Op::#variant_ident ( #branch ) => { # body } }
            }
        };
        match_stmt.extend(branch);
    }

    quote! {
        impl #ident {
            pub fn bc_write(&self, mut buf: &mut Vec<u8>) {
                match self {
                    #match_stmt
                }
            }
        }
    }
    .into()
}

#[proc_macro_derive(BcRead)]
pub fn bc_read_derive(input: TokenStream) -> TokenStream {
    let enum_ = parse_macro_input!(input as ItemEnum);
    let ident = enum_.ident;

    let mut match_stmt_unchecked = quote! {};
    let mut match_stmt = quote! {};
    let mut size_impl = quote! {};
    for variant in enum_.variants {
        let variant_ident = variant.ident;

        let mut body = quote! {};
        let mut body_unchecked = quote! {};
        let mut size = quote! { 0 };
        let branch;
        let branch_unchecked;
        match variant.fields {
            Fields::Unit => {
                branch = quote! { OpCode::#variant_ident => Self::#variant_ident, };
                branch_unchecked = branch.clone();
            }
            Fields::Named(fields) => {
                for field in fields.named {
                    let ident = field.ident;
                    let ty = field.ty;
                    body.extend(quote! { #ident : #ty::bc_read(&mut bytes), });
                    body_unchecked.extend(quote! { #ident : #ty::bc_read_unchecked(&mut bytes), });
                    size.extend(quote! { + size_of::<#ty>() });
                }
                branch = quote! { OpCode::#variant_ident => Self::#variant_ident { #body }, };
                branch_unchecked =
                    quote! { OpCode::#variant_ident => Self::#variant_ident { #body_unchecked }, };
            }
            Fields::Unnamed(fields) => {
                for field in fields.unnamed {
                    let ty = field.ty;
                    body.extend(quote! { #ty::bc_read(&mut bytes), });
                    body_unchecked.extend(quote! { #ty::bc_read_unchecked(&mut bytes), });
                    size.extend(quote! { + size_of::<#ty>() });
                }
                branch = quote! { OpCode::#variant_ident => Self::#variant_ident(#body), };
                branch_unchecked =
                    quote! { OpCode::#variant_ident => Self::#variant_ident(#body_unchecked), };
            }
        };
        size_impl.extend(quote! { OpCode::#variant_ident => #size, });
        match_stmt.extend(branch);
        match_stmt_unchecked.extend(branch_unchecked);
    }

    quote! {
        impl #ident {
            pub fn bc_read(mut bytes: &[u8]) -> Self {
                match OpCode::try_from(u8::bc_read(&mut bytes)).unwrap() {
                    #match_stmt
                }
            }
            pub fn bc_read_unchecked(mut bytes: &[u8]) -> Self {
                unsafe {
                    match OpCode::try_from(u8::bc_read_unchecked(&mut bytes)).unwrap_unchecked() {
                        #match_stmt_unchecked
                    }
                }
            }
            pub fn size(&self) -> usize {
                match OpCode::from(*self) {
                    #size_impl
                }
            }
        }
    }
    .into()
}

#[proc_macro_derive(AllVariants)]
pub fn all_variants_derive(input: TokenStream) -> TokenStream {
    let enum_ = parse_macro_input!(input as ItemEnum);
    let ident = enum_.ident;
    let variant_count = enum_.variants.len();

    let mut all_variants = quote! {};
    for variant in enum_.variants {
        let variant_ident = variant.ident;
        all_variants.extend(quote! { Self::#variant_ident, });
    }

    quote! {
        impl #ident {
            pub const ALL: [Self; #variant_count] = [#all_variants]; }
    }
    .into()
}

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

        impl From<&#enum_ident> for #new_ident {
            fn from(from: &#enum_ident) -> #new_ident {
                match from {
                    #from_branches
                }
            }
        }

        impl From<#enum_ident> for #new_ident {
            fn from(from: #enum_ident) -> #new_ident {
                Self::from(&from)
            }
        }
    }
    .into()
}
