use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

#[proc_macro_attribute]
pub fn pettyfunc(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input_func = syn::parse_macro_input!(input as syn::ItemFn);
    let (variables, args) = downcast_args(&input_func.sig);
    let name = &input_func.sig.ident;
    let vis = &input_func.vis;
    quote!(
        #vis fn #name <'__a> (
            args: crate::prelude::FnArgs<'__a>
        ) -> crate::prelude::PettyObject {
            #[inline]
            #input_func
            #variables
            #name ( #args ).into()
        }
    )
    .into()
}

fn downcast_args(sig: &syn::Signature) -> (TokenStream2, TokenStream2) {
    let mut out_args = TokenStream2::new();
    let mut variables = TokenStream2::new();
    for (arg_index, arg) in sig.inputs.iter().enumerate() {
        let syn::FnArg::Typed(arg) = arg else {
            panic!()
        };
        let (name, typ) = (&arg.pat, &arg.ty);

        variables.extend(quote!(
            let PettyObject::#typ(#name) = args.slice[#arg_index].clone() else {
                unimplemented!();
            };
        ));
        out_args.extend(quote!(#name,));
    }
    (variables, out_args)
}
