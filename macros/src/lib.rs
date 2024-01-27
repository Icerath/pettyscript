use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn pettyfunc(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::ItemFn);
    let syn::ReturnType::Type(_, return_type) = &input.sig.output else {
        panic!();
    };

    let variables = downcast_args(&input.sig);
    let (body, name, vis) = (input.block, input.sig.ident, input.vis);

    quote::quote!(
        #vis fn #name <'__a> (
            args: crate::prelude::FnArgs<'__a>
        ) -> crate::prelude::PettyObject {
            #variables
            #return_type::into(#body)
        }
    )
    .into()
}

fn downcast_args(sig: &syn::Signature) -> proc_macro2::TokenStream {
    sig.inputs
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            let syn::FnArg::Typed(arg) = arg else {
                panic!()
            };
            let (name, typ) = (&arg.pat, &arg.ty);

            quote::quote!(
                let PettyObject::#typ(#name) = &args.slice[#index] else {
                    unimplemented!();
                };
            )
        })
        .collect()
}
