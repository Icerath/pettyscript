use proc_macro::TokenStream;
use quote::quote;
use syn::Attribute;

#[proc_macro_attribute]
pub fn pettyfunc(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::ItemFn);
    let syn::ReturnType::Type(_, return_type) = &input.sig.output else {
        panic!();
    };

    let variables = downcast_args(&input.sig);
    let (vis, name, body) = (input.vis, input.sig.ident, input.block);

    quote!(
        #vis fn #name <'__a> (
            args: FnArgs<'__a>
        ) -> PettyObject {
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
            let syn::FnArg::Typed(arg) = arg else { panic!() };
            let (name, typ) = (&arg.pat, &arg.ty);

            let match_body = if is_option(&arg.attrs) {
                quote!({
                    Some(PettyObject::#typ(#name)) => Some(#name),
                    _ => None,
                })
            } else {
                quote!({
                    Some(PettyObject::#typ(#name)) => #name,
                    None => unimplemented!("Expected arg"),
                    _ => unimplemented!("Arg was of wrong type"),
                })
            };
            quote!(let #name = match &args.slice.get(#index) #match_body;)
        })
        .collect()
}

fn is_option(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(|attr| attr.meta.require_path_only().ok()?.get_ident())
        .any(|attr| attr == "option")
}
