extern crate proc_macro;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, Data, DeriveInput, Expr, Meta};

struct ConvertVariant(String, syn::Ident);

impl ToTokens for ConvertVariant {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let ConvertVariant(value, ident) = self;
        tokens.extend(quote! {
            #value => Self::#ident,
        });
    }
}

struct CustomConvertVariant(Expr, syn::Ident);

impl ToTokens for CustomConvertVariant {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let CustomConvertVariant(value, ident) = self;
        tokens.extend(quote! {
            #value => Self::#ident,
        });
    }
}

#[proc_macro_derive(ConvertKeywords, attributes(kw_from, kw))]
pub fn derive_convert_keywords(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let ident = input.ident;
    let data = match input.data {
        Data::Enum(data) => data,
        _ => panic!("Only enums are supported"),
    };
    let mut kw_from = None;
    let mut variants = vec![];
    let mut variants2 = vec![];
    for variant in data.variants {
        let name = variant.ident.to_string();
        if let Some(name) = name.strip_prefix("Kw") {
            variants.push(ConvertVariant(name.to_lowercase(), variant.ident.clone()));
        }

        for attr in variant.attrs {
            if attr.path().is_ident("kw_from") {
                if kw_from.is_some() {
                    panic!("Multiple kw_from items");
                }
                kw_from = Some(variant.ident.clone());
            } else if attr.path().is_ident("kw") {
                match attr.meta {
                    Meta::NameValue(syn::MetaNameValue { value, .. }) =>
                        variants2.push(CustomConvertVariant(value, variant.ident.clone())),
                    _ => panic!("kw attribute must have a value - #[kw = ...]")
                }
            }
        }
    }
    let kw_from = kw_from.expect("No item is tagged with #[kw_from]");

    quote! {
        impl #ident {
            pub fn convert_keywords(self, value: &str) -> Self {
                match self {
                    #ident::#kw_from => match value {
                        #(#variants)*
                        #(#variants2)*
                        _ => self,
                    },
                    _ => self,
                }
            }
        }
    }.into()
}
