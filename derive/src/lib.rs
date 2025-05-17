extern crate proc_macro;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, Data, DeriveInput, Expr, Fields, Meta, Type};

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

#[proc_macro_derive(Instruction, attributes(dyn_ins, n))]
pub fn derive_instruction(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let ident = input.ident;
    let data = match input.data {
        Data::Enum(data) => data,
        _ => panic!("Only enums are supported"),
    };
    let mut inputs = vec![];
    let mut inputs_mut = vec![];
    let mut outputs = vec![];
    let mut outputs_mut = vec![];
    let mut strings = vec![];
    let mut lexer_translate = vec![];
    let mut side_effects = vec![];
    for variant in data.variants {
        let ident = variant.ident;
        let name = ident.to_string().to_lowercase();
        if variant.attrs.iter().find(|attr| attr.path().is_ident("dyn_ins")).is_some() {
            inputs.push(quote! {
                Self::#ident(val) => val.inputs(),
            });
            inputs_mut.push(quote! {
                Self::#ident(val) => val.inputs_mut(),
            });
            outputs.push(quote! {
                Self::#ident(val) => val.outputs(),
            });
            outputs_mut.push(quote! {
                Self::#ident(val) => val.outputs_mut(),
            });
            strings.push(quote! {
                Self::#ident(val) => <Box<dyn Instruction> as std::fmt::Display>::fmt(&val, f),
            });
            lexer_translate.push(quote! {
                Self::#ident(val) => val.lexer_translate(),
            });
            side_effects.push(quote! {
                Self::#ident(val) => val.side_effects(),
            });
            continue;
        }
        let has_side_effects = variant.attrs.iter().find(|attr| attr.path().is_ident("n")).is_none();
        match variant.fields {
            Fields::Unit => {
                inputs.push(quote! {
                    Self::#ident => vec![],
                });
                inputs_mut.push(quote! {
                    Self::#ident => vec![],
                });
                outputs.push(quote! {
                    Self::#ident => vec![],
                });
                outputs_mut.push(quote! {
                    Self::#ident => vec![],
                });
                strings.push(quote! {
                    Self::#ident => write!(f, #name),
                });
                side_effects.push(quote! {
                    Self::#ident => #has_side_effects,
                });
            },
            Fields::Unnamed(fields) => {
                let captures = (0..fields.unnamed.len())
                    .map(|i| syn::Ident::new(&format!("p_{}", i), ident.span()))
                    .collect::<Vec<_>>();
                let (ins, outs): (Vec<_>, Vec<_>) = fields.unnamed.into_iter()
                    .enumerate()
                    .map(|(i, field)| match field.ty {
                        Type::Path(path) => if path.path.is_ident("InsIn") || path.path.is_ident("In") {
                            (Some(syn::Ident::new(&format!("p_{}", i), ident.span())), None)
                        } else if path.path.is_ident("InsOut") || path.path.is_ident("Out") {
                            (None, Some(syn::Ident::new(&format!("p_{}", i), ident.span())))
                        } else {
                            (None, None)
                        },
                        _ => (None, None),
                    })
                    .unzip();
                let ins = ins.into_iter()
                    .filter_map(|i| i)
                    .collect::<Vec<_>>();
                let outs = outs.into_iter()
                    .filter_map(|i| i)
                    .collect::<Vec<_>>();
                inputs.push(quote! {
                    Self::#ident(#(#captures),*) => vec![#(#ins),*],
                });
                inputs_mut.push(quote! {
                    Self::#ident(#(#captures),*) => vec![#(#ins),*],
                });
                outputs.push(quote! {
                    Self::#ident(#(#captures),*) => vec![#(#outs),*],
                });
                outputs_mut.push(quote! {
                    Self::#ident(#(#captures),*) => vec![#(#outs),*],
                });
                let f_str = format!("{}{}", name, " {}".repeat(captures.len()));
                strings.push(quote! {
                    Self::#ident(#(#captures),*) => write!(f, #f_str, #(#captures),*),
                });
                side_effects.push(quote! {
                    Self::#ident(#(#captures),*) => #has_side_effects,
                });
            },
            _ => panic!("Only unit and tuple variants are supported"),
        }
    }

    quote! {
        impl Instruction for #ident {
            fn inputs(&self) -> Vec<&InsIn> {
                match self {
                    #(#inputs)*
                }
            }
            fn inputs_mut(&mut self) -> Vec<&mut InsIn> {
                match self {
                    #(#inputs_mut)*
                }
            }

            fn outputs(&self) -> Vec<&InsOut> {
                match self {
                    #(#outputs)*
                }
            }
            fn outputs_mut(&mut self) -> Vec<&mut InsOut> {
                match self {
                    #(#outputs_mut)*
                }
            }

            fn lexer_translate(&self) -> Option<Vec<Ins>> {
                match self {
                    #(#lexer_translate)*
                    _ => None,
                }
            }
        }

        impl Display for #ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#strings)*
                }
            }
        }
    }.into()
}
