// build.rs
use quote::{ToTokens, quote};
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::Path;
use syn::{Fields, GenericArgument, PathArguments, Type};

fn main() {
    let out_dir = env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("instr_impls.rs");

    let instr_file_path = "src/lowering/instr.rs";
    println!("cargo:rerun-if-changed={}", instr_file_path);
    println!("cargo:rerun-if-changed=build.rs");

    let content = fs::read_to_string(instr_file_path).unwrap();
    let file = syn::parse_file(&content).expect("Failed to parse src/lowering/instr.rs");

    let generated_code = generate_impls(&file).unwrap_or_else(|e| {
        panic!("Failed to generate impls for Instr: {}", e);
    });

    fs::write(&dest_path, generated_code.to_string()).unwrap();
}

fn get_option_inner_type(ty: &Type) -> Option<&Type> {
    if let Type::Path(type_path) = ty {
        if type_path.qself.is_none() && type_path.path.segments.len() == 1 {
            let segment = &type_path.path.segments[0];
            if segment.ident == "Option" {
                if let PathArguments::AngleBracketed(args) = &segment.arguments {
                    if args.args.len() == 1 {
                        if let GenericArgument::Type(inner_ty) = &args.args[0] {
                            return Some(inner_ty);
                        }
                    }
                }
            }
        }
    }
    None
}

fn generate_impls(
    file: &syn::File,
) -> Result<proc_macro2::TokenStream, Box<dyn std::error::Error>> {
    let instr_enum = file
        .items
        .iter()
        .find_map(|item| {
            if let syn::Item::Enum(e) = item {
                if e.ident == "Instr" {
                    return Some(e);
                }
            }
            None
        })
        .ok_or("Could not find 'enum Instr' in src/lowering/instr.rs")?;

    let display_impl = generate_display_impl(instr_enum);
    let from_str_impl = generate_from_str_impl(instr_enum);

    Ok(quote! {
        #display_impl
        #from_str_impl
    })
}

fn get_doc_attr(attrs: &[syn::Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        if attr.path.is_ident("doc") {
            if let Ok(syn::Meta::NameValue(nv)) = attr.parse_meta() {
                if let syn::Lit::Str(lit) = nv.lit {
                    return Some(lit.value().trim().to_string());
                }
            }
        }
        None
    })
}

fn generate_display_impl(instr_enum: &syn::ItemEnum) -> proc_macro2::TokenStream {
    let match_arms = instr_enum.variants.iter().map(|variant| {
        let variant_ident = &variant.ident;
        let format_str = get_doc_attr(&variant.attrs)
            .unwrap_or_else(|| panic!("Variant {} is missing doc attribute", variant_ident));

        let (field_idents, fields_are_named) = match &variant.fields {
            Fields::Named(f) => (
                f.named
                    .iter()
                    .map(|field| field.ident.as_ref().unwrap().clone())
                    .collect(),
                true,
            ),
            Fields::Unnamed(f) => (
                (0..f.unnamed.len())
                    .map(|i| syn::Ident::new(&format!("v{}", i), proc_macro2::Span::call_site()))
                    .collect(),
                false,
            ),
            Fields::Unit => (vec![], true),
        };
        let field_types: Vec<_> = match &variant.fields {
            Fields::Named(f) => f.named.iter().map(|field| &field.ty).collect(),
            Fields::Unnamed(f) => f.unnamed.iter().map(|field| &field.ty).collect(),
            Fields::Unit => vec![],
        };
        let field_pattern = if fields_are_named {
            quote! { { #( #field_idents ),* } }
        } else {
            quote! { ( #( #field_idents ),* ) }
        };

        let mut write_ops = Vec::new();
        let mut last_end = 0;
        let placeholder_re = regex::Regex::new(r"\$\w+").unwrap();

        for mat in placeholder_re.find_iter(&format_str) {
            if mat.start() > last_end {
                let literal = &format_str[last_end..mat.start()];
                write_ops.push(quote! { write!(f, #literal)?; });
            }

            let placeholder_name = &mat.as_str()[1..];
            let (field_idx, field_ident) = if let Ok(idx) = placeholder_name.parse::<usize>() {
                (idx, &field_idents[idx])
            } else {
                field_idents
                    .iter()
                    .enumerate()
                    .find(|(_, ident)| *ident == placeholder_name)
                    .unwrap_or_else(|| panic!("Named placeholder '{}' not found in variant '{}'",
                        placeholder_name, variant_ident))
            };

            let field_ty = field_types[field_idx];

            if get_option_inner_type(field_ty).is_some() {
                write_ops.push(quote! {
                   if let Some(val) = &#field_ident {
                       write!(f, "{}", val)?;
                   }
                });
            } else {
                write_ops.push(quote! { write!(f, "{}", #field_ident)?; });
            }
            last_end = mat.end();
        }

        if last_end < format_str.len() {
            let literal = &format_str[last_end..];
            write_ops.push(quote! { write!(f, #literal)?; });
        }

        quote! {
            Self::#variant_ident #field_pattern => {
                #( #write_ops )*
                Ok(())
            }
        }
    });

    quote! {
        use std::fmt;
        use crate::lowering::instr::*;

        impl fmt::Display for Instr {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    #( #match_arms ),*
                }
            }
        }
    }
}

fn regex_for_type(ty: &Type) -> &'static str {
    let type_str = ty.to_token_stream().to_string();
    match type_str.as_str() {
        "Register" => r"(%\d+)",
        "i64" | "u16" => r"(-?\d+)",
        "f64" => r"(-?\d+\.\d+)",
        "bool" => r"(true|false)",
        "BasicBlockID" => r"(#\d+|entry)",
        "RegisterList" => r"((?:%\d+(?:,\s*%\d+)*)?)",

        // FIX: Use a specific regex for types that start with '@'
        "RefKind" | "FuncName" => r"(@\S+)",

        // FIX: Use a non-greedy "match anything" for IRType. This works because
        // the following patterns (like RefKind or Register) are specific enough
        // to stop this one from consuming the whole line.
        "IRType" => r"(.*?)",

        "String" => r"(\S+)",
        "PhiPredecessors" => r"(\[.*?\])",
        "RetVal" => r"(.+)",
        _ => r"(\S+)", // Default fallback
    }
}

// In build.rs
fn generate_from_str_impl(instr_enum: &syn::ItemEnum) -> proc_macro2::TokenStream {
    let mut static_regexes = Vec::new();
    let mut parser_arms = Vec::new();

    for variant in &instr_enum.variants {
        let variant_ident = &variant.ident;
        let static_re_ident = syn::Ident::new(
            &format!("RE_{}", variant_ident.to_string().to_uppercase()),
            proc_macro2::Span::call_site(),
        );

        let format_str = get_doc_attr(&variant.attrs).expect("Missing doc format string");
        let placeholder_re = regex::Regex::new(r"\$([a-zA-Z0-9_]+)").unwrap();

        let field_map: HashMap<String, &Type> = match &variant.fields {
            Fields::Named(f) => f
                .named
                .iter()
                .map(|field| (field.ident.as_ref().unwrap().to_string(), &field.ty))
                .collect(),
            Fields::Unnamed(f) => f
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, field)| (i.to_string(), &field.ty))
                .collect(),
            Fields::Unit => HashMap::new(),
        };

        let mut regex_str = String::from(r"^\s*");
        let mut last_end = 0;
        let mut placeholder_to_idx: HashMap<String, usize> = HashMap::new();
        let mut cap_idx: usize = 1;

        for mat in placeholder_re.find_iter(&format_str) {
            let literal_part = &format_str[last_end..mat.start()];
            let placeholder_name = mat.as_str()[1..].to_string();

            let field_type = field_map.get(&placeholder_name).unwrap_or_else(|| {
                panic!(
                    "Placeholder ${} has no corresponding field in variant {}",
                    placeholder_name, variant_ident
                )
            });

            if let Some(inner_ty) = get_option_inner_type(field_type) {
                let group = format!(
                    "{}{}",
                    regex::escape(literal_part),
                    regex_for_type(inner_ty)
                );
                regex_str.push_str(&format!("(?:{})?", group));
            } else {
                regex_str.push_str(&regex::escape(literal_part));
                regex_str.push_str(regex_for_type(field_type));
            }

            placeholder_to_idx.insert(placeholder_name.clone(), cap_idx);
            cap_idx += 1;
            last_end = mat.end();
        }
        regex_str.push_str(&regex::escape(&format_str[last_end..]));
        regex_str.push_str(r"\s*;?\s*$");

        static_regexes.push(quote! {
            static #static_re_ident: Lazy<Regex> = Lazy::new(|| {
                Regex::new(#regex_str).unwrap_or_else(|e| {
                    panic!("Failed to compile regex for {}: {}\\nRegex: {}", stringify!(#variant_ident), e, #regex_str);
                })
            });
        });

        let (constructor, parsers) = match &variant.fields {
            Fields::Named(fields) => {
                let field_parsers = fields.named.iter().map(|field| {
                    let field_ident = field.ident.as_ref().unwrap();
                    let field_ty = &field.ty;
                    let cap_idx = placeholder_to_idx.get(&field_ident.to_string()).unwrap();

                    if let Some(inner_ty) = get_option_inner_type(field_ty) {
                        quote! {
                            let #field_ident: #field_ty = caps.get(#cap_idx)
                                .and_then(|m| m.as_str().trim().parse::<#inner_ty>().ok());
                        }
                    } else {
                        quote! {
                            let #field_ident: #field_ty = caps.get(#cap_idx).unwrap().as_str().trim().parse()
                                .map_err(|e: <#field_ty as FromStr>::Err| format!("Could not parse '{}' from capture '{}': {}", stringify!(#field_ident), caps.get(#cap_idx).unwrap().as_str(), e.to_string()))?;
                        }
                    }
                });
                let field_names = fields.named.iter().map(|f| f.ident.as_ref().unwrap());
                (
                    quote! { { #( #field_names ),* } },
                    quote! { #( #field_parsers )* },
                )
            }
            Fields::Unnamed(fields) => {
                let var_parsers = fields.unnamed.iter().enumerate().map(|(i, field)| {
                    let var_name = syn::Ident::new(&format!("v{}", i), proc_macro2::Span::call_site());
                    let field_ty = &field.ty;
                    let cap_idx = placeholder_to_idx.get(&i.to_string()).unwrap();

                    if let Some(inner_ty) = get_option_inner_type(field_ty) {
                        quote! {
                            let #var_name: #field_ty = caps.get(#cap_idx)
                                .and_then(|m| m.as_str().trim().parse::<#inner_ty>().ok());
                        }
                    } else {
                        quote! {
                            let #var_name: #field_ty = caps.get(#cap_idx).unwrap().as_str().trim().parse()
                                .map_err(|e: <#field_ty as FromStr>::Err| format!("Could not parse argument {} from capture '{}': {}", #i, caps.get(#cap_idx).unwrap().as_str(), e.to_string()))?;
                        }
                    }
                });
                let var_names = (0..fields.unnamed.len())
                    .map(|i| syn::Ident::new(&format!("v{}", i), proc_macro2::Span::call_site()));
                (
                    quote! { ( #( #var_names ),* ) },
                    quote! { #( #var_parsers )* },
                )
            }
            Fields::Unit => (quote! {}, quote! {}),
        };

        parser_arms.push(quote! {
            #[allow(unused)]
            if let Some(caps) = #static_re_ident.captures(s) {
                #parsers
                return Ok(Self::#variant_ident #constructor);
            }
        });
    }

    quote! {
        use std::str::FromStr;
        use std::string::ToString;
        use once_cell::sync::Lazy;
        use regex::Regex;

        #(#static_regexes)*

        impl FromStr for Instr {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                use crate::lowering::instr::*;
                use crate::lowering::lowerer::*;

                #(#parser_arms)*

                Err(format!("Could not parse '{}' as an instruction.", s))
            }
        }
    }
}
