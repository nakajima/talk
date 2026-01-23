use std::{env, path::Path};

const INSTRUCTIONS_SRC_PATH: &str = "src/ir/instruction.rs";

fn main() {
    let out_dir = env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("instr_impls.rs");
    println!("cargo:rerun-if-changed={INSTRUCTIONS_SRC_PATH}");
    println!("cargo:rerun-if-changed=build.rs");

    let content = std::fs::read_to_string(INSTRUCTIONS_SRC_PATH).unwrap();
    let file = syn::parse_file(&content).expect("Failed to parse src/lowering/instr.rs");

    let generated_code = generate_impls(&file).unwrap_or_else(|e| {
        panic!("Failed to generate impls for Instr: {e}");
    });

    std::fs::write(&dest_path, generated_code.to_string()).unwrap();
}

fn generate_impls(
    file: &syn::File,
) -> Result<proc_macro2::TokenStream, Box<dyn std::error::Error>> {
    let instr_enum = file
        .items
        .iter()
        .find_map(|item| {
            if let syn::Item::Enum(e) = item
                && e.ident == "Instruction"
            {
                return Some(e);
            }
            None
        })
        .ok_or_else(|| panic!("Could not find 'enum Instr' in {INSTRUCTIONS_SRC_PATH}"))?;

    let display_impl = generate_display_impl(instr_enum);
    let from_str_impl = generate_from_str_impl(instr_enum);

    Ok(quote::quote! {
        // #display_impl
        #[allow(
            dead_code,
            unused_imports,
            unused_variables,
            unused_mut,
            non_snake_case,
            non_camel_case_types,
            non_upper_case_globals,
            clippy::all
        )]
        #from_str_impl
        #display_impl
    })
}
fn generate_from_str_impl(instr_enum: &syn::ItemEnum) -> proc_macro2::TokenStream {
    use quote::{format_ident, quote};
    use syn::Fields;

    let enum_ident = &instr_enum.ident;
    let mut branches = Vec::new();

    for v in &instr_enum.variants {
        let v_ident = &v.ident;
        let doc =
            get_doc_attr(&v.attrs).unwrap_or_else(|| panic!("missing #[doc] on variant {v_ident}"));

        // ensure named fields & build set for validation
        let fields: Vec<_> = match &v.fields {
            Fields::Named(named) => named
                .named
                .iter()
                .map(|f| f.ident.clone().unwrap())
                .collect(),
            _ => panic!("variant {v_ident} must use named fields"),
        };

        // doc -> regex; $name => capture, last => (.*), others => (\S+)
        let mut regex_src = String::from("^\\s*");
        let mut holes: Vec<String> = Vec::new();
        let mut chars = doc.chars().peekable();
        let mut buf = String::new();
        let mut last_ws = false;

        let flush = |b: &mut String, out: &mut String| {
            if !b.is_empty() {
                out.push_str(&regex::escape(b));
                b.clear();
            }
        };

        while let Some(ch) = chars.next() {
            if ch == '$' {
                flush(&mut buf, &mut regex_src);
                let mut name = String::new();
                while let Some(&c) = chars.peek() {
                    if c == '_' || c.is_ascii_alphanumeric() {
                        name.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if name.is_empty() {
                    panic!("`$` without name in template for {v_ident}");
                }
                holes.push(name);
                regex_src.push_str("{{CAP}}");
                last_ws = false;
            } else if ch.is_whitespace() {
                if !last_ws {
                    flush(&mut buf, &mut regex_src);
                    regex_src.push_str("\\s+");
                }
                last_ws = true;
            } else {
                last_ws = false;
                buf.push(ch);
            }
        }
        flush(&mut buf, &mut regex_src);
        regex_src.push_str("\\s*$");

        if holes.is_empty() {
            panic!("template for {v_ident} must contain at least one $field");
        }

        // validate holes exist as fields
        for h in &holes {
            if !fields.iter().any(|f| f == &format_ident!("{h}")) {
                panic!("template for {v_ident} references unknown field `${h}`");
            }
        }

        // patch captures
        let total = holes.len();
        let mut count = 0usize;
        let mut patched = String::new();
        let mut parts = regex_src.split("{{CAP}}").peekable();
        while let Some(p) = parts.next() {
            patched.push_str(p);
            if parts.peek().is_some() {
                count += 1;
                if count == total {
                    patched.push_str("(.*)");
                } else {
                    patched.push_str("(\\S+)");
                }
            }
        }
        let regex_lit = patched;

        // Make the *last* capture (and its leading whitespace) optional,
        // so lines without trailing metas still match.
        let regex_lit = {
            let required = "\\s+(.*)\\s*$";
            let optional = "(?:\\s+(.*))?\\s*$";
            if let Some(pos) = regex_lit.rfind(required) {
                let mut s = regex_lit.clone();
                s.replace_range(pos.., optional);
                s
            } else {
                regex_lit
            }
        };

        // c0..cN capture bindings with literal indices 1..=N
        let cap_idents: Vec<_> = (0..holes.len()).map(|i| format_ident!("c{i}")).collect();
        let mut grab_caps = Vec::new();
        for (i, ident) in cap_idents.iter().enumerate() {
            let idx = i + 1;
            grab_caps.push(quote! {
                let #ident = caps.get(#idx).map(|m| m.as_str()).unwrap_or("").trim();
            });
        }

        // parse into locals named after holes, then use struct shorthand
        let mut parse_locals = Vec::new();
        let mut hole_idents = Vec::new();
        for (i, h) in holes.iter().enumerate() {
            let local = format_ident!("{h}");
            let cap = &cap_idents[i];
            hole_idents.push(local.clone());
            parse_locals
                .push(quote! { let #local = #cap.parse().map_err(|e| anyhow::anyhow!("{}", e))?; });
        }

        // For fields not mentioned in the template, set them to Default::default()
        let hole_set: std::collections::HashSet<_> = holes.iter().collect();
        let mut all_field_idents = Vec::new();
        for field in &fields {
            let field_name = field.to_string();
            if hole_set.contains(&field_name) {
                all_field_idents.push(quote! { #field });
            } else {
                all_field_idents.push(quote! { #field: Default::default() });
            }
        }

        let re_ident = format_ident!("RE_{}", v_ident);
        let branch = quote! {
            #[allow(clippy::unwrap_used)]
            static #re_ident: ::once_cell::sync::Lazy<::regex::Regex> =
                ::once_cell::sync::Lazy::new(|| ::regex::Regex::new(#regex_lit).unwrap());
            if let Some(caps) = #re_ident.captures(line) {
                use std::str::FromStr as _;
                #(#grab_caps)*
                #(#parse_locals)*
                let value = Self::#v_ident { #(#all_field_idents),* };
                return Ok(value);
            }
        };
        branches.push(branch);
    }

    quote! {
        use std::str::FromStr;
        use crate::ir::instruction::*;

        #[allow(
            dead_code,
            unused_imports,
            unused_variables,
            unused_mut,
            non_snake_case,
            non_camel_case_types,
            non_upper_case_globals,
            clippy::all
        )]
        impl<T> FromStr for crate::ir::#enum_ident<T>
        where
            T: FromStr,
            <T as FromStr>::Err: std::fmt::Display,
            crate::ir::register::Register: FromStr,
            <crate::ir::register::Register as FromStr>::Err: std::fmt::Display,
            crate::ir::value::Value: FromStr,
            <crate::ir::value::Value as FromStr>::Err: std::fmt::Display,
            crate::ir::instruction::InstructionMeta: FromStr,
            <crate::ir::instruction::InstructionMeta as FromStr>::Err: std::fmt::Display,
            crate::ir::list::List<crate::ir::instruction::InstructionMeta>: FromStr,
            <crate::ir::list::List<crate::ir::instruction::InstructionMeta> as FromStr>::Err: std::fmt::Display,
        {
            type Err = anyhow::Error;

            fn from_str(line: &str) -> Result<Self, Self::Err> {
                #(#branches)*
                Err(anyhow::anyhow!("unrecognized instruction: {}", line))
            }
        }

        #[allow(
            dead_code,
            unused_imports,
            unused_variables,
            unused_mut,
            non_snake_case,
            non_camel_case_types,
            non_upper_case_globals,
            clippy::all
        )]
        #[allow(clippy::unwrap_used)]
        pub fn parse_instruction<T>(line: &str) -> crate::ir::#enum_ident<T>
        where
            T: FromStr,
            <T as FromStr>::Err: std::fmt::Display,
            crate::ir::register::Register: FromStr,
            <crate::ir::register::Register as FromStr>::Err: std::fmt::Display,
            crate::ir::value::Value: FromStr,
            <crate::ir::value::Value as FromStr>::Err: std::fmt::Display,
            crate::ir::instruction::InstructionMeta: FromStr,
            <crate::ir::instruction::InstructionMeta as FromStr>::Err: std::fmt::Display,
            crate::ir::list::List<crate::ir::instruction::InstructionMeta>: FromStr,
            <crate::ir::list::List<crate::ir::instruction::InstructionMeta> as FromStr>::Err: std::fmt::Display,
        {
            line.parse().unwrap()
        }
    }
}

fn generate_display_impl(instr_enum: &syn::ItemEnum) -> proc_macro2::TokenStream {
    use quote::{format_ident, quote};
    use syn::Fields;

    let enum_ident = &instr_enum.ident;
    let mut arms = Vec::new();

    for v in &instr_enum.variants {
        let v_ident = &v.ident;
        let doc =
            get_doc_attr(&v.attrs).unwrap_or_else(|| panic!("missing #[doc] on variant {v_ident}"));

        // Named fields only (matches your enum)
        let field_idents: Vec<_> = match &v.fields {
            Fields::Named(named) => named
                .named
                .iter()
                .map(|f| f.ident.clone().unwrap())
                .collect(),
            _ => panic!("variant {v_ident} must use named fields"),
        };

        // Tokenize doc by whitespace.
        // Literal tokens are printed verbatim,
        // $name tokens are formatted via Display on that field.
        let tokens: Vec<String> = doc.split_whitespace().map(|s| s.to_string()).collect();

        // Build code that pushes each piece into a Vec<String>
        let mut pushes = Vec::new();
        for t in &tokens {
            if let Some(name) = t.strip_prefix('$') {
                let id = format_ident!("{}", name);
                // format field as string
                pushes.push(quote! {
                    parts.push(format!("{}", #id));
                });
            } else {
                // literal piece
                let lit = t.clone();
                pushes.push(quote! {
                    parts.push(#lit.to_string());
                });
            }
        }

        // Pattern: destructure all fields so we can use shorthand names
        let pat_fields = quote! { { #( #field_idents ),* } };

        // One match arm
        arms.push(quote! {
            Self::#v_ident #pat_fields => {
                // Build string parts from template
                let mut parts: Vec<String> = Vec::new();
                #(#pushes)*

                // Drop empty pieces (e.g., when last field formats to "")
                // and join with single spaces to avoid trailing space.
                let s = parts.into_iter()
                    .filter(|p| !p.is_empty())
                    .collect::<Vec<_>>()
                    .join(" ");
                write!(f, "{}", s)
            }
        });
    }

    quote! {
        impl<T> std::fmt::Display for crate::ir::#enum_ident<T>
        where
            T: std::fmt::Display,
            crate::ir::register::Register: std::fmt::Display,
            crate::ir::value::Value: std::fmt::Display,
            crate::ir::instruction::InstructionMeta: std::fmt::Display,
            // If you print a List<InstructionMeta>, make sure List<T>: Display in your crate.
            crate::ir::list::List<crate::ir::instruction::InstructionMeta>: std::fmt::Display,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#arms),*
                }
            }
        }
    }
}

fn get_doc_attr(attrs: &[syn::Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        if attr.path.is_ident("doc")
            && let Ok(syn::Meta::NameValue(nv)) = attr.parse_meta()
            && let syn::Lit::Str(lit) = nv.lit
        {
            return Some(lit.value().trim().to_string());
        }
        None
    })
}
