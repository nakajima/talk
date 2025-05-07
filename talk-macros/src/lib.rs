use proc_macro::TokenStream;
use quote::quote;
use syn::{FieldsNamed, ItemStruct, parse_macro_input};

/// ```rust
/// use talk_macros::expr;
///
/// #[expr]
/// struct Node<'a> {
///     parent: Option<&'a Node<'a>>
/// }
///
/// impl<'a> Node<'a> {
///     fn new(parent: Option<&'a Node<'a>>) -> Self {
///         Self {
///             parent
///         }
///     }
/// }
///
/// let n = Node::new_with_meta(None);
/// assert_eq!(n.meta.id, 0);
/// ```
#[proc_macro_attribute]
pub fn expr(args: TokenStream, input: TokenStream) -> TokenStream {
    let mut item_struct = parse_macro_input!(input as ItemStruct);
    let name = item_struct.ident.clone();

    if let syn::Fields::Named(fields_named) = &mut item_struct.fields {
        fields_named
            .named
            .push(syn::parse_quote!(pub meta: ExprMeta));
    } else {
        panic!("#[expr] only on named‐field structs");
    }

    let expanded = quote! {
        #item_struct

        impl Expr for #name {
            fn meta(&self) -> ExprMeta {
                self.meta
            }
        }
    };

    TokenStream::from(expanded)
}
