extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro]
pub fn include_generated_ir(_item: TokenStream) -> TokenStream {
    "
    include!(concat!(env!(\"OUT_DIR\"), \"/instr_impls.rs\"));
    "
    .parse()
    .unwrap()
}
