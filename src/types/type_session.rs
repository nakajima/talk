use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;

pub enum Ty {}

pub struct TypeSession {
    term_env: FxHashMap<Symbol, Ty>,
    type_env: FxHashMap<Symbol, Ty>,
}
