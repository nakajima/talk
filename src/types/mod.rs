use crate::types::kind::Kind;

pub mod builtins;
pub mod constraints;
pub mod fields;
pub mod kind;
pub mod passes;
pub mod row;
pub mod ty;
pub mod type_error;
pub mod type_operations;
pub mod type_session;
pub mod types_decorator;

// Helper for n-ary arrows when all args are the same:
pub fn arrow_n(arg: Kind, n: usize, ret: Kind) -> Kind {
    (0..n).fold(ret, |acc, _| Kind::Arrow {
        in_kind: Box::new(arg.clone()),
        out_kind: Box::new(acc),
    })
}

#[macro_export]
macro_rules! fxhashmap {
    ($($k:expr => $v:expr),* $(,)?) => {
        ($k, $v) => {
            let mut m = rustc_hash::FxHashMap::default();
            $( m.insert($k, $v); )*
            m
        }
    };
}

#[macro_export]
macro_rules! indexmap {
    ($($k:expr => $v:expr),* $(,)?) => {{
        let mut m = indexmap::IndexMap::new();
        $( m.insert($k, $v); )*
        m
    }};
}
