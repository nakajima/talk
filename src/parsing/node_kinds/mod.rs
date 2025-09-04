pub mod attribute;
pub mod block;
pub mod call_arg;
pub mod decl;
pub mod expr;
pub mod func;
pub mod func_signature;
pub mod generic_decl;
pub mod incomplete_expr;
pub mod match_arm;
pub mod parameter;
pub mod pattern;
pub mod record_field;
pub mod stmt;
pub mod type_annotation;

#[macro_export]
macro_rules! impl_into_node {
    // 1-arg form: use the same ident as the type
    ($variant:ident $(,)?) => {
        $crate::impl_into_node!($variant, $variant);
    };
    ($variant:ident, $ty:ty) => {
        impl $crate::node::NodeType for $ty {}

        impl From<$crate::parsing::node::Node> for $ty {
            fn from(node: $crate::parsing::node::Node) -> $ty {
                let $crate::parsing::node::Node::$variant(val) = node else {
                    panic!("Unable to convert {node:?} to {}", stringify!($ty));
                };

                val
            }
        }

        impl From<$ty> for $crate::parsing::node::Node {
            fn from(val: $ty) -> Self {
                $crate::parsing::node::Node::$variant(val)
            }
        }

        impl From<&$ty> for $crate::parsing::node::Node {
            fn from(val: &$ty) -> Self {
                $crate::parsing::node::Node::$variant(val.clone())
            }
        }
    };
}
