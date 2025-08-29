pub mod attribute;
pub mod block;
pub mod call_arg;
pub mod decl;
pub mod expr;
pub mod func;
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

        impl From<Node> for $ty {
            fn from(node: Node) -> $ty {
                let Node::$variant(val) = node else {
                    panic!("Unable to convert {node:?} to {}", stringify!($ty));
                };

                val
            }
        }

        impl From<$ty> for Node {
            fn from(val: $ty) -> Self {
                Node::$variant(val)
            }
        }

        impl From<&$ty> for Node {
            fn from(val: &$ty) -> Self {
                Node::$variant(val.clone())
            }
        }
    };
}
