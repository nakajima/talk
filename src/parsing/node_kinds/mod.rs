pub mod attribute;
pub mod block;
pub mod body;
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

        impl TryFrom<$crate::parsing::node::Node> for $ty {
            type Error = $crate::parsing::parser_error::ParserError;

            fn try_from(node: $crate::parsing::node::Node) -> Result<$ty, Self::Error> {
                let $crate::parsing::node::Node::$variant(val) = node else {
                    return Err(Self::Error::ConversionError(format!(
                        "could not convert node to {:?}: {:?}",
                        stringify!($ty),
                        node
                    )));
                };

                Ok(val)
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
