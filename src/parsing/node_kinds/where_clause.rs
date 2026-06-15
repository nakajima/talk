use derive_visitor::{Drive, DriveMut};

use crate::{
    node_id::NodeID,
    node_kinds::type_annotation::TypeAnnotation,
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct WhereClause {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    pub predicates: Vec<WherePredicate>,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct WherePredicate {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    pub kind: WherePredicateKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum WherePredicateKind {
    TypeEq {
        lhs: TypeAnnotation,
        rhs: TypeAnnotation,
    },
    Conforms {
        ty: TypeAnnotation,
        protocols: Vec<TypeAnnotation>,
    },
}
