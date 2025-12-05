use indexmap::IndexSet;
use rustc_hash::FxHashMap;
use std::fmt::Debug;

use crate::{
    name_resolution::{scc_graph::BindingGroup, symbol::ProtocolId},
    types::{
        constraints::store::GroupId,
        infer_ty::{InferTy, Level, TypeParamId},
        predicate::Predicate,
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_operations::{InstantiationSubstitutions, UnificationSubstitutions},
        type_session::TypeSession,
    },
};

#[derive(Debug)]
pub struct SolveContext {
    pub(super) kind: SolveContextKind,
    pub(super) projection_placeholders: FxHashMap<InferTy, InferTy>,
    pub(super) substitutions: UnificationSubstitutions,
    pub(super) instantiations: InstantiationSubstitutions,
    pub(super) givens: IndexSet<Predicate<InferTy>>,
    pub(super) level: Level,
    pub(super) group: GroupId,
}

pub struct ChildSolveContext<'a> {
    pub(super) kind: SolveContextKind,
    pub(super) parent: &'a mut SolveContext,
    pub(super) level: Level,
    pub(super) instantiations: InstantiationSubstitutions,
    pub(super) expected_return: Option<InferTy>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SolveContextKind {
    Normal,
    Protocol {
        protocol_self: TypeParamId,
        protocol_id: ProtocolId,
    },
    Nominal,
}

pub trait Solve
where
    Self: Sized,
{
    fn kind(&self) -> SolveContextKind;
    fn next(&'_ mut self) -> ChildSolveContext<'_>;
    fn group(&self) -> GroupId;
    fn level(&self) -> Level;
    fn normalize(&mut self, ty: InferTy, session: &mut TypeSession) -> InferTy;
    fn parent(&mut self) -> &mut SolveContext;
    fn givens_mut(&'_ mut self) -> &mut IndexSet<Predicate<InferTy>>;
    fn substitutions_mut(&'_ mut self) -> &mut UnificationSubstitutions;
    fn instantiations_mut(&'_ mut self) -> &mut InstantiationSubstitutions;
    fn group_info(&self) -> BindingGroup {
        BindingGroup {
            id: self.group(),
            level: self.level(),
            binders: Default::default(),
        }
    }
}

impl<'a> Solve for ChildSolveContext<'a> {
    fn next(&'_ mut self) -> ChildSolveContext<'_> {
        ChildSolveContext {
            kind: self.kind,
            level: self.level().next(),
            parent: self.parent,
            instantiations: Default::default(),
            expected_return: self.expected_return.clone(),
        }
    }

    fn kind(&self) -> SolveContextKind {
        self.kind
    }

    fn givens_mut(&'_ mut self) -> &mut IndexSet<Predicate<InferTy>> {
        &mut self.parent().givens
    }

    fn level(&self) -> Level {
        self.level
    }

    fn parent(&mut self) -> &mut SolveContext {
        self.parent.parent()
    }

    fn normalize(&mut self, ty: InferTy, session: &mut TypeSession) -> InferTy {
        let level = self.level();
        self.parent().normalize_with_level(ty, session, level)
    }

    fn instantiations_mut(&'_ mut self) -> &mut InstantiationSubstitutions {
        &mut self.instantiations
    }

    fn substitutions_mut(&'_ mut self) -> &mut UnificationSubstitutions {
        &mut self.parent().substitutions
    }

    fn group(&self) -> GroupId {
        self.parent.group
    }
}

impl Solve for SolveContext {
    fn next(&'_ mut self) -> ChildSolveContext<'_> {
        ChildSolveContext {
            kind: self.kind,
            level: self.level().next(),
            parent: self,
            instantiations: Default::default(),
            expected_return: None,
        }
    }

    fn kind(&self) -> SolveContextKind {
        self.kind
    }

    fn level(&self) -> Level {
        self.level
    }

    fn parent(&mut self) -> &mut SolveContext {
        self
    }

    fn normalize(&mut self, ty: InferTy, session: &mut TypeSession) -> InferTy {
        self.normalize_with_level(ty, session, self.level)
    }

    fn givens_mut(&'_ mut self) -> &mut IndexSet<Predicate<InferTy>> {
        &mut self.givens
    }

    fn instantiations_mut(&'_ mut self) -> &mut InstantiationSubstitutions {
        &mut self.instantiations
    }

    fn substitutions_mut(&'_ mut self) -> &mut UnificationSubstitutions {
        &mut self.substitutions
    }

    fn group(&self) -> GroupId {
        self.group
    }
}

impl SolveContext {
    pub(super) fn new(
        substitutions: UnificationSubstitutions,
        level: Level,
        group: GroupId,
        kind: SolveContextKind,
    ) -> Self {
        Self {
            kind,
            substitutions,
            projection_placeholders: Default::default(),
            givens: Default::default(),
            instantiations: Default::default(),
            level,
            group,
        }
    }

    fn normalize_with_level(
        &mut self,
        ty: InferTy,
        session: &mut TypeSession,
        level: Level,
    ) -> InferTy {
        let ty = session.apply(ty, &mut self.substitutions);
        match &ty {
            InferTy::Projection {
                base: box InferTy::Nominal { symbol, .. },
                protocol_id,
                associated,
            } => {
                let Some(conformance) = session.type_catalog.conformances.get(&ConformanceKey {
                    protocol_id: *protocol_id,
                    conforming_id: *symbol,
                }) else {
                    return InferTy::Error(
                        TypeError::TypesDoesNotConform {
                            symbol: *symbol,
                            protocol_id: *protocol_id,
                        }
                        .into(),
                    );
                };
                let Some(ty) = conformance.associated_types.get(associated).cloned() else {
                    return InferTy::Error(
                        TypeError::MissingConformanceRequirement(format!(
                            "Associated type: {associated:?}"
                        ))
                        .into(),
                    );
                };

                ty
            }
            InferTy::Projection {
                base: box InferTy::Var { .. },
                ..
            } => {
                if let Some(placeholder) = self.projection_placeholders.get(&ty).cloned() {
                    return placeholder;
                }

                let placeholder = session.new_ty_meta_var(level);
                self.projection_placeholders.insert(ty, placeholder.clone());
                placeholder
            }
            InferTy::Func(box param, box ret) => InferTy::Func(
                self.normalize_with_level(param.clone(), session, level)
                    .into(),
                self.normalize_with_level(ret.clone(), session, level)
                    .into(),
            ),
            _ => ty,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use std::assert_matches::assert_matches;

    use crate::{
        compiling::module::ModuleId,
        fxhashmap,
        label::Label,
        name_resolution::symbol::{ProtocolId, StructId, Symbol},
        node_id::NodeID,
        span::Span,
        types::{
            infer_ty::{InferTy, Level},
            solve_context::{Solve, SolveContext, SolveContextKind},
            type_catalog::{Conformance, ConformanceKey},
            type_operations::UnificationSubstitutions,
            type_session::TypeSession,
        },
    };

    #[test]
    fn normalizes_projection_on_nominal() {
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let var = session.new_ty_meta_var(Level::default());
        session.type_catalog.conformances.insert(
            ConformanceKey {
                protocol_id: ProtocolId::from(1),
                conforming_id: Symbol::Struct(StructId::from(1)),
            },
            Conformance {
                node_id: NodeID::SYNTHESIZED,
                conforming_id: Symbol::Struct(1.into()),
                protocol_id: ProtocolId::from(1),
                witnesses: Default::default(),
                associated_types: fxhashmap!(
                    Label::Named("foo".into()) => var.clone()
                ),
                span: Span::SYNTHESIZED,
            },
        );

        let ty = InferTy::Projection {
            protocol_id: ProtocolId::from(1),
            base: InferTy::Nominal {
                symbol: Symbol::Struct(1.into()),
                type_args: Default::default(),
            }
            .into(),
            associated: Label::Named("foo".into()),
        };

        let mut context = SolveContext::new(
            UnificationSubstitutions::new(session.meta_levels.clone()),
            Level::default(),
            Default::default(),
            SolveContextKind::Nominal,
        );

        assert_eq!(context.normalize(ty, &mut session), var);
    }

    #[test]
    fn normalizes_projection_on_meta() {
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let var = session.new_ty_meta_var(Level::default());
        let ty = InferTy::Projection {
            protocol_id: ProtocolId::from(1),
            base: var.into(),
            associated: Label::Named("foo".into()),
        };

        let mut context = SolveContext::new(
            UnificationSubstitutions::new(session.meta_levels.clone()),
            Level::default(),
            Default::default(),
            SolveContextKind::Nominal,
        );

        let stable_1 = context.normalize(ty.clone(), &mut session);
        let stable_2 = context.normalize(ty, &mut session);
        assert_matches!(stable_1, InferTy::Var { .. });
        assert_eq!(stable_1, stable_2);
    }
}
