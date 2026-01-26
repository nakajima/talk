use indexmap::IndexSet;
use rustc_hash::FxHashMap;
use std::{
    cell::{RefCell, RefMut},
    fmt::Debug,
    rc::Rc,
};

use crate::{
    name_resolution::{
        scc_graph::BindingGroup,
        symbol::{ProtocolId, Symbol},
    },
    types::{
        constraints::store::GroupId,
        infer_ty::{Infer, InferTy, Level},
        predicate::Predicate,
        type_operations::{InstantiationSubstitutions, UnificationSubstitutions},
        type_session::TypeSession,
        variational::Configuration,
    },
};

/// Shared state between parent and child solve contexts.
/// Accessed via Rc<RefCell<>> to allow child contexts to share
/// substitutions, givens, and projection_placeholders with their parent.
struct SharedSolveState {
    projection_placeholders: FxHashMap<InferTy, InferTy>,
    substitutions: UnificationSubstitutions,
    givens: IndexSet<Predicate<Infer>>,
}

pub struct SolveContext {
    kind: SolveContextKind,
    level: Level,
    group: GroupId,
    instantiations: InstantiationSubstitutions,
    shared: Rc<RefCell<SharedSolveState>>,
}

impl Debug for SolveContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SolveContext")
            .field("kind", &self.kind)
            .field("level", &self.level)
            .field("group", &self.group)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SolveContextKind {
    Normal,
    Protocol {
        protocol_self: Symbol,
        protocol_id: ProtocolId,
    },
    Nominal,
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
            level,
            group,
            instantiations: Default::default(),
            shared: Rc::new(RefCell::new(SharedSolveState {
                projection_placeholders: Default::default(),
                substitutions,
                givens: Default::default(),
            })),
        }
    }

    /// Create a child context with incremented level and fresh instantiations,
    /// sharing substitutions/givens/projection_placeholders with this context.
    pub fn next(&self) -> SolveContext {
        SolveContext {
            kind: self.kind,
            level: self.level.next(),
            group: self.group,
            instantiations: Default::default(),
            shared: Rc::clone(&self.shared),
        }
    }

    pub fn kind(&self) -> SolveContextKind {
        self.kind
    }

    pub fn level(&self) -> Level {
        self.level
    }

    pub fn group(&self) -> GroupId {
        self.group
    }

    pub fn group_info(&self) -> BindingGroup {
        BindingGroup {
            id: self.group,
            level: self.level,
            binders: Default::default(),
            is_top_level: Default::default(),
            config: Configuration::universal(),
        }
    }

    pub fn givens_mut(&self) -> RefMut<'_, IndexSet<Predicate<Infer>>> {
        RefMut::map(self.shared.borrow_mut(), |s| &mut s.givens)
    }

    pub fn substitutions_mut(&self) -> RefMut<'_, UnificationSubstitutions> {
        RefMut::map(self.shared.borrow_mut(), |s| &mut s.substitutions)
    }

    pub fn instantiations_mut(&mut self) -> &mut InstantiationSubstitutions {
        &mut self.instantiations
    }

    pub fn normalize(&self, ty: InferTy, session: &mut TypeSession) -> InferTy {
        self.normalize_with_level(ty, session, self.level)
    }

    fn normalize_with_level(
        &self,
        ty: InferTy,
        session: &mut TypeSession,
        level: Level,
    ) -> InferTy {
        let ty = {
            let mut shared = self.shared.borrow_mut();
            session.apply(ty, &mut shared.substitutions)
        };
        match &ty {
            InferTy::Projection {
                base: box InferTy::Var { .. },
                ..
            } => {
                let mut shared = self.shared.borrow_mut();
                if let Some(placeholder) = shared.projection_placeholders.get(&ty).cloned() {
                    return placeholder;
                }

                let placeholder = session.new_ty_meta_var(level);
                shared
                    .projection_placeholders
                    .insert(ty, placeholder.clone());
                placeholder
            }
            InferTy::Func(box param, box ret, effects) => InferTy::Func(
                self.normalize_with_level(param.clone(), session, level)
                    .into(),
                self.normalize_with_level(ret.clone(), session, level)
                    .into(),
                effects.clone(),
            ),
            _ => ty,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        compiling::module::ModuleId,
        label::Label,
        name_resolution::symbol::ProtocolId,
        types::{
            infer_ty::{InferTy, Level},
            solve_context::{SolveContext, SolveContextKind},
            type_operations::UnificationSubstitutions,
            type_session::TypeSession,
        },
    };

    #[test]
    fn normalizes_projection_on_meta() {
        let mut session = TypeSession::new(
            ModuleId::Current,
            Default::default(),
            Default::default(),
            Default::default(),
        );
        let var = session.new_ty_meta_var(Level::default());
        let ty = InferTy::Projection {
            protocol_id: ProtocolId::from(1),
            base: var.into(),
            associated: Label::Named("foo".into()),
        };

        let context = SolveContext::new(
            UnificationSubstitutions::new(session.meta_levels.clone()),
            Level::default(),
            Default::default(),
            SolveContextKind::Nominal,
        );

        let stable_1 = context.normalize(ty.clone(), &mut session);
        let stable_2 = context.normalize(ty, &mut session);
        assert!(matches!(stable_1, InferTy::Var { .. }));
        assert_eq!(stable_1, stable_2);
    }
}
