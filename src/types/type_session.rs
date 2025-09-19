use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::AST,
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::TypeId},
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    span::Span,
    types::{
        builtins::builtin_scope,
        constraint::Constraint,
        fields::{Method, TypeFields},
        kind::Kind,
        passes::{
            dependencies_pass::DependenciesPass,
            inference_pass::{InferencePass, Inferenced, Meta, collect_meta},
            type_headers_pass::TypeHeaderPass,
            type_resolve_pass::{HeadersResolved, TypeResolvePass},
        },
        row::Row,
        scheme::{ForAll, Scheme},
        term_environment::{EnvEntry, TermEnv},
        ty::{Level, Ty},
        type_operations::{UnificationSubstitutions, apply},
        vars::Vars,
    },
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ASTTyRepr {
    Annotated(TypeAnnotation), // already resolved names
    Generic(GenericDecl),
    Hole(NodeID, Span),           // no annotation; to be inferred later
    SelfType(Name, NodeID, Span), // For synthesized `self` param
}

impl ASTTyRepr {
    pub fn span(&self) -> Span {
        match self {
            Self::Annotated(ta) => ta.span,
            Self::Generic(gd) => gd.span,
            Self::Hole(_, span) => *span,
            Self::SelfType(_, _, span) => *span,
        }
    }
}

pub trait TypingPhase: std::fmt::Debug {
    type Next: TypingPhase;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
    Extension,
}

#[derive(Debug, PartialEq, Default)]
pub struct Raw {
    pub type_constructors: FxHashMap<TypeId, TypeDef<ASTTyRepr>>,
    pub protocols: FxHashMap<TypeId, TypeDef<ASTTyRepr>>,
}

impl TypingPhase for Raw {
    type Next = HeadersResolved;
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeExtension<T> {
    pub node_id: NodeID,
    pub conformances: Vec<TypeId>,
    pub methods: IndexMap<Label, Method<T>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef<T> {
    pub name: Name,
    pub node_id: NodeID,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub generics: IndexMap<Name, T>,
    pub fields: TypeFields<T>,
    pub extensions: Vec<TypeExtension<T>>,
}

#[derive(Debug)]
pub struct TypeSession<Phase: TypingPhase = Raw> {
    pub vars: Vars,
    pub synthsized_ids: IDGenerator,
    pub phase: Phase,
    pub term_env: TermEnv,
    pub meta_levels: FxHashMap<Meta, Level>,
}

impl Default for TypeSession<Raw> {
    fn default() -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.promote(sym, entry);
        }

        TypeSession {
            vars: Default::default(),
            synthsized_ids: Default::default(),
            phase: Raw {
                type_constructors: Default::default(),
                protocols: Default::default(),
            },
            meta_levels: Default::default(),
            term_env,
        }
    }
}

pub struct Typed {}

impl<Phase: TypingPhase> TypeSession<Phase> {
    pub fn drive(ast: &mut AST<NameResolved>) -> TypeSession<Inferenced> {
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderPass::drive(&mut session, ast);
        let session = TypeResolvePass::drive(ast, session);
        let session = DependenciesPass::drive(session, ast);
        InferencePass::perform(session, ast)
    }

    #[instrument(skip(self))]
    pub fn generalize(&mut self, inner: Level, ty: Ty, unsolved: &[Constraint]) -> EnvEntry {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // keep only metas born at or above inner
        let mut foralls = vec![];
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                Ty::Param(p) => {
                    // No substitution needed (the ty already contains Ty::Param(p)),
                    // but we must record it in `foralls`, so instantiate() knows what to replace.
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.push(ForAll::Ty(*p));
                    }
                }

                Ty::UnificationVar { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.type_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, Ty::Param(param_id));
                }
                Ty::Record(box Row::Var(id)) => {
                    let level = self
                        .meta_levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Row(param_id));
                    substitutions.row.insert(*id, Row::Param(param_id));
                }
                _ => {
                    tracing::warn!("got {m:?} for var while generalizing")
                }
            }
        }

        let ty = apply(ty, &mut substitutions);

        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }

        let predicates = unsolved
            .iter()
            .map(|c| c.into_predicate(&mut substitutions))
            .collect();

        EnvEntry::Scheme(Scheme::new(foralls, predicates, ty))
    }

    #[instrument(skip(self))]
    pub fn generalize_with_substitutions(
        &mut self,
        inner: Level,
        ty: Ty,
        unsolved: &[Constraint],
        substitutions: &mut UnificationSubstitutions,
    ) -> EnvEntry {
        let ty = apply(ty, substitutions);

        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // keep only metas born at or above inner
        let mut foralls = vec![];
        for m in &metas {
            match m {
                Ty::Param(p) => {
                    // No substitution needed (the ty already contains Ty::Param(p)),
                    // but we must record it in `foralls`, so instantiate() knows what to replace.
                    if !foralls
                        .iter()
                        .any(|fa| matches!(fa, ForAll::Ty(q) if *q == *p))
                    {
                        foralls.push(ForAll::Ty(*p));
                    }
                }

                Ty::UnificationVar { level, id } => {
                    if *level <= inner {
                        tracing::warn!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.type_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Ty(param_id));
                    substitutions.ty.insert(*id, Ty::Param(param_id));
                }
                Ty::Record(box Row::Var(id)) => {
                    let level = self
                        .meta_levels
                        .get(&Meta::Row(*id))
                        .expect("didn't get level for row meta");
                    if *level <= inner {
                        tracing::trace!("discarding {m:?} due to level ({level:?} < {inner:?})");
                        continue;
                    }

                    let param_id = self.vars.row_params.next_id();
                    tracing::trace!("generalizing {m:?} to {param_id:?}");
                    foralls.push(ForAll::Row(param_id));
                    substitutions.row.insert(*id, Row::Param(param_id));
                }
                _ => {
                    tracing::warn!("got {m:?} for var while generalizing")
                }
            }
        }

        let ty = apply(ty, substitutions);

        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }

        let predicates = unsolved
            .iter()
            .map(|c| c.into_predicate(substitutions))
            .collect();

        EnvEntry::Scheme(Scheme::new(foralls, predicates, ty))
    }

    pub fn advance(self, phase: Phase::Next) -> TypeSession<Phase::Next> {
        TypeSession::<Phase::Next> {
            vars: self.vars,
            synthsized_ids: self.synthsized_ids,
            phase,
            term_env: self.term_env,
            meta_levels: self.meta_levels,
        }
    }

    pub(crate) fn new_ty_meta_var(&mut self, level: Level) -> Ty {
        let id = self.vars.ty_metas.next_id();
        self.meta_levels.insert(Meta::Ty(id), level);
        tracing::trace!("Fresh {id:?}");
        Ty::UnificationVar { id, level }
    }

    pub(crate) fn new_row_meta_var(&mut self, level: Level) -> Row {
        let id = self.vars.row_metas.next_id();
        self.meta_levels.insert(Meta::Row(id), level);
        tracing::trace!("Fresh {id:?}");
        Row::Var(id)
    }
}
