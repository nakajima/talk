use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::AST,
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{ProtocolId, Symbol, TypeId},
    },
    node_id::NodeID,
    node_kinds::{generic_decl::GenericDecl, type_annotation::TypeAnnotation},
    span::Span,
    types::{
        builtins::builtin_scope,
        constraints::constraint::Constraint,
        fields::{Method, TypeFields},
        kind::Kind,
        passes::{
            dependencies_pass::{DependenciesPass, SCCResolved},
            inference_pass::{InferencePass, Meta, collect_meta},
            type_headers_pass::TypeHeaderPass,
            type_resolve_pass::TypeResolvePass,
        },
        row::Row,
        scheme::{ForAll, Scheme},
        term_environment::{EnvEntry, TermEnv},
        ty::{Level, SkolemId, Ty, TypeParamId},
        type_catalog::{ConformanceStub, TypeCatalog},
        type_operations::{UnificationSubstitutions, apply, apply_row, substitute},
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeDefKind {
    Struct,
    Enum,
    Protocol,
    Extension,
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct Raw {
    pub type_constructors: FxHashMap<TypeId, TypeDef>,
    pub protocols: FxHashMap<ProtocolId, TypeDef>,
    pub annotations: FxHashMap<NodeID, ASTTyRepr>,
    pub typealiases: FxHashMap<NodeID, (Name, TypeAnnotation)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeExtension {
    pub node_id: NodeID,
    pub conformances: Vec<ConformanceStub>,
    pub methods: IndexMap<Label, Method>,
    pub static_methods: IndexMap<Label, Method>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDef {
    pub name: Name,
    pub node_id: NodeID,
    pub kind: Kind,
    pub def: TypeDefKind,
    pub generics: IndexMap<Name, ASTTyRepr>,
    pub fields: TypeFields,
    pub extensions: Vec<TypeExtension>,
    pub conformances: Vec<ConformanceStub>,
    pub child_types: FxHashMap<String, Symbol>,
}

// new helper
#[derive(Debug, Clone)]
pub struct ProtocolBound {
    pub protocol_id: ProtocolId,
    pub args: Vec<Ty>, // concrete types the protocol is instantiated with, e.g. [Ty::Float]
}

#[derive(Debug)]
pub struct TypeSession {
    pub(super) vars: Vars,
    pub synthsized_ids: IDGenerator,
    pub term_env: TermEnv,
    pub meta_levels: FxHashMap<Meta, Level>,
    pub skolem_map: FxHashMap<Ty, Ty>,
    pub skolem_bounds: FxHashMap<SkolemId, Vec<TypeId>>,
    pub type_param_bounds: FxHashMap<TypeParamId, Vec<ProtocolBound>>,
    pub types_by_node: FxHashMap<NodeID, Ty>,
    pub typealiases: FxHashMap<Symbol, Scheme>,
    pub type_catalog: TypeCatalog,
}

impl Default for TypeSession {
    fn default() -> Self {
        let mut term_env = TermEnv {
            symbols: FxHashMap::default(),
        };

        for (sym, entry) in builtin_scope() {
            term_env.insert(sym, entry);
        }

        TypeSession {
            vars: Default::default(),
            synthsized_ids: Default::default(),
            skolem_map: Default::default(),
            meta_levels: Default::default(),
            term_env,
            type_param_bounds: Default::default(),
            skolem_bounds: Default::default(),
            types_by_node: Default::default(),
            typealiases: Default::default(),
            type_catalog: Default::default(),
        }
    }
}

pub struct Typed {}

impl TypeSession {
    pub fn drive(ast: &mut AST<NameResolved>) -> TypeSession {
        let mut session = TypeSession::default();
        let raw = TypeHeaderPass::drive(&mut session, ast);
        let _headers = TypeResolvePass::drive(ast, &mut session, raw);
        let mut scc = SCCResolved::default();
        DependenciesPass::drive(&mut session, ast, &mut scc);
        InferencePass::perform(&mut session, &scc, ast);
        session
    }

    #[instrument(skip(self))]
    pub fn generalize(&mut self, inner: Level, ty: Ty, unsolved: &[Constraint]) -> EnvEntry {
        // collect metas in ty
        let mut metas = FxHashSet::default();
        collect_meta(&ty, &mut metas);

        // Also collect metas that appear only in constraints
        for constraint in unsolved {
            collect_metas_in_constraint(constraint, &mut metas);
        }

        // keep only metas born at or above inner
        let mut foralls = vec![];
        let mut substitutions = UnificationSubstitutions::new(self.meta_levels.clone());
        for m in &metas {
            match m {
                Ty::Param(p) => {
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
                Ty::Record(box Row::Var(id))
                | Ty::Nominal {
                    row: box Row::Var(id),
                    ..
                } => {
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

        for c in unsolved {
            if let Constraint::HasField(h) = c {
                tracing::info!("got unsolved hasfield: {c:?}");
                let r = apply_row(h.row.clone(), &mut substitutions);
                if let Row::Var(row_meta) = r {
                    // quantify if its level is above the binder's level
                    let lvl = *self
                        .meta_levels
                        .get(&Meta::Row(row_meta))
                        .unwrap_or(&Level(0));
                    if lvl >= inner {
                        let param_id = self.vars.row_params.next_id();
                        foralls.push(ForAll::Row(param_id));
                        substitutions.row.insert(row_meta, Row::Param(param_id));
                    }
                }
            }
        }

        // De-skolemize
        let ty = substitute(ty, &self.skolem_map);
        let ty = apply(ty, &mut substitutions);

        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }

        let predicates = unsolved
            .iter()
            .map(|c| {
                let c = c.substitute(&self.skolem_map);

                c.into_predicate(&mut substitutions)
            })
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

        // 3) de-skolemize+apply again
        let ty = substitute(ty, &self.skolem_map);
        let ty = apply(ty, substitutions);

        // 4) build predicates from unsolved using *current substitutions*
        if foralls.is_empty() {
            return EnvEntry::Mono(ty);
        }
        let predicates = unsolved
            .iter()
            .map(|c| c.substitute(&self.skolem_map))
            .map(|c| c.into_predicate(substitutions))
            .collect();

        EnvEntry::Scheme(Scheme::new(foralls, predicates, ty))
    }

    // Handle converting Ty::TypeConstructor/Ty::TypeApplication to Ty::Nominal
    pub(super) fn normalize_nominals(&mut self, ty: &Ty, level: Level) -> Ty {
        let normalized = match ty.clone() {
            Ty::Nominal { .. } => ty.clone(),
            Ty::Constructor {
                type_id,
                params,
                ret,
            } => Ty::Constructor {
                type_id,
                params: params
                    .into_iter()
                    .map(|p| self.normalize_nominals(&p, level))
                    .collect(),
                ret: self.normalize_nominals(&ret, level).into(),
            },
            Ty::Func(box ty, box ty1) => Ty::Func(
                self.normalize_nominals(&ty, level).into(),
                self.normalize_nominals(&ty1, level).into(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|i| self.normalize_nominals(&i, level))
                    .collect(),
            ),
            Ty::Record(row) => Ty::Record(self.normalize_nominals_row(&row, level).into()),
            ty @ (Ty::Hole(..)
            | Ty::Primitive(..)
            | Ty::Param(..)
            | Ty::Rigid(..)
            | Ty::UnificationVar { .. }) => ty,
        };

        #[cfg(debug_assertions)]
        if normalized != *ty {
            tracing::trace!("normalize_nominal: {ty:?} -> {normalized:?}");
        }

        normalized
    }

    pub(super) fn normalize_nominals_row(&mut self, row: &Row, level: Level) -> Row {
        if let Row::Extend { box row, label, ty } = row.clone() {
            return Row::Extend {
                row: self.normalize_nominals_row(&row, level).into(),
                label,
                ty: self.normalize_nominals(&ty, level),
            };
        }

        row.clone()
    }

    pub(crate) fn new_type_param(&mut self) -> Ty {
        let id = self.vars.type_params.next_id();
        tracing::trace!("Fresh type param {id:?}");
        Ty::Param(id)
    }

    pub(crate) fn new_skolem(&mut self) -> Ty {
        let id = self.vars.skolems.next_id();
        tracing::trace!("Fresh skolem {id:?}");
        Ty::Rigid(id)
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

fn collect_metas_in_constraint(constraint: &Constraint, out: &mut FxHashSet<Ty>) {
    match constraint {
        Constraint::Equals(equals) => {
            collect_meta(&equals.lhs, out);
            collect_meta(&equals.rhs, out);
        }
        Constraint::Member(member) => {
            collect_meta(&member.receiver, out);
            collect_meta(&member.ty, out);
        }
        Constraint::Call(call) => {
            collect_meta(&call.callee, out);
            for argument in &call.args {
                collect_meta(argument, out);
            }
            if let Some(receiver) = &call.receiver {
                collect_meta(receiver, out);
            }
            collect_meta(&call.returns, out);
        }
        Constraint::Construction(construction) => {
            collect_meta(&construction.callee, out);
            for argument in &construction.args {
                collect_meta(argument, out);
            }
            collect_meta(&construction.returns, out);
        }
        Constraint::HasField(has_field) => {
            // The row meta is handled in your existing HasField block later.
            collect_meta(&has_field.ty, out);
        }
        Constraint::Conforms(_) => {
            // No direct metas to generalize here.
        }
        Constraint::AssociatedEquals(associated_equals) => {
            collect_meta(&associated_equals.output, out);
            collect_meta(&associated_equals.subject, out);
        }
        Constraint::TypeMember(c) => {
            collect_meta(&c.base, out);
            collect_meta(&c.result, out);
            for ty in &c.generics {
                collect_meta(ty, out);
            }
        }
    }
}
