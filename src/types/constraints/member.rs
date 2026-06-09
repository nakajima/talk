use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{
            constraint::ConstraintCause,
            store::{ConstraintId, ConstraintStore},
        },
        infer_row::Row,
        infer_ty::{Meta, Ty},
        passes::uncurry_function,
        predicate::Predicate,
        solve_context::SolveContext,
        type_args::TypeArgs,
        type_error::TypeError,
        type_operations::{curry, unify},
        type_session::{MetaOrigin, TypeSession},
    },
};

fn is_function_show(label: &Label) -> bool {
    matches!(label, Label::Named(name) if name == "show")
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Member {
    pub id: ConstraintId,
    pub node_id: NodeID,
    pub receiver: Ty,
    pub label: Label,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemberCall {
    pub id: ConstraintId,
    pub member_node_id: NodeID,
    pub call_node_id: NodeID,
    pub receiver: Ty,
    pub self_ty: Ty,
    pub label: Label,
    pub ty: Ty,
    pub returns: Ty,
    pub infer_receiver_from_return: bool,
}

impl Member {
    #[instrument(skip(constraints, context, session))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        MemberLookup::access(self).solve(constraints, context, session)
    }
}

impl MemberCall {
    #[instrument(skip(constraints, context, session))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        MemberLookup::call(self).solve(constraints, context, session)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum MemberUse {
    Access {
        node_id: NodeID,
    },
    Call {
        member_node_id: NodeID,
        call_node_id: NodeID,
        self_ty: Ty,
        returns: Ty,
        infer_receiver_from_return: bool,
    },
}

impl MemberUse {
    fn member_node_id(&self) -> NodeID {
        match self {
            Self::Access { node_id } => *node_id,
            Self::Call { member_node_id, .. } => *member_node_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MemberLookup {
    id: ConstraintId,
    receiver: Ty,
    label: Label,
    ty: Ty,
    use_site: MemberUse,
}

impl MemberLookup {
    fn access(member: &Member) -> Self {
        Self {
            id: member.id,
            receiver: member.receiver.clone(),
            label: member.label.clone(),
            ty: member.ty.clone(),
            use_site: MemberUse::Access {
                node_id: member.node_id,
            },
        }
    }

    fn call(member_call: &MemberCall) -> Self {
        Self {
            id: member_call.id,
            receiver: member_call.receiver.clone(),
            label: member_call.label.clone(),
            ty: member_call.ty.clone(),
            use_site: MemberUse::Call {
                member_node_id: member_call.member_node_id,
                call_node_id: member_call.call_node_id,
                self_ty: member_call.self_ty.clone(),
                returns: member_call.returns.clone(),
                infer_receiver_from_return: member_call.infer_receiver_from_return,
            },
        }
    }

    fn member_node_id(&self) -> NodeID {
        self.use_site.member_node_id()
    }

    fn cause(&self) -> ConstraintCause {
        ConstraintCause::Member(self.member_node_id())
    }

    fn call_node_id(&self) -> Option<NodeID> {
        match self.use_site {
            MemberUse::Access { .. } => None,
            MemberUse::Call { call_node_id, .. } => Some(call_node_id),
        }
    }

    fn record_method_callee(&self, session: &mut TypeSession, symbol: Symbol, type_args: TypeArgs) {
        if let MemberUse::Call {
            call_node_id,
            ref self_ty,
            ..
        } = self.use_site
        {
            session.record_method_callee(call_node_id, symbol, self_ty.clone(), type_args);
        }
    }

    fn record_function_callee(
        &self,
        session: &mut TypeSession,
        symbol: Symbol,
        type_args: TypeArgs,
    ) {
        if let Some(call_node_id) = self.call_node_id() {
            session.record_function_callee(call_node_id, symbol, type_args);
        }
    }

    fn record_variant_callee(
        &self,
        session: &mut TypeSession,
        enum_symbol: Symbol,
        variant: Symbol,
        type_args: TypeArgs,
    ) {
        if let Some(call_node_id) = self.call_node_id() {
            session.record_variant_callee(call_node_id, enum_symbol, variant, type_args);
        }
    }

    fn infer_receiver_from_return(
        &self,
        receiver_meta: Meta,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Option<SolveResult> {
        let MemberUse::Call {
            ref returns,
            infer_receiver_from_return,
            ..
        } = self.use_site
        else {
            return None;
        };
        if !infer_receiver_from_return {
            return None;
        }

        let returns = session.apply(returns, &mut context.substitutions_mut());
        if matches!(returns, Ty::Nominal { .. })
            && let Ok(metas) = unify(&self.receiver, &returns, context, session)
        {
            return Some(SolveResult::Solved(metas));
        }
        if let Ty::Var { id, .. } = returns {
            return Some(SolveResult::Defer(DeferralReason::Multi(vec![
                DeferralReason::WaitingOnMeta(receiver_meta),
                DeferralReason::WaitingOnMeta(Meta::Ty(id)),
            ])));
        }

        None
    }

    #[instrument(skip(self, constraints, context, session))]
    fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        let receiver = self.receiver.clone();
        let ty = self.ty.clone();

        match &receiver {
            Ty::Var { id, .. } => {
                if let Some(Ty::Param(param_id, bounds)) = session.lookup_type_param_origin(*id)
                    && let SolveResult::Solved(metas) = self.lookup_type_param_member(
                        constraints,
                        context,
                        session,
                        &ty,
                        param_id,
                        &bounds,
                    )
                {
                    return SolveResult::Solved(metas);
                }

                if let Some(result) =
                    self.infer_receiver_from_return(Meta::Ty(*id), context, session)
                {
                    return result;
                }

                tracing::trace!("waiting on meta {id:?}");
                SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)))
            }
            Ty::Rigid(id) => {
                let Some(Ty::Param(type_param_id, bounds)) =
                    session.skolem_map.get(&Ty::Rigid(*id))
                else {
                    unreachable!();
                };
                let type_param_id = *type_param_id;
                let bounds = bounds.clone();

                self.lookup_type_param_member(
                    constraints,
                    context,
                    session,
                    &ty,
                    type_param_id,
                    &bounds,
                )
            }
            Ty::Param(id, bounds) => {
                self.lookup_type_param_member(constraints, context, session, &ty, *id, bounds)
            }
            Ty::Constructor { name, .. } => self.lookup_constructor_member(
                constraints,
                context,
                session,
                &name.symbol().unwrap_or_else(|_| unreachable!()),
            ),
            Ty::Record(_, box row) => {
                constraints._has_field(
                    (*row).clone(),
                    self.label.clone(),
                    ty,
                    Some(self.member_node_id()),
                    &constraints.copy_group(self.id),
                );
                SolveResult::Solved(Default::default())
            }
            Ty::Primitive(symbol) => self.lookup_nominal_member(
                constraints,
                context,
                session,
                symbol,
                Default::default(),
            ),
            Ty::Nominal { symbol, type_args } => {
                self.lookup_nominal_member(constraints, context, session, symbol, type_args)
            }
            Ty::Func(..) => {
                if is_function_show(&self.label) {
                    let method_ty =
                        Ty::Func(Ty::Void.into(), Ty::String().into(), Row::Empty.into());
                    if let Ok(metas) = unify(&method_ty, &ty, context, session) {
                        return SolveResult::Solved(metas);
                    }
                }
                SolveResult::Defer(DeferralReason::Unknown)
            }
            _ => SolveResult::Defer(DeferralReason::Unknown),
        }
    }

    #[instrument(skip(self, context, session, constraints))]
    fn lookup_type_param_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        ty: &Ty,
        type_param: Symbol,
        bounds: &[ProtocolId],
    ) -> SolveResult {
        let mut solved_metas: Vec<Meta> = Default::default();
        let cause = self.cause();

        let mut candidates: Vec<ProtocolId> = bounds.to_vec();
        for given in context.givens_mut().iter() {
            if let Predicate::Conforms {
                param, protocol_id, ..
            } = given
                && param == &type_param
                && !candidates.contains(protocol_id)
            {
                candidates.push(*protocol_id);
            }
        }

        let matching_methods: Vec<(ProtocolId, Symbol)> = candidates
            .iter()
            .filter_map(|protocol_id| {
                session
                    .lookup_member(&(*protocol_id).into(), &self.label)
                    .map(|(req, _source)| (*protocol_id, req))
            })
            .collect();

        if matching_methods.is_empty() {
            return SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        }

        let mut unique_methods = Vec::new();
        for method in matching_methods {
            if unique_methods
                .iter()
                .any(|(_, existing_req)| existing_req == &method.1)
            {
                continue;
            }
            unique_methods.push(method);
        }

        if unique_methods.len() > 1 {
            return SolveResult::Err(TypeError::AmbiguousMember(
                self.receiver.clone(),
                self.label.clone(),
            ));
        }

        let (protocol_id, req) = &unique_methods[0];
        let Some(entry) = session.lookup(req) else {
            return SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        let instantiated = entry.instantiate(self.member_node_id(), constraints, context, session);
        let (req_self, req_func) = consume_self(&instantiated.value);

        match unify(&req_self, &self.receiver, context, session).map_err(|e| e.with_cause(cause)) {
            Ok(metas) => solved_metas.extend(metas),
            Err(e) => return SolveResult::Err(e),
        }

        match unify(ty, &req_func, context, session).map_err(|e| e.with_cause(cause)) {
            Ok(metas) => solved_metas.extend(metas),
            Err(e) => return SolveResult::Err(e),
        };

        if matches!(self.use_site, MemberUse::Call { .. }) {
            let mut substitutions = context.substitutions_mut();
            let type_args = TypeArgs {
                ty: instantiated
                    .type_args
                    .ty
                    .iter()
                    .map(|(param, ty)| (*param, session.apply(ty, &mut substitutions)))
                    .collect(),
                row: instantiated
                    .type_args
                    .row
                    .iter()
                    .map(|(param, row)| (*param, session.apply_row(row, &mut substitutions)))
                    .collect(),
            };
            drop(substitutions);
            self.record_method_callee(session, *req, type_args);
        }

        tracing::trace!(
            "Chose protocol {:?} for member {} at {:?}",
            protocol_id,
            self.label,
            self.member_node_id()
        );

        SolveResult::Solved(solved_metas)
    }

    #[instrument(skip(self, context, session, constraints))]
    fn lookup_constructor_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        nominal_symbol: &Symbol,
    ) -> SolveResult {
        let cause = self.cause();
        let Some(member_sym) = session.lookup_constructor_member(nominal_symbol, &self.label)
        else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*nominal_symbol));
        };

        let instantiated = session
            .lookup(&member_sym)
            .map(|entry| entry.instantiate(self.member_node_id(), constraints, context, session));
        let mut member_ty = if let Some(instantiated) = instantiated.as_ref() {
            instantiated.value.clone()
        } else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(member_sym));
        };

        if let Symbol::Variant(..) = member_sym {
            let Some(nominal) = session.lookup_nominal(nominal_symbol) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*nominal_symbol));
            };

            let mut variant_type_args = TypeArgs::default();
            for param in nominal.type_params.iter() {
                let Ty::Param(param_id, bounds) = param else {
                    continue;
                };

                let Ty::Var { id: meta, level } = session.new_ty_meta_var_with_origin(
                    context.level(),
                    Some(MetaOrigin::TypeParam {
                        param: *param_id,
                        bounds: bounds.clone(),
                    }),
                ) else {
                    unreachable!();
                };
                variant_type_args
                    .ty
                    .insert(*param_id, Ty::Var { id: meta, level });
            }
            self.record_variant_callee(
                session,
                *nominal_symbol,
                member_sym,
                variant_type_args.clone(),
            );

            let Some(variant) = nominal.variants.get(&self.label) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(member_sym));
            };

            member_ty = if let Some(enum_entry) = session.lookup(nominal_symbol) {
                let enum_ty = variant_type_args.apply(enum_entry._as_ty());

                match variant.len() {
                    0 => enum_ty,
                    _ => {
                        let instantiated_variants: Vec<_> = variant
                            .iter()
                            .map(|v| variant_type_args.apply(v.clone()))
                            .collect();
                        curry(instantiated_variants, enum_ty, Row::Empty.into())
                    }
                }
            } else {
                Ty::Error(
                    TypeError::TypeNotFound(format!(
                        "{nominal_symbol:?} while looking up constructor member {:?}",
                        self.label
                    ))
                    .into(),
                )
            };
        } else if matches!(
            member_sym,
            Symbol::InstanceMethod(..) | Symbol::MethodRequirement(..)
        ) {
            let type_args = instantiated
                .as_ref()
                .map(|instantiated| instantiated.type_args.clone())
                .unwrap_or_default();
            self.record_method_callee(session, member_sym, type_args);
        } else {
            let type_args = instantiated
                .as_ref()
                .map(|instantiated| instantiated.type_args.clone())
                .unwrap_or_default();
            self.record_function_callee(session, member_sym, type_args);
        }

        if let Symbol::Struct(..) = member_sym {
            member_ty = Ty::Constructor {
                name: crate::name::Name::Resolved(member_sym, self.label.to_string()),
                params: vec![],
                ret: session.new_ty_meta_var(context.level()).into(),
            };
        }

        match unify(&member_ty, &self.ty, context, session).map_err(|e| e.with_cause(cause)) {
            Ok(vars) => SolveResult::Solved(vars),
            Err(e) => SolveResult::Err(e),
        }
    }

    #[instrument(skip(self, context, session, constraints), fields(label = self.label.to_string()))]
    fn lookup_nominal_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        symbol: &Symbol,
        type_args: &[Ty],
    ) -> SolveResult {
        let mut solved_metas: Vec<Meta> = Default::default();
        let cause = self.cause();

        let Some(nominal) = session.lookup_nominal(symbol) else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*symbol));
        };

        if let Some((member_sym, _source)) = session.lookup_member(symbol, &self.label) {
            match member_sym {
                Symbol::InstanceMethod(..) | Symbol::MethodRequirement(..) => {
                    let Some(entry) = session.lookup(&member_sym) else {
                        return SolveResult::Err(TypeError::MemberNotFound(
                            self.receiver.clone(),
                            self.label.to_string(),
                        ));
                    };

                    let instantiated =
                        entry.instantiate(self.member_node_id(), constraints, context, session);
                    self.record_method_callee(session, member_sym, instantiated.type_args.clone());
                    let method =
                        session.apply(&instantiated.value, &mut context.substitutions_mut());
                    let (method_receiver, method_fn) = consume_self(&method);

                    match unify(&method_receiver, &self.receiver, context, session)
                        .map_err(|e| e.with_cause(cause))
                    {
                        Ok(metas) => solved_metas.extend(metas),
                        Err(e) => return SolveResult::Err(e),
                    };

                    match unify(&method_fn, &self.ty, context, session)
                        .map_err(|e| e.with_cause(cause))
                    {
                        Ok(metas) => solved_metas.extend(metas),
                        Err(e) => return SolveResult::Err(e),
                    };

                    return SolveResult::Solved(solved_metas);
                }
                Symbol::Variant(..) => {
                    let Some(values) = nominal
                        .substituted_variant_values(type_args)
                        .get(&self.label)
                        .cloned()
                    else {
                        return SolveResult::Err(TypeError::MemberNotFound(
                            self.receiver.clone(),
                            self.label.to_string(),
                        ));
                    };

                    self.record_variant_callee(session, *symbol, member_sym, TypeArgs::default());

                    let constructor_ty = match values.len() {
                        0 => self.receiver.clone(),
                        _ => curry(values, self.receiver.clone(), Row::Empty.into()),
                    };

                    let group = constraints.copy_group(self.id);
                    constraints.wants_equals_at_with_cause(
                        self.member_node_id(),
                        constructor_ty,
                        self.ty.clone(),
                        &group,
                        Some(cause),
                    );
                    return SolveResult::Solved(Default::default());
                }
                Symbol::StaticMethod(..) => {
                    return self.lookup_constructor_member(constraints, context, session, symbol);
                }
                _ => (),
            }
        }

        if let Some((_protocol_id, member_sym)) =
            session.claimed_protocol_member(*symbol, &self.label)
        {
            let Some(entry) = session.lookup(&member_sym) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(member_sym));
            };

            let instantiated =
                entry.instantiate(self.member_node_id(), constraints, context, session);
            self.record_method_callee(session, member_sym, instantiated.type_args.clone());
            let method = session.apply(&instantiated.value, &mut context.substitutions_mut());
            let (method_receiver, method_fn) = consume_self(&method);

            match unify(&method_receiver, &self.receiver, context, session)
                .map_err(|e| e.with_cause(cause))
            {
                Ok(metas) => solved_metas.extend(metas),
                Err(e) => return SolveResult::Err(e),
            };

            match unify(&method_fn, &self.ty, context, session).map_err(|e| e.with_cause(cause)) {
                Ok(metas) => solved_metas.extend(metas),
                Err(e) => return SolveResult::Err(e),
            };

            return SolveResult::Solved(solved_metas);
        }

        if let Some(ty) = nominal
            .substitute_properties(type_args)
            .get(&self.label)
            .cloned()
        {
            if let Some((member, _)) = session.lookup_member(symbol, &self.label) {
                self.record_method_callee(session, member, TypeArgs::default());
            }
            match unify(&self.ty, &ty, context, session).map_err(|e| e.with_cause(cause)) {
                Ok(vars) => SolveResult::Solved(vars),
                Err(e) => SolveResult::Err(e),
            }
        } else {
            SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ))
        }
    }
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub fn consume_self(method: &Ty) -> (Ty, Ty) {
    assert!(
        matches!(method, Ty::Func(..)),
        "didn't get func to consume self"
    );
    let (mut params, ret, effects) = uncurry_function(method.clone());
    let method_receiver = params.remove(0);
    if params.is_empty() {
        // We need to make sure there's at least one param or else curry doesn't return a func.
        params.insert(0, Ty::Void);
    }
    (method_receiver, curry(params, ret, effects.into()))
}
