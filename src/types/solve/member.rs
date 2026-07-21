use super::*;
use crate::types::ty::Perm;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum MemberDispatch {
    Handled,
    NoCandidate,
    Stuck,
}

impl<'s> Solver<'s> {
    /// One step on a HasMember predicate against a known head.
    /// Dispatch a member use through the protocols that could provide it.
    /// Returns true when handled: exactly one distinct requirement binds
    /// (instances with contexts — Hall et al., TOPLAS 1996); several emit
    /// an ambiguity error naming the protocol-static forms (`P.m(x)`)
    /// that pick one, since committing to any would make meaning depend
    /// on table order (overlapping instances — Jones, *Qualified Types*,
    /// 1994, §2.4). Zero candidates fall through to the caller.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn dispatch_member_through(
        &mut self,
        protocols: &[ProtocolRef],
        head: Option<Symbol>,
        lookup_receiver: &Ty,
        self_receiver: &Ty,
        label: &str,
        member: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> MemberDispatch {
        let mut candidates: Vec<(ProtocolRef, ProtocolRef, Requirement)> = vec![];
        for protocol in protocols {
            let Some((owner, requirement)) = self.catalog.requirement_in_ref(protocol, label)
            else {
                continue;
            };
            // Two protocols inheriting one base share its requirement —
            // that is one candidate, not an ambiguity.
            if candidates
                .iter()
                .any(|(_, _, r)| r.symbol == requirement.symbol)
            {
                continue;
            }
            candidates.push((protocol.clone(), owner, requirement.clone()));
        }
        if candidates.len() > 1 {
            let filtered: Vec<_> = candidates
                .iter()
                .filter(|(protocol, owner, requirement)| {
                    self.requirement_accepts_member_shape(
                        protocol,
                        owner,
                        requirement,
                        lookup_receiver,
                        member,
                    )
                })
                .cloned()
                .collect();
            if !filtered.is_empty() {
                candidates = filtered;
            }
        }
        match candidates.as_slice() {
            [] => MemberDispatch::NoCandidate,
            [(protocol, owner, requirement)] => {
                let evidence =
                    self.evidence_for_requirement(head, lookup_receiver, protocol, label);
                self.bind_requirement(
                    owner.clone(),
                    requirement,
                    lookup_receiver,
                    self_receiver,
                    member,
                    origin,
                    queue,
                    evidence,
                );
                MemberDispatch::Handled
            }
            many => {
                let rendered = self.store.render(self_receiver);
                let member = self.store.shallow(member);
                let member_shape_stuck = match &member {
                    Ty::Var(_) => true,
                    Ty::Func(params, _, _) => params.iter().any(Ty::has_unification_vars),
                    _ => false,
                };
                if member_shape_stuck {
                    return MemberDispatch::Stuck;
                }
                self.errors.push((
                    TypeError::AmbiguousMember {
                        receiver: rendered,
                        label: label.to_string(),
                        candidates: many.iter().map(|(p, ..)| p.to_string()).collect(),
                    },
                    origin.node,
                ));
                MemberDispatch::Handled
            }
        }
    }

    fn evidence_for_requirement(
        &mut self,
        head: Option<Symbol>,
        lookup_receiver: &Ty,
        protocol: &ProtocolRef,
        label: &str,
    ) -> Option<(
        crate::types::catalog::ConformanceId,
        Option<Symbol>,
        Vec<(Symbol, Ty)>,
    )> {
        let receiver = self.store.shallow(lookup_receiver);
        if receiver.has_unification_vars() || matches!(receiver, Ty::Param(_)) {
            return None;
        }
        let matches = if let Some(head) = head
            && let Ty::Nominal(_, args) = &receiver
        {
            self.catalog.matching_conformances(head, args, protocol)
        } else {
            self.catalog
                .matching_protocol_head_conformances(&receiver, protocol)
        };
        let [matched] = matches.as_slice() else {
            return None;
        };
        let witness = matched.conformance.witnesses.get(label).copied();
        let mut substitution = matched.evidence_substitution();
        substitution.push((protocol.protocol, receiver));
        if let Some(info) = self.catalog.protocols.get(&protocol.protocol) {
            substitution.extend(
                info.params
                    .iter()
                    .zip(&protocol.args)
                    .map(|(param, arg)| (param.symbol, arg.clone())),
            );
        }
        Some((matched.id, witness, substitution))
    }

    fn protocol_owner_refs(&mut self, label: &str, node: NodeID) -> Vec<ProtocolRef> {
        let Some(owners) = self.catalog.member_owners.get(label) else {
            return vec![];
        };
        owners
            .iter()
            .filter_map(|owner| match owner {
                MemberOwner::Protocol(protocol) => Some(*protocol),
                MemberOwner::Nominal(_) => None,
            })
            .map(|protocol| {
                let args = self
                    .catalog
                    .protocols
                    .get(&protocol)
                    .map(|info| {
                        info.params
                            .iter()
                            .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                            .collect()
                    })
                    .unwrap_or_default();
                ProtocolRef { protocol, args }
            })
            .collect()
    }

    fn requirement_accepts_member_shape(
        &mut self,
        protocol: &ProtocolRef,
        owner: &ProtocolRef,
        requirement: &Requirement,
        lookup_receiver: &Ty,
        member: &Ty,
    ) -> bool {
        let member = self.store.shallow(member);
        let Ty::Func(member_params, _, _) = member else {
            return true;
        };
        let Some(scheme) = self.schemes.get(&requirement.symbol) else {
            return true;
        };
        let owner_app = ProtocolApplication::new(lookup_receiver.clone(), owner.clone());
        let mut tys = owner_app.substitution(self.catalog);
        if owner.protocol != protocol.protocol {
            let protocol_app = ProtocolApplication::new(lookup_receiver.clone(), protocol.clone());
            tys.extend(protocol_app.substitution(self.catalog));
        }
        for param in &scheme.params {
            tys.entry(param.symbol).or_insert(Ty::Param(param.symbol));
        }
        let signature = scheme
            .ty
            .substitute(&tys, &Default::default(), &Default::default());
        let Ty::Func(requirement_params, _, _) = signature else {
            return true;
        };
        let requirement_params = requirement_params.into_iter().skip(1).collect::<Vec<_>>();
        if requirement_params.len() != member_params.len() {
            return false;
        }
        requirement_params
            .iter()
            .zip(member_params.iter())
            .all(|(expected, actual)| {
                let mut bindings = FxHashMap::default();
                match_pattern(expected, actual, &mut bindings) || {
                    let mut reverse_bindings = FxHashMap::default();
                    match_pattern(actual, expected, &mut reverse_bindings)
                }
            })
    }

    pub(super) fn try_member(
        &mut self,
        receiver: Ty,
        label: Label,
        member: Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let label_str = label.to_string();
        let (member_receiver, self_receiver) = self.member_receivers(&receiver);
        let diagnostic_receiver = self_receiver.clone();
        if stuck_projection(self.store, &member_receiver) {
            return Some(Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            });
        }

        match member_receiver.clone() {
            Ty::Var(_) => Some(Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            }),
            Ty::Error => None,
            // Members of an irreducible projection dispatch through the
            // bounds declared on the associated type.
            Ty::Proj(_, _, assoc_symbol) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&assoc_symbol)
                    .cloned()
                    .unwrap_or_default();
                match self.dispatch_member_through(
                    &bounds,
                    None,
                    &member_receiver,
                    &self_receiver,
                    &label_str,
                    &member,
                    origin,
                    queue,
                ) {
                    MemberDispatch::Handled => return None,
                    MemberDispatch::Stuck => {
                        return Some(Constraint::HasMember {
                            receiver,
                            label,
                            member,
                            origin,
                        });
                    }
                    MemberDispatch::NoCandidate => {}
                }
                let owner_protocols = self.protocol_owner_refs(&label_str, origin.node);
                if !owner_protocols.is_empty() {
                    match self.dispatch_member_through(
                        &owner_protocols,
                        None,
                        &member_receiver,
                        &self_receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        MemberDispatch::Handled => return None,
                        MemberDispatch::Stuck => {
                            return Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            });
                        }
                        MemberDispatch::NoCandidate => {}
                    }
                }
                let rendered = self.store.render(&diagnostic_receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            // Tuple element access: `.0`, `.1`, ... extract by position.
            Ty::Tuple(items) => {
                let index = label_str.parse::<usize>().ok();
                match index.and_then(|index| items.get(index)) {
                    Some(item) => {
                        queue.push(Constraint::Eq(member, item.clone(), origin));
                    }
                    None => {
                        let rendered = self.store.render(&diagnostic_receiver);
                        self.errors.push((
                            TypeError::UnknownMember {
                                receiver: rendered,
                                label: label_str,
                            },
                            origin.node,
                        ));
                    }
                }
                None
            }
            // Structural access via an open-row equality (Leijen 2005):
            // present fields hit; absent fields on a closed row are a row
            // mismatch.
            Ty::Record(_) => {
                let tail = self.store.fresh_row(self.level, origin.node);
                let probe = Ty::Record(Row {
                    fields: vec![(Label::Named(label_str), member)],
                    tail: Some(RowTail::Var(tail)),
                });
                queue.push(Constraint::Eq(member_receiver.clone(), probe, origin));
                None
            }
            Ty::Param(param) => {
                let mut bounds = self
                    .catalog
                    .param_bounds
                    .get(&param)
                    .cloned()
                    .unwrap_or_default();
                bounds.extend(self.given_protocols_for(&member_receiver));
                match self.dispatch_member_through(
                    &bounds,
                    None,
                    &member_receiver,
                    &self_receiver,
                    &label_str,
                    &member,
                    origin,
                    queue,
                ) {
                    MemberDispatch::Handled => return None,
                    MemberDispatch::Stuck => {
                        return Some(Constraint::HasMember {
                            receiver,
                            label,
                            member,
                            origin,
                        });
                    }
                    MemberDispatch::NoCandidate => {}
                }
                let owner_protocols = self.protocol_owner_refs(&label_str, origin.node);
                if !owner_protocols.is_empty() {
                    match self.dispatch_member_through(
                        &owner_protocols,
                        None,
                        &member_receiver,
                        &self_receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        MemberDispatch::Handled => return None,
                        MemberDispatch::Stuck => {
                            return Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            });
                        }
                        MemberDispatch::NoCandidate => {}
                    }
                }
                let rendered = self.store.render(&diagnostic_receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            Ty::Any { protocol, .. } => {
                if let Some((owner, requirement)) =
                    self.catalog.requirement_in_ref(&protocol, &label_str)
                {
                    let requirement = requirement.clone();
                    self.bind_requirement(
                        owner,
                        &requirement,
                        &member_receiver,
                        &self_receiver,
                        &member,
                        origin,
                        queue,
                        None,
                    );
                    return None;
                }
                let owner_protocols = self.protocol_owner_refs(&label_str, origin.node);
                if !owner_protocols.is_empty() {
                    match self.dispatch_member_through(
                        &owner_protocols,
                        None,
                        &member_receiver,
                        &self_receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        MemberDispatch::Handled => return None,
                        MemberDispatch::Stuck => {
                            return Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            });
                        }
                        MemberDispatch::NoCandidate => {}
                    }
                }
                let rendered = self.store.render(&diagnostic_receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            Ty::Nominal(symbol, args) => {
                if let Some(info) = self.catalog.structs.get(&symbol) {
                    let substitution: FxHashMap<Symbol, Ty> = info
                        .params
                        .iter()
                        .map(|param| param.symbol)
                        .zip(args.iter().cloned())
                        .collect();
                    if let Some((property, field_ty)) = info.fields.get(&label_str) {
                        // A closure field's row is THIS instance's: splice
                        // the head's trailing `Ty::Eff` args over the
                        // field's quantified tails. A head without eff
                        // args (an annotation or import that never met a
                        // construction) reads with fresh rows instead.
                        let mut eff_args = args
                            .iter()
                            .filter_map(|arg| match arg {
                                Ty::Eff(row) => Some(row.clone()),
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            .into_iter();
                        let eff_rows: FxHashMap<Symbol, EffectRow> = info
                            .eff_params
                            .iter()
                            .map(|&param| {
                                let row = eff_args.next().unwrap_or_else(|| {
                                    EffectRow::open(self.store.fresh_eff(self.level, origin.node))
                                });
                                (param, row)
                            })
                            .collect();
                        let field_ty = field_ty
                            .substitute(&substitution, &Default::default(), &Default::default())
                            .substitute_eff_rows(&eff_rows);
                        queue.push(Constraint::Eq(member, field_ty, origin));
                        self.member_resolutions
                            .insert(origin.node, MemberResolution::Direct(*property));
                        return None;
                    }
                    if let Some(&method) = info.methods.get(&label_str) {
                        return self.dispatch_nominal_method(
                            method,
                            &substitution,
                            self_receiver.clone(),
                            label,
                            member,
                            origin,
                            queue,
                        );
                    }
                }
                // Methods on enums dispatch exactly like struct methods:
                // instantiate the (possibly generic) scheme, pin self,
                // and the member is the self-dropped signature.
                if let Some(info) = self.catalog.enums.get(&symbol)
                    && let Some(&method) = info.methods.get(&label_str)
                {
                    let substitution: FxHashMap<Symbol, Ty> = info
                        .params
                        .iter()
                        .map(|param| param.symbol)
                        .zip(args.iter().cloned())
                        .collect();
                    return self.dispatch_nominal_method(
                        method,
                        &substitution,
                        self_receiver.clone(),
                        label,
                        member,
                        origin,
                        queue,
                    );
                }
                // `clone` is a real marker-protocol requirement, but its
                // implementation is compiler-provided because retaining an
                // arbitrary Self is not expressible in user code.
                let clone_protocol = if self.catalog.cheap_clone_rows(symbol, &args) {
                    Some(Symbol::CheapClone)
                } else if self.catalog.grade_of(symbol) == crate::types::catalog::Grade::Copy {
                    Some(Symbol::Copy)
                } else {
                    None
                };
                if label_str == "clone"
                    && let Some(protocol) = clone_protocol
                    && let Some((_, requirement)) = self.catalog.requirement_in(protocol, "clone")
                {
                    let requirement_symbol = requirement.symbol;
                    queue.push(Constraint::Eq(
                        member,
                        Ty::Func(
                            vec![],
                            Box::new(member_receiver.clone()),
                            EffectRow::open(self.store.fresh_eff(self.level, origin.node)),
                        ),
                        origin,
                    ));
                    self.member_resolutions
                        .insert(origin.node, MemberResolution::Direct(requirement_symbol));
                    return None;
                }
                // Members provided through conformances (extend witnesses):
                // type via the protocol requirement, which is always valid if
                // the conformance is (the witness is checked against the
                // requirement when the extend body is checked).
                if self.catalog.conformances_by_head.contains_key(&symbol) {
                    let mut protocols = self
                        .catalog
                        .conformances_for_head(symbol)
                        .map(|(_, row)| row.protocol.clone())
                        .collect::<Vec<_>>();
                    protocols.dedup();
                    match self.dispatch_member_through(
                        &protocols,
                        Some(symbol),
                        &member_receiver,
                        &self_receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        MemberDispatch::Handled => return None,
                        MemberDispatch::Stuck => {
                            return Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            });
                        }
                        MemberDispatch::NoCandidate => {}
                    }
                }
                // Auto-derived protocol members (`optional.show()` or
                // `point.equals(rhs:)` without an explicit conformance):
                // dispatch through the requirement at the protocol's
                // defaulted application for this concrete Self type.
                let is_derivable_head = self.catalog.structs.contains_key(&symbol)
                    || self.catalog.enums.contains_key(&symbol);
                if is_derivable_head {
                    let self_ty = Ty::Nominal(symbol, args.clone());
                    for protocol in self.catalog.derivable.clone() {
                        let Some(protocol) = self.catalog.derived_protocol_ref(protocol, &self_ty)
                        else {
                            continue;
                        };
                        if let Some((owner, requirement)) =
                            self.catalog.requirement_in_ref(&protocol, &label_str)
                        {
                            let requirement = requirement.clone();
                            self.bind_requirement(
                                owner,
                                &requirement,
                                &member_receiver,
                                &self_receiver,
                                &member,
                                origin,
                                queue,
                                None,
                            );
                            return None;
                        }
                    }
                }
                // Inherent extend members (`extend Float { func _trunc() }`).
                // The head application binds the extend's rigid params;
                // everything quantified (method generics, effect rows)
                // freshens through the member's scheme like any callable.
                if let Some(members) = self.catalog.extend_members.get(&symbol)
                    && members.contains_key(&label_str)
                    && args.iter().any(Ty::has_unification_vars)
                {
                    return Some(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                }
                if let Some(members) = self.catalog.extend_members.get(&symbol)
                    && let Some(inherent) = members.get(&label_str)
                    && {
                        let mut probe = FxHashMap::default();
                        inherent
                            .self_args
                            .iter()
                            .zip(&args)
                            .all(|(pattern, actual)| match_pattern(pattern, actual, &mut probe))
                    }
                {
                    let inherent = inherent.clone();
                    let scheme = self.schemes.get(&inherent.symbol).cloned()?;
                    let mut substitution: FxHashMap<Symbol, Ty> = FxHashMap::default();
                    for (pattern, actual) in inherent.self_args.iter().zip(&args) {
                        bind_param_pattern(pattern, actual, &mut substitution);
                    }
                    for param in &scheme.params {
                        let var = Ty::Var(self.store.fresh_ty(self.level, origin.node));
                        self.instantiations
                            .entry(origin.node)
                            .or_default()
                            .push((param.symbol, var.clone()));
                        substitution.insert(param.symbol, var);
                    }
                    let mut effs = FxHashMap::default();
                    effs.insert(
                        inherent.symbol,
                        EffTail::Var(self.store.fresh_eff(self.level, origin.node)),
                    );
                    for param in &scheme.eff_params {
                        effs.insert(
                            *param,
                            EffTail::Var(self.store.fresh_eff(self.level, origin.node)),
                        );
                    }
                    for predicate in &scheme.predicates {
                        queue.push(
                            predicate
                                .substitute(&substitution, &effs, &Default::default())
                                .into_constraint(origin),
                        );
                    }
                    let signature = scheme
                        .ty
                        .substitute(&substitution, &effs, &Default::default());
                    if let Ty::Func(params, ret, eff) = signature
                        && !params.is_empty()
                    {
                        self.push_immediate_argument_eq(
                            queue,
                            params[0].clone(),
                            self_receiver.clone(),
                            origin,
                        );
                        queue.push(Constraint::Eq(
                            Ty::Func(params[1..].to_vec(), ret, eff),
                            member,
                            origin,
                        ));
                        // Publish the instance-head bindings (the extend's
                        // rigid params at the receiver's application).
                        self.instantiations
                            .entry(origin.node)
                            .or_default()
                            .extend(substitution.iter().map(|(s, t)| (*s, t.clone())));
                        self.member_resolutions
                            .insert(origin.node, MemberResolution::Direct(inherent.symbol));
                    }
                    return None;
                }
                // Copy/CheapClone both declare `clone`, but neither should
                // make the method visible on a type that conforms to neither.
                if label_str == "clone" && clone_protocol.is_none() {
                    let rendered = self.store.render(&diagnostic_receiver);
                    self.errors.push((
                        TypeError::UnknownMember {
                            receiver: rendered,
                            label: label_str,
                        },
                        origin.node,
                    ));
                    return None;
                }
                let owner_protocols = self.protocol_owner_refs(&label_str, origin.node);
                if !owner_protocols.is_empty() {
                    match self.dispatch_member_through(
                        &owner_protocols,
                        Some(symbol),
                        &member_receiver,
                        &self_receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        MemberDispatch::Handled => return None,
                        MemberDispatch::Stuck => {
                            return Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            });
                        }
                        MemberDispatch::NoCandidate => {}
                    }
                }
                let rendered = self.store.render(&diagnostic_receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            _ => {
                let rendered = self.store.render(&diagnostic_receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
        }
    }

    /// One step on a HasVariant constraint (a leading-dot use in inference
    /// position). Waits for the enum type's head like `try_member`; a known
    /// enum resolves exactly as the checking-mode path does — variant
    /// lookup, constructor instantiation, artifact recording — with the
    /// written arguments' types equated against the instantiated payload.
    pub(super) fn try_variant(
        &mut self,
        enum_ty: Ty,
        label: Label,
        payload: Vec<(Label, Ty)>,
        ctor: Option<Ty>,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        // Borrow expectations construct through to the enum inside (the
        // syntactic pre-strip in `check_expr` covers written borrows; this
        // covers heads that only resolve to a borrow in the solver).
        let (lookup, _) = self.member_receivers(&enum_ty);
        if stuck_projection(self.store, &lookup) {
            return Some(Constraint::HasVariant {
                enum_ty,
                label,
                payload,
                ctor,
                origin,
            });
        }
        let head = self.store.shallow(&lookup);
        let Ty::Nominal(symbol, args) = head else {
            return match head {
                Ty::Var(_) => Some(Constraint::HasVariant {
                    enum_ty,
                    label,
                    payload,
                    ctor,
                    origin,
                }),
                Ty::Error => None,
                _ => {
                    let receiver = self.store.render(&lookup);
                    self.errors.push((
                        TypeError::UnknownMember {
                            receiver,
                            label: label.to_string(),
                        },
                        origin.node,
                    ));
                    None
                }
            };
        };
        let Some(info) = self.catalog.enums.get(&symbol).cloned() else {
            let receiver = self.store.render(&lookup);
            self.errors.push((
                TypeError::UnknownMember {
                    receiver,
                    label: label.to_string(),
                },
                origin.node,
            ));
            return None;
        };
        let Some(variant) = info.variants.get(&label.to_string()).cloned() else {
            let receiver = self.store.render(&lookup);
            self.errors.push((
                TypeError::UnknownMember {
                    receiver,
                    label: label.to_string(),
                },
                origin.node,
            ));
            return None;
        };
        self.member_resolutions
            .insert(origin.node, MemberResolution::Direct(variant.symbol));
        let payload_labels: Vec<Label> = payload.iter().map(|(label, _)| label.clone()).collect();
        if !variant.payload_labels_match(&payload_labels) {
            self.errors.push((
                TypeError::InvalidVariantPayloadLabels {
                    variant: label.to_string(),
                },
                origin.node,
            ));
        }
        let mut tys: FxHashMap<Symbol, Ty> = info
            .params
            .iter()
            .map(|param| param.symbol)
            .zip(args.iter().cloned())
            .collect();
        for param in &variant.constructor_scheme.params {
            tys.entry(param.symbol)
                .or_insert_with(|| Ty::Var(self.store.fresh_ty(self.level, origin.node)));
        }
        let mut effs = FxHashMap::default();
        for param in &variant.constructor_scheme.eff_params {
            effs.insert(
                *param,
                EffTail::Var(self.store.fresh_eff(self.level, origin.node)),
            );
        }
        let mut rows = FxHashMap::default();
        for param in &variant.constructor_scheme.row_params {
            rows.insert(
                *param,
                RowTail::Var(self.store.fresh_row(self.level, origin.node)),
            );
        }
        let instantiation = variant.instantiate(&tys, &effs, &rows);
        if !instantiation.instantiations.is_empty() {
            self.instantiations
                .entry(origin.node)
                .or_default()
                .extend(instantiation.instantiations.iter().cloned());
        }
        for given in &instantiation.givens {
            queue.push(
                given
                    .clone()
                    .into_constraint(CtOrigin::new(origin.node, CtReason::Apply)),
            );
        }
        queue.push(Constraint::Eq(
            lookup,
            instantiation.result_type.clone(),
            origin,
        ));
        if payload.len() != instantiation.argument_types.len() {
            self.errors.push((
                TypeError::ArityMismatch {
                    expected: instantiation.argument_types.len(),
                    found: payload.len(),
                },
                origin.node,
            ));
        } else {
            for (expected, (_, found)) in instantiation.argument_types.iter().zip(&payload) {
                // A borrow-typed (or still-solving) payload argument against
                // an owned/unsolved slot defers (ADR 0021): eager equality
                // would bind the slot to the borrow — or the argument var
                // owned — before the coercion can be judged.
                let defer = matches!(
                    (self.store.shallow(expected), self.store.shallow(found)),
                    (_, Ty::Borrow(..)) | (Ty::Param(_), Ty::Var(_))
                );
                if defer {
                    queue.push(Constraint::CoerceOwned {
                        expected: expected.clone(),
                        found: found.clone(),
                        origin,
                    });
                } else {
                    queue.push(Constraint::Eq(expected.clone(), found.clone(), origin));
                }
            }
        }
        if let Some(ctor) = ctor {
            queue.push(Constraint::Eq(
                ctor,
                Ty::Func(
                    instantiation.argument_types,
                    Box::new(instantiation.result_type),
                    EffectRow::pure(),
                ),
                origin,
            ));
        }
        None
    }

    pub(super) fn member_receivers(&mut self, receiver: &Ty) -> (Ty, Ty) {
        let normalized = normalize_ty(self.store, self.catalog, receiver);
        let self_receiver = self.rewrite_ty_from_givens(normalized);
        let mut lookup_receiver = self_receiver.clone();
        loop {
            match lookup_receiver {
                Ty::Borrow(_, inner) | Ty::Unique(inner) => lookup_receiver = *inner,
                other => {
                    lookup_receiver = other;
                    break;
                }
            }
        }
        (lookup_receiver, self_receiver)
    }

    /// Type a method use on a nominal head (struct or enum): instantiate the
    /// method's scheme, substitute the head's type arguments (`substitution`),
    /// pin `self` to the receiver, and hand back the self-dropped signature as
    /// the member type. Structs and enums dispatch methods identically.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_nominal_method(
        &mut self,
        method: Symbol,
        substitution: &FxHashMap<Symbol, Ty>,
        receiver: Ty,
        label: Label,
        member: Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let signature = self.symbol_ty(method, origin.node, queue);
        let signature =
            signature.substitute(substitution, &Default::default(), &Default::default());
        match self.store.shallow(&signature) {
            Ty::Func(params, ret, eff) if !params.is_empty() => {
                self.push_immediate_argument_eq(queue, params[0].clone(), receiver, origin);
                queue.push(Constraint::Eq(
                    Ty::Func(params[1..].to_vec(), ret, eff),
                    member,
                    origin,
                ));
                // Publish the owner-param bindings (struct/enum generics
                // at the receiver's application) alongside the scheme
                // instantiation `symbol_ty` recorded — the node carries
                // the complete θ.
                self.instantiations
                    .entry(origin.node)
                    .or_default()
                    .extend(substitution.iter().map(|(s, t)| (*s, t.clone())));
                self.member_resolutions
                    .insert(origin.node, MemberResolution::Direct(method));
                None
            }
            // Signature still being checked in this group: retry when it resolves.
            Ty::Var(_) => Some(Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            }),
            _ => None,
        }
    }

    /// Type a member through a protocol requirement: substitute Self and the
    /// associated types into the requirement's signature, bind self, and
    /// demand conformance. Associated types substitute as projections
    /// `recv.Assoc` and reduce through `normalize_ty` once the receiver is
    /// concrete. A protocol's own Self
    /// (default-body checking) gets the protocol's same-named associated param
    /// where one exists — a sub-protocol's redeclared `associated` refines its
    /// super's — and a Self-projection otherwise.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn bind_requirement(
        &mut self,
        protocol: ProtocolRef,
        requirement: &Requirement,
        lookup_receiver: &Ty,
        self_receiver: &Ty,
        member: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
        evidence: Option<(
            crate::types::catalog::ConformanceId,
            Option<Symbol>,
            Vec<(Symbol, Ty)>,
        )>,
    ) {
        let receiver_head = self.store.shallow(lookup_receiver);
        let app = ProtocolApplication::new(receiver_head.clone(), protocol.clone());
        let mut tys = app.substitution(self.catalog);
        // Snapshot the receiver-derived entries (Self + assoc bindings)
        // before the generics join `tys`: the default-body θ published
        // below is exactly these.
        let receiver_entries: Vec<(Symbol, Ty)> =
            tys.iter().map(|(s, t)| (*s, t.clone())).collect();
        // The requirement's type is its scheme — the one signature
        // carrier. Method-level generics (`func map<U>`) instantiate
        // fresh per use, recorded for the lowerer's per-call-site θ;
        // the outer tail and inner closure rows are its eff_params.
        let Some(scheme) = self.schemes.get(&requirement.symbol).cloned() else {
            return;
        };
        for param in &scheme.params {
            let var = Ty::Var(self.store.fresh_ty(self.level, origin.node));
            self.instantiations
                .entry(origin.node)
                .or_default()
                .push((param.symbol, var.clone()));
            tys.insert(param.symbol, var);
        }
        let mut effs = FxHashMap::default();
        for param in &scheme.eff_params {
            effs.insert(
                *param,
                EffTail::Var(self.store.fresh_eff(self.level, origin.node)),
            );
        }
        let signature = scheme.ty.substitute(&tys, &effs, &Default::default());

        // The requirement supplies the abstract shape, but a concrete call
        // also knows its selected witness. Equating their outer effect rows
        // carries the witness's inferred effects into the member expression
        // that will be baked into the typed AST.
        let witness = evidence
            .as_ref()
            .and_then(|(_, witness, _)| *witness)
            .unwrap_or(requirement.symbol);
        let witness_substitution = evidence
            .as_ref()
            .map(|(_, _, substitution)| substitution.clone());
        let witness_signature = witness_substitution.as_ref().and_then(|substitution| {
            let substitution = substitution.iter().cloned().collect::<FxHashMap<_, _>>();
            let scheme = self.schemes.get(&witness)?.clone();
            let mut specialized = scheme.clone();
            specialized.ty =
                specialized
                    .ty
                    .substitute(&substitution, &Default::default(), &Default::default());
            specialized.predicates = specialized
                .predicates
                .iter()
                .map(|predicate| {
                    predicate.substitute(&substitution, &Default::default(), &Default::default())
                })
                .collect();
            Some(self.instantiate_scheme(&specialized, origin.node, queue))
        });
        if let Some(Ty::Func(_, _, witness_effects)) = witness_signature
            && let Ty::Func(_, _, requirement_effects) = &signature
        {
            queue.push(Constraint::EffEq(
                requirement_effects.clone(),
                witness_effects,
                origin,
            ));
        }

        let mut local_wanteds = vec![];
        if let Ty::Func(params, ret, eff) = signature
            && !params.is_empty()
        {
            self.push_immediate_argument_eq(
                &mut local_wanteds,
                params[0].clone(),
                self_receiver.clone(),
                origin,
            );
            local_wanteds.push(Constraint::Eq(
                Ty::Func(params[1..].to_vec(), ret, eff),
                member.clone(),
                origin,
            ));
        }
        let givens: Vec<Predicate> = scheme
            .predicates
            .iter()
            .map(|predicate| predicate.substitute(&tys, &effs, &Default::default()))
            .collect();
        if givens.is_empty() {
            queue.extend(local_wanteds);
        } else if !local_wanteds.is_empty() {
            queue.push(Constraint::Implic(Box::new(
                crate::types::constraint::Implication {
                    level: self.level,
                    givens,
                    wanteds: local_wanteds,
                    local_params: vec![],
                    touchable_level: None,
                },
            )));
        }
        queue.push(Constraint::Conforms {
            ty: lookup_receiver.clone(),
            protocol: protocol.clone(),
            origin,
        });
        // Publish the target-side θ on the node (Swift model: the IR
        // carries the resolution): a concrete witness needs its
        // conformance row's rigid params bound against the receiver head;
        // a default body needs Self and the assoc bindings. Entries may
        // hold vars/projections — finalize zonks and normalizes them.
        if let Some(bound) = witness_substitution {
            self.instantiations
                .entry(origin.node)
                .or_default()
                .extend(bound);
        } else {
            self.instantiations
                .entry(origin.node)
                .or_default()
                .extend(receiver_entries);
        }
        let resolution = if let Some((row, _, substitution)) = evidence {
            MemberResolution::ViaConformance {
                row,
                protocol: protocol.clone(),
                witness,
                substitution,
            }
        } else {
            MemberResolution::ViaRequirement {
                protocol: protocol.clone(),
                requirement: requirement.symbol,
                self_ty: receiver_head,
            }
        };
        self.member_resolutions.insert(origin.node, resolution);
    }

    fn push_immediate_argument_eq(
        &mut self,
        queue: &mut Vec<Constraint>,
        expected: Ty,
        found: Ty,
        origin: CtOrigin,
    ) {
        match self.store.shallow(&expected) {
            Ty::Borrow(expected_kind, expected_inner) => match self.store.shallow(&found) {
                Ty::Borrow(found_kind, found_inner) if found_kind == expected_kind => {
                    queue.push(Constraint::Eq(
                        (*expected_inner).clone(),
                        (*found_inner).clone(),
                        origin,
                    ));
                }
                Ty::Borrow(Perm::Exclusive, found_inner) if expected_kind == Perm::Shared => {
                    queue.push(Constraint::Eq(
                        (*expected_inner).clone(),
                        (*found_inner).clone(),
                        origin,
                    ));
                }
                Ty::Borrow(..) => queue.push(Constraint::Eq(expected, found, origin)),
                Ty::Var(_) if origin.reason == CtReason::Apply => {
                    queue.push(Constraint::ApplyBorrow {
                        expected_perm: expected_kind,
                        expected_inner: (*expected_inner).clone(),
                        found,
                        origin,
                    });
                }
                _ => queue.push(Constraint::Eq((*expected_inner).clone(), found, origin)),
            },
            _ => queue.push(Constraint::Eq(expected, found, origin)),
        }
    }

    /// Solver-side symbol lookup: in-flight monomorphic signature, or a
    /// scheme instantiation (with its predicates emitted as new wanteds).
    pub(super) fn symbol_ty(
        &mut self,
        symbol: Symbol,
        node: NodeID,
        queue: &mut Vec<Constraint>,
    ) -> Ty {
        if let Some(ty) = self.mono.get(&symbol) {
            return ty.clone();
        }
        if let Some(scheme) = self.schemes.get(&symbol) {
            let scheme = scheme.clone();
            return self.instantiate_scheme(&scheme, node, queue);
        }
        Ty::Var(self.store.fresh_ty(self.level, node))
    }

    pub(super) fn instantiate_scheme(
        &mut self,
        scheme: &Scheme,
        node: NodeID,
        queue: &mut Vec<Constraint>,
    ) -> Ty {
        if scheme.params.is_empty()
            && scheme.eff_params.is_empty()
            && scheme.row_params.is_empty()
            && scheme.perm_params.is_empty()
        {
            return scheme.ty.clone();
        }
        let mut tys = FxHashMap::default();
        let mut recorded = vec![];
        for param in &scheme.params {
            let var = Ty::Var(self.store.fresh_ty(self.level, node));
            recorded.push((param.symbol, var.clone()));
            tys.insert(param.symbol, var);
        }
        let mut effs = FxHashMap::default();
        for param in &scheme.eff_params {
            effs.insert(*param, EffTail::Var(self.store.fresh_eff(self.level, node)));
        }
        let mut rows = FxHashMap::default();
        for param in &scheme.row_params {
            let var = self.store.fresh_row(self.level, node);
            // Recorded as an empty open record over the fresh variable
            // (zonked to the call's concrete row at finalize) for the
            // lowerer's per-call-site θ.
            recorded.push((
                *param,
                Ty::Record(Row {
                    fields: vec![],
                    tail: Some(RowTail::Var(var)),
                }),
            ));
            rows.insert(*param, RowTail::Var(var));
        }
        let mut perms = FxHashMap::default();
        for param in &scheme.perm_params {
            perms.insert(*param, Perm::Var(self.store.fresh_perm(self.level, node)));
        }
        // Perms substitute into predicates too (see `instantiate` in
        // generate/instantiate.rs — same rule, same reason).
        for predicate in &scheme.predicates {
            queue.push(
                predicate
                    .substitute(&tys, &effs, &rows)
                    .substitute_perms(&perms)
                    .into_constraint(CtOrigin::new(node, CtReason::Apply)),
            );
        }
        self.instantiations
            .entry(node)
            .or_default()
            .extend(recorded);
        scheme
            .ty
            .substitute(&tys, &effs, &rows)
            .substitute_perms(&perms)
    }
}
