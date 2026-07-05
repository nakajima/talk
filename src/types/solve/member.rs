use super::*;
use crate::types::ty::Perm;

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
        protocols: &[Symbol],
        head: Option<Symbol>,
        lookup_receiver: &Ty,
        self_receiver: &Ty,
        label: &str,
        member: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let mut candidates: Vec<(Symbol, Symbol, Requirement)> = vec![];
        for &protocol in protocols {
            let Some((owner, requirement)) = self.catalog.requirement_in(protocol, label) else {
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
            candidates.push((protocol, owner, requirement.clone()));
        }
        match candidates.as_slice() {
            [] => false,
            [(protocol, owner, requirement)] => {
                let witness = head
                    .and_then(|h| self.catalog.conformances.get(&(h, *protocol)))
                    .and_then(|c| c.witnesses.get(label))
                    .copied()
                    .unwrap_or(requirement.symbol);
                self.bind_requirement(
                    *owner,
                    requirement,
                    lookup_receiver,
                    self_receiver,
                    member,
                    origin,
                    queue,
                    witness,
                );
                true
            }
            many => {
                let rendered = self.store.render(self_receiver);
                self.errors.push((
                    TypeError::AmbiguousMember {
                        receiver: rendered,
                        label: label.to_string(),
                        candidates: many.iter().map(|(p, ..)| p.to_string()).collect(),
                    },
                    origin.node,
                ));
                true
            }
        }
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
                if self.dispatch_member_through(
                    &bounds,
                    None,
                    &member_receiver,
                    &self_receiver,
                    &label_str,
                    &member,
                    origin,
                    queue,
                ) {
                    return None;
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
                if self.dispatch_member_through(
                    &bounds,
                    None,
                    &member_receiver,
                    &self_receiver,
                    &label_str,
                    &member,
                    origin,
                    queue,
                ) {
                    return None;
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
                let Some((owner, requirement)) = self.catalog.requirement_in(protocol, &label_str)
                else {
                    let rendered = self.store.render(&diagnostic_receiver);
                    self.errors.push((
                        TypeError::UnknownMember {
                            receiver: rendered,
                            label: label_str,
                        },
                        origin.node,
                    ));
                    return None;
                };
                let requirement = requirement.clone();
                self.bind_requirement(
                    owner,
                    &requirement,
                    &member_receiver,
                    &self_receiver,
                    &member,
                    origin,
                    queue,
                    requirement.symbol,
                );
                None
            }
            Ty::Nominal(symbol, args) => {
                if let Some(info) = self.catalog.structs.get(&symbol) {
                    let substitution: FxHashMap<Symbol, Ty> = info
                        .params
                        .iter()
                        .copied()
                        .zip(args.iter().cloned())
                        .collect();
                    if let Some((property, field_ty)) = info.fields.get(&label_str) {
                        let field_ty = field_ty.substitute(
                            &substitution,
                            &Default::default(),
                            &Default::default(),
                        );
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
                        .copied()
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
                // Members provided through conformances (extend witnesses):
                // type via the protocol requirement, which is always valid if
                // the conformance is (the witness is checked against the
                // requirement when the extend body is checked).
                if let Some(protocols) = self.catalog.conformances_by_head.get(&symbol) {
                    let protocols = protocols.clone();
                    if self.dispatch_member_through(
                        &protocols,
                        Some(symbol),
                        &member_receiver,
                        &self_receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        return None;
                    }
                }
                // Auto-derived protocol members (`optional.show()` without
                // an explicit conformance): dispatch through the requirement
                // when the head is a struct/enum and the protocol derives.
                let is_derivable_head = self.catalog.structs.contains_key(&symbol)
                    || self.catalog.enums.contains_key(&symbol);
                if is_derivable_head {
                    for protocol in self.catalog.derivable.clone() {
                        if let Some((owner, requirement)) =
                            self.catalog.requirement_in(protocol, &label_str)
                        {
                            let requirement = requirement.clone();
                            let witness = requirement.symbol;
                            self.bind_requirement(
                                owner,
                                &requirement,
                                &member_receiver,
                                &self_receiver,
                                &member,
                                origin,
                                queue,
                                witness,
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
                    && let Some(inherent) = members.get(&label_str)
                {
                    let inherent = inherent.clone();
                    let Some(scheme) = self.schemes.get(&inherent.symbol).cloned() else {
                        return None;
                    };
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

    pub(super) fn member_receivers(&mut self, receiver: &Ty) -> (Ty, Ty) {
        let normalized = normalize_ty(self.store, self.catalog, receiver);
        let self_receiver = self.rewrite_ty_from_givens(normalized);
        let lookup_receiver = match self_receiver.clone() {
            Ty::Borrow(_, inner) | Ty::Unique(inner) => *inner,
            other => other,
        };
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
        protocol: Symbol,
        requirement: &Requirement,
        lookup_receiver: &Ty,
        self_receiver: &Ty,
        member: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
        witness: Symbol,
    ) {
        let owner_assoc: Vec<(String, Symbol)> = self
            .catalog
            .protocols
            .get(&protocol)
            .map(|info| info.assoc.iter().map(|(n, s)| (n.clone(), *s)).collect())
            .unwrap_or_default();

        let receiver_head = self.store.shallow(lookup_receiver);
        let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
        match &receiver_head {
            Ty::Param(self_symbol @ Symbol::Protocol(_)) => {
                let receiver_assoc = self
                    .catalog
                    .protocols
                    .get(self_symbol)
                    .map(|info| info.assoc.clone())
                    .unwrap_or_default();
                for (name, owner_symbol) in &owner_assoc {
                    let substituted = receiver_assoc
                        .get(name)
                        .map(|refined| Ty::Param(*refined))
                        .unwrap_or_else(|| {
                            Ty::Proj(Box::new(receiver_head.clone()), protocol, *owner_symbol)
                        });
                    tys.insert(*owner_symbol, substituted);
                }
            }
            Ty::Param(_) | Ty::Proj(..) => {
                for (_, owner_symbol) in &owner_assoc {
                    tys.insert(
                        *owner_symbol,
                        Ty::Proj(Box::new(receiver_head.clone()), protocol, *owner_symbol),
                    );
                }
            }
            Ty::Any { assoc, .. } => {
                for (_, owner_symbol) in &owner_assoc {
                    let substituted = assoc
                        .iter()
                        .find_map(|(symbol, ty)| (symbol == owner_symbol).then(|| ty.clone()))
                        .unwrap_or_else(|| {
                            Ty::Proj(Box::new(lookup_receiver.clone()), protocol, *owner_symbol)
                        });
                    tys.insert(*owner_symbol, substituted);
                }
            }
            _ => {
                for (_, owner_symbol) in &owner_assoc {
                    tys.insert(
                        *owner_symbol,
                        Ty::Proj(Box::new(lookup_receiver.clone()), protocol, *owner_symbol),
                    );
                }
            }
        }
        tys.insert(protocol, lookup_receiver.clone());
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
            protocol,
            origin,
        });
        // Publish the target-side θ on the node (Swift model: the IR
        // carries the resolution): a concrete witness needs its
        // conformance row's rigid params bound against the receiver head;
        // a default body needs Self and the assoc bindings. Entries may
        // hold vars/projections — finalize zonks and normalizes them.
        let head_for_witness = match &receiver_head {
            Ty::Borrow(_, inner) => inner.as_ref().clone(),
            other => other.clone(),
        };
        if witness != requirement.symbol {
            if let Ty::Nominal(head, head_args) = &head_for_witness
                && let Some(conformance) = self.catalog.conformances.get(&(*head, protocol))
            {
                let mut bound: FxHashMap<Symbol, Ty> = FxHashMap::default();
                for (pattern, actual) in conformance.self_args.iter().zip(head_args) {
                    bind_param_pattern(pattern, actual, &mut bound);
                }
                self.instantiations
                    .entry(origin.node)
                    .or_default()
                    .extend(bound);
            }
        } else {
            self.instantiations
                .entry(origin.node)
                .or_default()
                .extend(receiver_entries);
        }
        self.member_resolutions.insert(
            origin.node,
            MemberResolution::ViaConformance { protocol, witness },
        );
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
        for predicate in &scheme.predicates {
            queue.push(
                predicate
                    .substitute(&tys, &effs, &rows)
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
