use super::*;

impl<'s> Solver<'s> {
    /// The unique-owner improvement rule (Jones, FPCA 1995): a stuck
    /// HasMember whose label has exactly one owner determines its receiver —
    /// a protocol owner adds a bound, a nominal owner commits the variable.
    /// Ambiguity is an error, never a guess.
    pub(super) fn improve(
        &mut self,
        stuck: &mut Vec<Constraint>,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let mut improved = false;
        let mut remaining = vec![];
        for constraint in stuck.drain(..) {
            if self.defaulting
                && let Constraint::Eq(a, b, origin) = constraint
            {
                if self.commit_unique_projection(&a, origin, queue)
                    || self.commit_unique_projection(&b, origin, queue)
                {
                    queue.push(Constraint::Eq(a, b, origin));
                    improved = true;
                } else {
                    remaining.push(Constraint::Eq(a, b, origin));
                }
                continue;
            }
            // Unique-row improvement (the final solve's analog of
            // unique-owner member improvement): a variable-headed
            // conformance goal with variable-free protocol arguments
            // and exactly one candidate row anywhere commits the
            // receiver to that row's head — forced, not a guess.
            if self.defaulting
                && let Constraint::Conforms {
                    ty,
                    protocol,
                    origin,
                } = &constraint
                && matches!(self.store.shallow(ty), Ty::Var(_))
                && let Some(head) = self.catalog.unique_conformance_head(protocol)
            {
                queue.push(Constraint::Eq(ty.clone(), head, *origin));
                queue.push(constraint);
                improved = true;
                continue;
            }
            // The dual improvement: a concrete receiver whose protocol
            // ARGUMENTS are still variable (`word.into()` in a position
            // that pins nothing) commits to the one DECLARED row that can
            // satisfy the goal — a synthesized row (the reflexive Into)
            // never wins a defaulting tie against a declared conversion.
            // Rows whose matched arguments still carry patterns cannot
            // pin anything and disqualify nothing.
            if self.defaulting
                && let Constraint::Conforms {
                    ty,
                    protocol,
                    origin,
                } = &constraint
                && protocol
                    .args
                    .iter()
                    .any(|arg| matches!(self.store.shallow(arg), Ty::Var(_)))
                && let Ty::Nominal(head, head_args) = self.store.shallow(ty)
            {
                let target = ProtocolRef {
                    protocol: protocol.protocol,
                    args: protocol
                        .args
                        .iter()
                        .map(|arg| self.store.shallow(arg))
                        .collect(),
                };
                let committed: Option<Vec<Ty>> = {
                    let candidates = self.catalog.matching_conformances(head, &head_args, &target);
                    let mut declared = candidates
                        .iter()
                        .filter(|matched| !matched.conformance.synthesized);
                    match (declared.next(), declared.next()) {
                        (Some(only), None) => {
                            let args: Vec<Ty> = only
                                .conformance
                                .protocol
                                .args
                                .iter()
                                .map(|arg| {
                                    arg.substitute(
                                        &only.substitution,
                                        &Default::default(),
                                        &Default::default(),
                                    )
                                })
                                .collect();
                            let closed = !args.iter().any(|arg| {
                                let mut open = false;
                                let _ = arg.try_visit(
                                    &mut |ty: &Ty| -> std::ops::ControlFlow<()> {
                                        if matches!(ty, Ty::Param(_) | Ty::Var(_)) {
                                            open = true;
                                            return std::ops::ControlFlow::Break(());
                                        }
                                        std::ops::ControlFlow::Continue(())
                                    },
                                );
                                open
                            });
                            closed.then_some(args)
                        }
                        _ => None,
                    }
                };
                if let Some(row_args) = committed {
                    for (arg, row_arg) in protocol.args.iter().zip(row_args) {
                        queue.push(Constraint::Eq(arg.clone(), row_arg, *origin));
                    }
                    queue.push(constraint);
                    improved = true;
                    continue;
                }
            }
            let Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            } = constraint
            else {
                remaining.push(constraint);
                continue;
            };
            let (lookup_receiver, self_receiver) = self.member_receivers(&receiver);
            let shallow = self.store.shallow(&lookup_receiver);
            let owned = match &shallow {
                Ty::Var(v) => self.store.level(v.0) >= self.level,
                _ => false,
            };
            if !owned {
                // Concrete heads retry normally; outer-level variables may
                // be solved by a later group, so improvement (which commits)
                // must not fire — they float out instead.
                remaining.push(Constraint::HasMember {
                    receiver,
                    label,
                    member,
                    origin,
                });
                continue;
            }
            let label_str = label.to_string();
            let owners = self
                .catalog
                .member_owners
                .get(&label_str)
                .cloned()
                .unwrap_or_default();
            match owners.as_slice() {
                [MemberOwner::Protocol(protocol)] => {
                    let args = self
                        .catalog
                        .protocols
                        .get(protocol)
                        .map(|info| {
                            info.params
                                .iter()
                                .map(|_| Ty::Var(self.store.fresh_ty(self.level, origin.node)))
                                .collect()
                        })
                        .unwrap_or_default();
                    let protocol = ProtocolRef {
                        protocol: *protocol,
                        args,
                    };
                    let overloads = self
                        .catalog
                        .requirement_overloads_in_ref(&protocol, &label_str);
                    if !overloads.is_empty() {
                        // Written labels select among same-base requirement
                        // overloads (ADR 0041).
                        let symbols: Vec<Symbol> = overloads
                            .iter()
                            .map(|(_, requirement)| requirement.symbol)
                            .collect();
                        let Some(selected) =
                            self.select_method_overload(&symbols, &label_str, origin)
                        else {
                            continue;
                        };
                        let Some((owner, requirement)) = overloads
                            .into_iter()
                            .find(|(_, requirement)| requirement.symbol == selected)
                        else {
                            continue;
                        };
                        self.bind_requirement(
                            owner,
                            &requirement,
                            &lookup_receiver,
                            &self_receiver,
                            &member,
                            origin,
                            queue,
                            None,
                        );
                        improved = true;
                    } else {
                        remaining.push(Constraint::HasMember {
                            receiver,
                            label,
                            member,
                            origin,
                        });
                    }
                }
                [MemberOwner::Nominal(symbol)] => {
                    if !self.defaulting {
                        // One nominal owner, but a record receiver could
                        // also satisfy the use: hold the constraint on the
                        // binder's scheme; the final solve commits if no
                        // instantiation discharged it.
                        remaining.push(Constraint::HasMember {
                            receiver,
                            label,
                            member,
                            origin,
                        });
                        continue;
                    }
                    let params = self
                        .catalog
                        .structs
                        .get(symbol)
                        .map(|i| i.params.len())
                        .or_else(|| self.catalog.enums.get(symbol).map(|i| i.params.len()))
                        .unwrap_or(0);
                    let args: Vec<Ty> = (0..params)
                        .map(|_| Ty::Var(self.store.fresh_ty(self.level, origin.node)))
                        .collect();
                    queue.push(Constraint::Eq(
                        lookup_receiver,
                        Ty::Nominal(*symbol, args),
                        origin,
                    ));
                    queue.push(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                    improved = true;
                }
                [] => {
                    // No nominal or protocol owns the label: the member
                    // is a record projection — default the receiver to an
                    // open record row (presence constraints become row
                    // unification: Gaster & Jones, POPL 1996; Leijen,
                    // Trends in FP 2005). The improvement gate above
                    // already restricts this to variables this group
                    // owns, so nominal information always wins, and the
                    // row tail generalizes if it survives the group.
                    // Bind the PEELED receiver: a borrowed receiver (an
                    // inferred borrow-default param) keeps its borrow and
                    // its payload becomes the record.
                    let tail = self.store.fresh_row(self.level, origin.node);
                    let probe = Ty::Record(Row {
                        fields: vec![(label.clone(), member.clone())],
                        tail: Some(RowTail::Var(tail)),
                    });
                    queue.push(Constraint::Eq(lookup_receiver, probe, origin));
                    improved = true;
                }
                _many => {
                    // Several owners: the constraint stays open and rides
                    // the binder's scheme (qualified types — Jones 1994);
                    // each instantiation discharges it against a concrete
                    // receiver.
                    remaining.push(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                }
            }
        }
        *stuck = remaining;
        improved
    }

    /// Unique-candidate projection improvement: a stuck associated-type
    /// projection whose base is a concrete nominal and whose protocol
    /// arguments are still variables commits to the one conformance row
    /// that can ever match — the same "uniqueness justifies commitment"
    /// rule as unique-owner member improvement. Sound only at the final
    /// solve (the `defaulting` gate in `improve`): earlier groups must
    /// keep floating, because a later group may pin the variables to a
    /// different row. Zero or several candidate rows stay stuck —
    /// ambiguity is an error, never a guess.
    fn commit_unique_projection(
        &mut self,
        ty: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let Ty::Proj(base, protocol, _) = self.store.shallow(ty) else {
            return false;
        };
        if !protocol.has_unification_vars() {
            return false;
        }
        let base = self.store.shallow(&base);
        let base = match &base {
            Ty::Borrow(_, inner) => self.store.shallow(inner),
            other => other.clone(),
        };
        let Ty::Nominal(symbol, args) = &base else {
            return false;
        };
        let catalog = self.catalog;
        let matches = catalog.matching_conformances(*symbol, args, &protocol);
        let [matched] = matches.as_slice() else {
            return false;
        };
        // The matching row may reach the target through a superprotocol;
        // commit against the candidate whose arguments actually matched
        // (the same candidate `match_conformance_row` selected).
        let committed_args = catalog
            .protocol_and_supers(matched.protocol)
            .into_iter()
            .filter(|candidate| {
                candidate.protocol == protocol.protocol
                    && candidate.args.len() == protocol.args.len()
            })
            .map(|candidate| {
                candidate
                    .args
                    .iter()
                    .map(|arg| {
                        arg.substitute(
                            &matched.substitution,
                            &Default::default(),
                            &Default::default(),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .find(|committed| {
                committed
                    .iter()
                    .zip(&protocol.args)
                    .all(|(pattern, actual)| {
                        crate::types::ty::match_key_pattern(
                            pattern,
                            actual,
                            &mut FxHashMap::default(),
                        )
                    })
            });
        let Some(committed_args) = committed_args else {
            return false;
        };
        // The commitment must pin the variables concretely: a generic row
        // whose parameters the match left unbound (a variable actual is a
        // wildcard) proves nothing and would only re-stick.
        if committed_args.iter().any(Ty::has_unification_vars) {
            return false;
        }
        for (actual, committed) in protocol.args.iter().zip(committed_args) {
            queue.push(Constraint::Eq(actual.clone(), committed, origin));
        }
        // Re-check the conformance through the normal path so the row's
        // context (premises) is applied, not just its arguments.
        queue.push(Constraint::Conforms {
            ty: base.clone(),
            protocol: protocol.clone(),
            origin,
        });
        true
    }
}
