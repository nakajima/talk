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
                    if let Some((owner, requirement)) =
                        self.catalog.requirement_in_ref(&protocol, &label_str)
                    {
                        let requirement = requirement.clone();
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
}
