use super::*;

use crate::node_kinds::call_arg::{CallArg, CallArgOrigin};
use crate::parsing::label::Label;
use crate::span::Span;
use crate::types::callables::ArgumentLabel;
use crate::types::error::LabelMismatch;

/// How a call names its callee, for selecting the callable under check.
enum CalleeShape {
    /// A direct reference: `f(...)`, `'ask(...)`, `Point(...)`.
    Value(Option<Symbol>),
    /// A member access: `recv.m(...)` or `Type.m(...)`.
    Member { type_receiver: bool },
    /// Never a source label occurrence (leading-dot variants, sugar).
    Skip,
}

/// One written argument, snapshotted for post-solve checking.
struct ArgSite {
    node: NodeID,
    /// The written label, `Some("_")` for the `_:` spelling, `None` for an
    /// unlabeled argument.
    written: Option<String>,
    label_span: Span,
    origin: CallArgOrigin,
    insert_at: u32,
}

struct CallSite {
    call: NodeID,
    callee: NodeID,
    shape: CalleeShape,
    args: Vec<ArgSite>,
}

impl From<&CallArg> for ArgSite {
    fn from(arg: &CallArg) -> Self {
        ArgSite {
            node: arg.id,
            written: match &arg.label {
                Label::Named(name) => Some(name.clone()),
                _ => None,
            },
            label_span: arg.label_span,
            origin: arg.origin,
            insert_at: arg
                .mode_span
                .map(|span| span.start)
                .unwrap_or(arg.value.span.start),
        }
    }
}

impl<'a> TypecheckSession<'a> {
    /// Post-solve argument-label checking (ADR 0041). Every statically
    /// resolved call publishes its selected callable; calls with a callable
    /// contract check written labels against declared labels, and indirect
    /// function-value calls are positional. Runs after solving so member
    /// and initializer selections are available; compiler-generated sugar
    /// is exempted by argument origin, never by inspecting synthesized
    /// names or spans.
    pub(super) fn check_call_labels(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
        let mut sites: Vec<CallSite> = vec![];
        {
            let mut collector = derive_visitor::visitor_enter_fn(|expr: &Expr| {
                // Effect performs obey the same label rules; the effect
                // name is the callee.
                if let ExprKind::CallEffect {
                    effect_name, args, ..
                } = &expr.kind
                {
                    if args
                        .iter()
                        .any(|arg| arg.origin == CallArgOrigin::Synthesized)
                    {
                        return;
                    }
                    let shape = match effect_name.symbol() {
                        Ok(symbol) => CalleeShape::Value(Some(symbol)),
                        Err(_) => CalleeShape::Skip,
                    };
                    sites.push(CallSite {
                        call: expr.id,
                        callee: expr.id,
                        shape,
                        args: args.iter().map(ArgSite::from).collect(),
                    });
                    return;
                }
                let ExprKind::Call {
                    callee,
                    args,
                    desugared_operator,
                    ..
                } = &expr.kind
                else {
                    return;
                };
                // Sugar selects its callable semantically; it has no source
                // label occurrences.
                if desugared_operator.is_some()
                    || args
                        .iter()
                        .any(|arg| arg.origin == CallArgOrigin::Synthesized)
                {
                    return;
                }
                let shape = match &callee.kind {
                    // An unresolved callee proves nothing about labels;
                    // name resolution already diagnosed it.
                    ExprKind::Variable(name) => match name.symbol() {
                        Ok(symbol) => CalleeShape::Value(Some(symbol)),
                        Err(_) => CalleeShape::Skip,
                    },
                    ExprKind::Member(Some(receiver), ..) => CalleeShape::Member {
                        type_receiver: Self::is_type_receiver(receiver),
                    },
                    // Leading-dot variant sugar: payload labels have their
                    // own declaration-backed checking.
                    ExprKind::Member(None, ..) => CalleeShape::Skip,
                    ExprKind::Constructor(..) => CalleeShape::Member {
                        type_receiver: true,
                    },
                    // Any other callee is a function value: positional.
                    _ => CalleeShape::Value(None),
                };
                let args = args.iter().map(ArgSite::from).collect();
                sites.push(CallSite {
                    call: expr.id,
                    callee: callee.id,
                    shape,
                    args,
                });
            });
            for ast in asts.values() {
                for root in &ast.roots {
                    use derive_visitor::Drive;
                    root.drive(&mut collector);
                }
            }
        }

        for site in sites {
            self.check_call_site(site);
        }
    }

    fn is_type_receiver(receiver: &Expr) -> bool {
        matches!(&receiver.kind, ExprKind::Constructor(..))
            || matches!(
                &receiver.kind,
                ExprKind::Variable(name) if matches!(
                    name.symbol(),
                    Ok(Symbol::Struct(_)
                        | Symbol::Enum(_)
                        | Symbol::Protocol(_)
                        | Symbol::TypeAlias(_)
                        | Symbol::TypeParameter(_))
                )
            )
    }

    fn check_call_site(&mut self, site: CallSite) {
        // The selected callable: initializer/member/requirement selections
        // publish at the callee node; direct references carry their symbol.
        let resolved =
            self.artifacts.member_resolutions.get(&site.callee).map(
                |resolution| match resolution {
                    MemberResolution::Direct(symbol) => *symbol,
                    MemberResolution::ViaConformance { witness, .. } => *witness,
                    MemberResolution::ViaRequirement { requirement, .. } => *requirement,
                },
            );
        let selected = resolved.or(match site.shape {
            CalleeShape::Value(symbol) => symbol,
            _ => None,
        });
        if matches!(site.shape, CalleeShape::Skip) {
            return;
        }
        if let Some(symbol) = selected {
            self.artifacts.selected_callables.insert(site.call, symbol);
        }

        let contract = selected.and_then(|symbol| self.catalog.callable_contracts.get(&symbol));
        let Some(contract) = contract else {
            // No contract: a function value (or a construct whose labels are
            // validated elsewhere, like enum variants). Function values are
            // positional — written labels are unexpected. An unresolved
            // member proves nothing; the solver already diagnosed it.
            let indirect = match (&site.shape, selected) {
                (CalleeShape::Member { .. }, None) => false,
                (_, None) => true,
                (
                    _,
                    Some(
                        Symbol::Global(_)
                        | Symbol::DeclaredLocal(_)
                        | Symbol::PatternBindLocal(_)
                        | Symbol::ParamLocal(_)
                        | Symbol::Property(_),
                    ),
                ) => true,
                (_, Some(_)) => false,
            };
            if !indirect {
                return;
            }
            let mismatches: Vec<LabelMismatch> = site
                .args
                .iter()
                .enumerate()
                .filter(|(_, arg)| arg.origin == CallArgOrigin::Written)
                .filter_map(|(index, arg)| {
                    let found = arg.written.clone()?;
                    Some(LabelMismatch {
                        index,
                        arg: arg.node,
                        expected: None,
                        found: Some(found),
                        label_span: arg.label_span,
                        insert_at: arg.insert_at,
                    })
                })
                .collect();
            if !mismatches.is_empty() {
                self.diagnostics.errors.push((
                    TypeError::ArgumentLabelMismatch {
                        callable: None,
                        mismatches,
                    },
                    site.call,
                ));
            }
            return;
        };

        let labels = &contract.name.labels;
        // A protocol-static call form passes the receiver explicitly as a
        // compiler-defined unlabeled leading argument.
        let args: &[ArgSite] = if matches!(
            site.shape,
            CalleeShape::Member {
                type_receiver: true
            }
        ) && site.args.len() == labels.len() + 1
            && site.args[0].written.is_none()
            && matches!(
                contract.role,
                crate::types::callables::CallableRole::Requirement
                    | crate::types::callables::CallableRole::Method { is_static: false }
            ) {
            &site.args[1..]
        } else {
            &site.args
        };
        // Label checking follows arity checking: a wrong-arity call reports
        // the arity error alone, never label mismatches for a partial zip.
        if args.len() != labels.len() {
            return;
        }

        let callable = Some(contract.name.to_string());
        let mut mismatches: Vec<LabelMismatch> = vec![];
        for (index, (arg, expected)) in args.iter().zip(labels).enumerate() {
            // Trailing blocks and paren-less leading strings omit their
            // labels by syntax, not by the declaration.
            if matches!(
                arg.origin,
                CallArgOrigin::TrailingBlock | CallArgOrigin::BareString
            ) {
                continue;
            }
            let expected = match expected {
                ArgumentLabel::Named(name) => Some(name.as_str()),
                ArgumentLabel::Omitted => None,
            };
            let matches = match (&arg.written, expected) {
                (Some(written), Some(name)) => written == name,
                (None, None) => true,
                _ => false,
            };
            if matches {
                continue;
            }
            mismatches.push(LabelMismatch {
                index,
                arg: arg.node,
                expected: expected.map(str::to_string),
                found: arg.written.clone(),
                label_span: arg.label_span,
                insert_at: arg.insert_at,
            });
        }
        if !mismatches.is_empty() {
            self.diagnostics.errors.push((
                TypeError::ArgumentLabelMismatch {
                    callable,
                    mismatches,
                },
                site.call,
            ));
        }
    }
}
