//! Derived `Showable` witnesses, synthesized directly in λ_G.
//!
//! The checker discharges `Showable` *structurally* for structs and enums
//! with no explicit conformance row (`solve/conformance.rs::try_derive`) — so there is
//! no witness function to demand. The lowerer builds one here, in CPS λ_G,
//! with the same output format the previous implementation synthesized as
//! an AST (its `auto_derived_body_synthesis`): enums print
//! `Name.variant(payloads…)`, structs print `Name(field: value…)`
//! (`Name {}` when fieldless). This is the class-default move of Wadler &
//! Blott (POPL 1989) with a compiler-supplied instance body, made static
//! by monomorphization.
//!
//! Each piece of the output is either a string literal or a sub-`show`
//! call on a payload/field, folded left through the `String: Add` witness
//! — a continuation chain, since every concat and sub-show is a CPS call.

use crate::lambda_g::expr::{Const, ExprId, Op, TyKind};
use crate::lambda_g::program::Label;
use crate::name_resolution::symbol::Symbol;
use crate::types::ty::Ty as CheckTy;

use super::{Lowering, Theta, theta_key};

/// One piece of the rendered output.
enum Piece {
    Lit(String),
    /// A sub-show: the value to render and its checker type (which picks
    /// the witness — possibly another derived one).
    Show(ExprId, CheckTy),
}

impl<'a> Lowering<'a> {
    /// The derived `show` specialization for `head`, building it on first
    /// demand. Keyed like a protocol-default body — (requirement,
    /// θ{protocol := head}) — so recursive nominals tie the knot through
    /// `done` instead of recursing forever.
    pub(super) fn demand_derived_show(
        &mut self,
        protocol: Symbol,
        requirement: Symbol,
        head: &CheckTy,
    ) -> Option<Label> {
        let CheckTy::Nominal(head_symbol, head_args) = head else {
            return None;
        };
        let mut key_theta = Theta::default();
        key_theta.insert(protocol, head.clone());
        let key = (requirement, theta_key(&key_theta));
        if let Some(&label) = self.done.get(&key) {
            return Some(label);
        }

        let type_name = self
            .units
            .iter()
            .find_map(|u| u.resolved.symbol_names.get(head_symbol).cloned())
            .unwrap_or_else(|| format!("{head_symbol}"));

        // show : (Self) -> String, in CPS.
        let self_ty = self.map_ty(head);
        let string_ty = self.p.ty(TyKind::Boxed(Symbol::String));
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(string_ty, bot);
        let dom = self.p.ty_tuple(&[self_ty, ret_k_ty]);
        let label = self.p.func(&format!("show_{type_name}"), dom, bot);
        self.done.insert(key, label);

        let var = self.p.var(label);
        let self_value = self.p.extract(var, 0);
        let k = self.p.extract(var, 1);

        let body = if let Some(info) = self.enum_info(*head_symbol) {
            let subst: Theta = info
                .params
                .iter()
                .copied()
                .zip(head_args.iter().cloned())
                .collect();
            let no_effs = Default::default();
            let no_rows = Default::default();
            let self_check_ty = CheckTy::Nominal(*head_symbol, head_args.to_vec());
            // One switch arm per variant, each rendering its own pieces.
            let void_ty = self.p.ty_void();
            let trap = self.p.func("derived_show_failed", void_ty, bot);
            let trap_ref = self.p.func_ref(trap);
            let mut arm_refs = Vec::with_capacity(info.variants.len());
            for (variant_name, variant) in info.variants.iter() {
                let Some(instantiation) = variant
                    .instantiate(&subst, &no_effs, &no_rows)
                    .refined_by_result(&self_check_ty)
                else {
                    arm_refs.push(trap_ref);
                    continue;
                };
                let mut pieces = vec![];
                if instantiation.argument_types.is_empty() {
                    pieces.push(Piece::Lit(format!("{type_name}.{variant_name}")));
                } else {
                    pieces.push(Piece::Lit(format!("{type_name}.{variant_name}(")));
                    for (i, payload_ty) in instantiation.argument_types.iter().enumerate() {
                        if i > 0 {
                            pieces.push(Piece::Lit(", ".into()));
                        }
                        let lam_ty = self.map_ty(payload_ty);
                        let value = self
                            .p
                            .primop(Op::GetPayload(i as u32), &[self_value], lam_ty);
                        pieces.push(Piece::Show(value, payload_ty.clone()));
                    }
                    pieces.push(Piece::Lit(")".into()));
                }
                let arm_body = self.render_pieces(protocol, requirement, pieces, k)?;
                let case = self.p.func(&format!("show_{variant_name}"), void_ty, bot);
                self.p.set_body(case, arm_body);
                arm_refs.push(self.p.func_ref(case));
            }
            let i64_ty = self.p.ty_i64();
            let tag = self.p.primop(Op::GetTag, &[self_value], i64_ty);
            self.p.switch(tag, &arm_refs, trap_ref, bot)
        } else if let Some(info) = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(head_symbol).cloned())
        {
            let subst: Theta = info
                .params
                .iter()
                .copied()
                .zip(head_args.iter().cloned())
                .collect();
            let mut pieces = vec![];
            if info.fields.is_empty() {
                pieces.push(Piece::Lit(format!("{type_name} {{}}")));
            } else {
                for (i, (field_name, (_, field_ty))) in info.fields.iter().enumerate() {
                    let prefix = if i == 0 {
                        format!("{type_name}({field_name}: ")
                    } else {
                        format!(", {field_name}: ")
                    };
                    pieces.push(Piece::Lit(prefix));
                    let field_ty =
                        field_ty.substitute(&subst, &Default::default(), &Default::default());
                    let lam_ty = self.map_ty(&field_ty);
                    let value = self.p.primop(Op::GetField(i as u32), &[self_value], lam_ty);
                    pieces.push(Piece::Show(value, field_ty));
                }
                pieces.push(Piece::Lit(")".into()));
            }
            self.render_pieces(protocol, requirement, pieces, k)?
        } else {
            self.diagnostics.push(format!(
                "lowering: cannot derive show for {type_name} (not a struct or enum)"
            ));
            return None;
        };

        self.p.set_body(label, body);
        Some(label)
    }

    /// Fold the pieces left-to-right into a continuation chain delivering
    /// the concatenated String to `k`. The first piece is always a literal
    /// (every format starts with the type name).
    fn render_pieces(
        &mut self,
        protocol: Symbol,
        requirement: Symbol,
        pieces: Vec<Piece>,
        k: ExprId,
    ) -> Option<ExprId> {
        let mut iter = pieces.into_iter();
        let acc = match iter.next() {
            Some(Piece::Lit(text)) => self.string_value(&text),
            _ => {
                self.diagnostics
                    .push("lowering: derived show must start with a literal".into());
                return None;
            }
        };
        let rest: Vec<Piece> = iter.collect();
        self.render_rest(protocol, requirement, acc, &rest, k)
    }

    fn render_rest(
        &mut self,
        protocol: Symbol,
        requirement: Symbol,
        acc: ExprId,
        rest: &[Piece],
        k: ExprId,
    ) -> Option<ExprId> {
        let Some((piece, rest)) = rest.split_first() else {
            return Some(self.p.app(k, acc));
        };
        let string_ty = self.p.ty(TyKind::Boxed(Symbol::String));
        let bot = self.p.ty_bot();
        match piece {
            Piece::Lit(text) => {
                let lit = self.string_value(text);
                let add = self.string_add()?;
                let next = self.p.func("show_acc", string_ty, bot);
                let next_var = self.p.var(next);
                let next_body = self.render_rest(protocol, requirement, next_var, rest, k)?;
                self.p.set_body(next, next_body);
                let next_ref = self.p.func_ref(next);
                let add_ref = self.p.func_ref(add);
                let args = self.p.tuple(&[acc, lit, next_ref]);
                Some(self.p.app(add_ref, args))
            }
            Piece::Show(value, ty) => {
                // s ← show(value); acc ← acc + s; continue.
                let (show, _) = self.resolve_witness(protocol, requirement, "show".into(), ty)?;
                let add = self.string_add()?;
                let joined = self.p.func("show_acc", string_ty, bot);
                let joined_var = self.p.var(joined);
                let joined_body = self.render_rest(protocol, requirement, joined_var, rest, k)?;
                self.p.set_body(joined, joined_body);
                let joined_ref = self.p.func_ref(joined);

                let shown = self.p.func("shown", string_ty, bot);
                let shown_var = self.p.var(shown);
                let add_ref = self.p.func_ref(add);
                let add_args = self.p.tuple(&[acc, shown_var, joined_ref]);
                let shown_body = self.p.app(add_ref, add_args);
                self.p.set_body(shown, shown_body);
                let shown_ref = self.p.func_ref(shown);

                let show_ref = self.p.func_ref(show);
                let show_args = self.p.tuple(&[*value, shown_ref]);
                Some(self.p.app(show_ref, show_args))
            }
        }
    }

    /// The `String: Add` witness (string concatenation), demanded once.
    fn string_add(&mut self) -> Option<Label> {
        let witness = self.units.iter().find_map(|u| {
            u.types
                .catalog
                .conformances
                .iter()
                .find_map(|((head, _), conformance)| {
                    if *head == Symbol::String {
                        conformance.witnesses.get("add").copied()
                    } else {
                        None
                    }
                })
        });
        let Some(witness) = witness else {
            self.diagnostics
                .push("lowering: derived show needs the String: Add witness".into());
            return None;
        };
        Some(self.demand(witness, Theta::default()))
    }

    /// A String record over interned static bytes (the same layout string
    /// literals lower to).
    pub(super) fn string_value(&mut self, text: &str) -> ExprId {
        let bytes = text.as_bytes();
        let offset = self.intern_static(bytes);
        let ptr_ty = self.p.ty_ptr();
        let base = self.p.constant(Const::StaticPtr(offset), ptr_ty);
        let len = self.p.int(bytes.len() as i64);
        let ty = self.p.ty(TyKind::Boxed(Symbol::String));
        let storage = self.string_storage_value(Symbol::String, base);
        self.p
            .primop(Op::RecordNew(Symbol::String), &[storage, len, len], ty)
    }
}
