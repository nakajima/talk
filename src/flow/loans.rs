//! Loans, provenance, and the borrow conflict rules — the legacy checker's
//! NLL core, reimplemented over the flow walk. Borrows have no surface
//! expression: they arise from `&`-typed parameters (call arguments and
//! receivers), bindings whose type contains a borrow (`Substring`, `&mut T`
//! annotations), match-arm binders over borrowed scrutinees, and `[&x]`
//! closure captures. A loan lives until its borrower's last use
//! (`flow::liveness`).

use crate::flow::OwnershipError;
use crate::hir::{self, ExprKind};
use crate::node_id::NodeID;
use crate::types::ty::{Perm, Ty};

use super::moves::{MoveChecker, MoveState};
use super::place::Place;

/// Where a borrowed value ultimately came from — the provenance origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Origin {
    /// A `&`-typed parameter: the caller owns it; returning is fine.
    BorrowedParam,
    /// A by-value parameter this function owns.
    OwnedParam,
    /// A local this function owns.
    Local,
    /// A global.
    Static,
    /// Unknown (e.g. a call with no borrow-typed inputs).
    Unknown,
}

impl Origin {
    pub(crate) fn is_function_owned(self) -> bool {
        matches!(self, Origin::OwnedParam | Origin::Local)
    }
}

/// One provenance loan: a borrowed value reaches `owner` (when known).
#[derive(Clone, Debug)]
pub(crate) struct ProvLoan {
    pub(crate) origin: Origin,
    pub(crate) owner: Option<Place>,
    pub(crate) kind: Perm,
}

/// The set of places a borrowed value may reach (aggregates carry many).
#[derive(Clone, Debug, Default)]
pub(crate) struct Provenance {
    pub(crate) loans: Vec<ProvLoan>,
}

impl Provenance {
    pub(crate) fn direct(origin: Origin, owner: Option<Place>, kind: Perm) -> Provenance {
        Provenance {
            loans: vec![ProvLoan {
                origin,
                owner,
                kind,
            }],
        }
    }

    pub(crate) fn unknown(kind: Perm) -> Provenance {
        Provenance::direct(Origin::Unknown, None, kind)
    }

    pub(crate) fn union(mut self, other: Provenance) -> Provenance {
        self.loans.extend(other.loans);
        self
    }

    /// The same reach at a different permission: a `&mut`-annotated binding
    /// borrows its sources exclusively.
    pub(crate) fn with_kind(mut self, kind: Perm) -> Provenance {
        for loan in &mut self.loans {
            loan.kind = kind;
        }
        self
    }

    pub(crate) fn has_unknown(&self) -> bool {
        self.loans.iter().any(|loan| loan.origin == Origin::Unknown)
    }

    pub(crate) fn has_function_owned(&self) -> bool {
        self.loans
            .iter()
            .any(|loan| loan.origin.is_function_owned())
    }
}

/// An active NLL loan: `borrower` holds access to `owner` at `kind`.
#[derive(Clone, Debug)]
pub(crate) struct ActiveLoan {
    pub(crate) borrower: Place,
    pub(crate) owner: Place,
    pub(crate) kind: Perm,
}

impl MoveState {
    pub(crate) fn add_loan(&mut self, borrower: Place, owner: Place, kind: Perm) {
        self.loans.push(ActiveLoan {
            borrower,
            owner,
            kind,
        });
    }

    /// The owner a use of `place` actually touches: a borrowed root's path
    /// rebases onto its real owner (`borrow.length` conflicts on `s`).
    pub(crate) fn loan_owner_for(&self, place: &Place) -> Place {
        if let Some(provenance) = self
            .provenances
            .get(&Place::root(place.root))
            .or_else(|| self.provenances.get(place))
            && let Some(owner) = provenance.loans.iter().find_map(|loan| loan.owner.clone())
        {
            let mut rebased = owner;
            rebased.fields.extend(place.fields.iter().copied());
            return rebased;
        }
        place.clone()
    }

    /// The permission a use of `place` can actually exert on its rebased
    /// owner: rebasing through a shared loan caps an exclusive touch of
    /// the borrower to a shared touch of the owner (mutating an iterator's
    /// cursor is not a write through its array borrow).
    pub(crate) fn rebased_perm(&self, place: &Place, requested: Perm) -> Perm {
        if !requested.is_exclusive() {
            return requested;
        }
        if let Some(provenance) = self
            .provenances
            .get(&Place::root(place.root))
            .or_else(|| self.provenances.get(place))
            && let Some(loan) = provenance.loans.iter().find(|loan| loan.owner.is_some())
        {
            return loan.kind;
        }
        requested
    }

    /// Mark every borrow whose owner overlaps `owner` as invalidated.
    pub(crate) fn invalidate_borrows_of(&mut self, owner: &Place) {
        let mut invalid: Vec<(Place, Place)> = vec![];
        for (borrower, provenance) in &self.provenances {
            for loan in &provenance.loans {
                if let Some(loan_owner) = &loan.owner
                    && loan_owner.overlaps(owner)
                {
                    invalid.push((borrower.clone(), loan_owner.clone()));
                }
            }
        }
        for (borrower, owner) in invalid {
            self.invalid_borrows.entry(borrower).or_insert(owner);
        }
    }

    /// The invalidated borrower a use of `place` touches, if any.
    pub(crate) fn invalid_borrow_for_use(&self, place: &Place) -> Option<(&Place, &Place)> {
        self.invalid_borrows
            .iter()
            .find(|(borrower, _)| borrower.overlaps(place))
    }

    /// Drop every loan/provenance whose borrower root has no later use.
    pub(crate) fn prune_dead_loans(&mut self, liveness: &super::liveness::Liveness, node: NodeID) {
        self.loans
            .retain(|loan| !liveness.dead_after(node, loan.borrower.root));
        self.provenances
            .retain(|borrower, _| !liveness.dead_after(node, borrower.root));
        self.invalid_borrows
            .retain(|borrower, _| !liveness.dead_after(node, borrower.root));
    }
}

impl MoveChecker<'_> {
    /// The legacy `check_borrow_conflicts`: a requested borrow of `owner`
    /// conflicts with an existing loan on an overlapping owner unless the
    /// requester IS that loan's borrower, and only when either side is
    /// exclusive (two shared borrows coexist).
    pub(crate) fn check_borrow_conflicts(
        &mut self,
        node: NodeID,
        owner: &Place,
        requested: Perm,
        requester: Option<&Place>,
        state: &MoveState,
    ) {
        let conflict = state.loans.iter().find(|existing| {
            existing.owner.overlaps(owner)
                && !requester.is_some_and(|requester| requester.overlaps(&existing.borrower))
                && (requested.is_exclusive() || existing.kind.is_exclusive())
        });
        if let Some(existing) = conflict {
            let error = OwnershipError::OverlappingBorrow {
                owner: self.render(owner),
                requested_kind: perm_name(requested).to_string(),
                existing: self.render(&existing.borrower),
                existing_kind: perm_name(existing.kind).to_string(),
            };
            self.error(error, node);
        }
    }

    /// The legacy `check_move_while_borrowed`.
    pub(crate) fn check_move_while_borrowed(
        &mut self,
        node: NodeID,
        place: &Place,
        state: &MoveState,
    ) {
        if let Some(loan) = state.loans.iter().find(|loan| loan.owner.overlaps(place)) {
            let error = OwnershipError::MoveWhileBorrowed {
                name: self.render(place),
                borrower: self.render(&loan.borrower),
            };
            self.error(error, node);
        }
    }

    /// The legacy `check_move_out_of_borrowed_value`: extracting a non-copy
    /// value from inside a borrowed value moves out of it — unless the value
    /// is CheapClone, in which case the extraction clones (tier 2: lowering
    /// retains the buffers, the owner stays live). Returns whether the
    /// tier-2 clone applied.
    pub(crate) fn check_move_out_of_borrowed(
        &mut self,
        expr: &hir::Expr,
        place: &Place,
        state: &MoveState,
    ) -> bool {
        if place.fields.is_empty() {
            return false;
        }
        let root = Place::root(place.root);
        // A `'heap` root's fields belong to the shared object: extracting
        // an owned value must clone (its buffers are the region's).
        let root_is_object = self.root_ty(place.root).is_some_and(|ty| match &ty {
            Ty::Borrow(_, inner) => self.grades.is_object(inner),
            other => self.grades.is_object(other),
        });
        let root_is_borrowed = state.borrowed_roots.contains_key(&place.root)
            || state.provenances.contains_key(&root)
            || self
                .symbol_ty(place.root)
                .is_some_and(|ty| self.grades.is_borrowed_value(&ty));
        if root_is_borrowed || root_is_object {
            if self.grades.is_cheap_clone(&expr.ty) {
                if self.recording {
                    self.auto_clones.insert(expr.id);
                }
                return true;
            }
            // A type-parameter extraction from a heap object: the grade is
            // the instantiation's, so the clone/no-op/error decision moves
            // to lowering (which holds θ). Mark it and let each
            // monomorphization resolve.
            if root_is_object && matches!(expr.ty, Ty::Param(_)) {
                if self.recording {
                    self.auto_clones.insert(expr.id);
                }
                return true;
            }
            let error = OwnershipError::MoveOutOfBorrowedValue {
                name: self.render(place),
                owner: self.render(&root),
                ty: expr.ty.render_mono(),
            };
            self.error(error, expr.id);
        }
        false
    }

    /// Use of a borrow whose owner has moved or been reassigned.
    pub(crate) fn check_invalidated_use(
        &mut self,
        node: NodeID,
        ty: &Ty,
        place: &Place,
        state: &MoveState,
    ) {
        if let Some((borrower, owner)) = state.invalid_borrow_for_use(place) {
            let error = OwnershipError::UseAfterInvalidatedBorrow {
                name: self.render(borrower),
                owner: self.render(owner),
                ty: ty.render_mono(),
            };
            self.error(error, node);
        }
    }

    fn symbol_ty(&self, symbol: crate::name_resolution::symbol::Symbol) -> Option<Ty> {
        self.types
            .schemes
            .get(&symbol)
            .map(|scheme| scheme.ty.clone())
            .or_else(|| self.param_tys.get(&symbol).cloned())
    }

    pub(crate) fn render(&self, place: &Place) -> String {
        super::moves::render_place(place, self.types)
    }

    // ----- Provenance ---------------------------------------------------------

    /// The places a borrowed value produced by `expr` may reach.
    pub(crate) fn expr_provenance(&mut self, expr: &hir::Expr, state: &MoveState) -> Provenance {
        if let Some(place) = self.place(expr) {
            let root = Place::root(place.root);
            if let Some(provenance) = state
                .provenances
                .get(&place)
                .or_else(|| state.provenances.get(&root))
            {
                return provenance.clone();
            }
            let kind = state
                .borrowed_roots
                .get(&place.root)
                .copied()
                .unwrap_or(Perm::Shared);
            return Provenance::direct(self.origin_of_root(place.root), Some(place), kind);
        }
        match &expr.kind {
            ExprKind::Call { callee, args, .. } => self.call_provenance(callee, args, state),
            ExprKind::Tuple(items)
            | ExprKind::LiteralArray(items)
            | ExprKind::Con { args: items, .. } => {
                let mut provenance = Provenance::default();
                for item in items {
                    if self.grades.contains_borrowed(&item.ty) {
                        provenance = provenance.union(self.expr_provenance(item, state));
                    }
                }
                provenance
            }
            ExprKind::RecordLiteral { fields, spread } => {
                let mut provenance = Provenance::default();
                for field in fields {
                    if self.grades.contains_borrowed(&field.value.ty) {
                        provenance = provenance.union(self.expr_provenance(&field.value, state));
                    }
                }
                if let Some(spread) = spread
                    && self.grades.contains_borrowed(&spread.ty)
                {
                    provenance = provenance.union(self.expr_provenance(spread, state));
                }
                provenance
            }
            // A literal is static data: a borrow of it outlives everything.
            ExprKind::Lit(_) => Provenance::direct(Origin::Static, None, Perm::Shared),
            // A call-result temp: recorded at its Call statement.
            ExprKind::Temp(temp) => state
                .temp_provenances
                .get(temp)
                .cloned()
                .unwrap_or_else(|| Provenance::unknown(Perm::Shared)),
            _ => Provenance::unknown(Perm::Shared),
        }
    }

    /// A declared struct field or enum payload cannot store a plain `&T`:
    /// the borrow would outlive its owner unseen. Borrowed-marker view
    /// nominals (e.g. `Substring`) stay legal — provenance tracks those —
    /// and function types are values, not borrows. Core is exempt (its
    /// iterator machinery stores borrow fields deliberately, like its raw
    /// pointers).
    pub(crate) fn check_borrow_storage(&mut self, roots: &[hir::Node]) {
        if self.module_id == crate::compiling::module::ModuleId::Core {
            return;
        }
        for root in roots {
            let hir::Node::Decl(decl) = root else {
                continue;
            };
            match &decl.kind {
                hir::DeclKind::Struct { name, .. } => {
                    let Ok(symbol) = name.symbol() else { continue };
                    let Some(info) = self.types.catalog.structs.get(&symbol) else {
                        continue;
                    };
                    for (field, (_, ty)) in info.fields.clone() {
                        if stores_borrow(&ty) {
                            let error = OwnershipError::BorrowInStorage {
                                owner: super::moves::render_symbol(symbol, self.types),
                                field,
                                ty: ty.render_mono(),
                            };
                            self.error(error, decl.id);
                        }
                    }
                }
                hir::DeclKind::Enum { name, .. } => {
                    let Ok(symbol) = name.symbol() else { continue };
                    let Some(info) = self.types.catalog.enums.get(&symbol) else {
                        continue;
                    };
                    for (variant, info) in info.variants.clone() {
                        let Ty::Func(payloads, ..) = &info.constructor_scheme.ty else {
                            continue;
                        };
                        for ty in payloads {
                            if stores_borrow(ty) {
                                let error = OwnershipError::BorrowInStorage {
                                    owner: super::moves::render_symbol(symbol, self.types),
                                    field: variant.clone(),
                                    ty: ty.render_mono(),
                                };
                                self.error(error, decl.id);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// A top-level binder cannot hold a borrowed value — unless every loan
    /// is rooted in another global (validated by provenance when the walk
    /// installs the binding; see `install_provenance`). This type-level
    /// pass keeps only the shapes the walk's provenance rule does not
    /// reach: uninitialized and destructuring binders.
    pub(crate) fn check_global_storage(&mut self, roots: &[hir::Node]) {
        for root in roots {
            let hir::Node::Decl(decl) = root else {
                continue;
            };
            let hir::DeclKind::Let { lhs, rhs, .. } = &decl.kind else {
                continue;
            };
            for (binder_id, binder) in lhs.collect_binders() {
                let Some(ty) = self.types.node_types.get(&binder_id).cloned().or_else(|| {
                    self.types
                        .schemes
                        .get(&binder)
                        .map(|scheme| scheme.ty.clone())
                }) else {
                    continue;
                };
                if matches!(ty, Ty::Func(..)) {
                    continue;
                }
                if self.grades.contains_borrowed(&ty) {
                    // Exactly the shape the walk's provenance rule covers:
                    // an initialized single binder (not `'heap`-carrying)
                    // installs provenance, which validates global-rooted
                    // loans in `install_provenance`.
                    if rhs.is_some()
                        && matches!(lhs.kind, crate::hir::PatternKind::Bind(_))
                        && !self.grades.contains_object(&ty)
                    {
                        continue;
                    }
                    let error = OwnershipError::BorrowedGlobal {
                        name: super::moves::render_symbol(binder, self.types),
                        ty: ty.render_mono(),
                    };
                    self.error(error, binder_id);
                }
            }
        }
    }

    /// The single structural pre-pass computing each free function's
    /// returned-borrow reach: which parameter indices the tail expression's
    /// borrows can point into.
    pub(crate) fn seed_return_reach<'f>(
        &mut self,
        files: impl Iterator<Item = &'f crate::hir::HirFile>,
    ) {
        let mut funcs: Vec<(crate::name_resolution::symbol::Symbol, &hir::Func)> = vec![];
        for file in files {
            for root in &file.roots {
                let hir::Node::Decl(decl) = root else {
                    continue;
                };
                match &decl.kind {
                    hir::DeclKind::Func(func) => {
                        if let Ok(symbol) = func.name.symbol() {
                            funcs.push((symbol, func));
                        }
                    }
                    hir::DeclKind::Let {
                        lhs,
                        rhs: Some(rhs),
                        ..
                    } => {
                        if let crate::hir::PatternKind::Bind(name) = &lhs.kind
                            && let ExprKind::Func(func) = &rhs.kind
                            && let Ok(symbol) = name.symbol()
                        {
                            funcs.push((symbol, func));
                        }
                    }
                    _ => {}
                }
            }
        }
        for (symbol, func) in funcs {
            let func_ty = self
                .types
                .schemes
                .get(&symbol)
                .map(|scheme| scheme.ty.clone());
            let reach = self.return_reach_of(func, func_ty.as_ref());
            if !reach.is_empty() {
                self.return_reach.insert(symbol, reach);
            }
        }
    }

    fn return_reach_of(&mut self, func: &hir::Func, func_ty: Option<&Ty>) -> Vec<usize> {
        let tail = match func.body.body.last() {
            Some(hir::Node::Expr(tail)) => tail,
            Some(hir::Node::Stmt(hir::Stmt {
                kind: hir::StmtKind::Expr(tail),
                ..
            })) => tail,
            _ => return vec![],
        };
        if !self.grades.contains_borrowed(&tail.ty) {
            return vec![];
        }
        let saved_borrowed = std::mem::take(&mut self.borrowed_params);
        let saved_param_tys = std::mem::take(&mut self.param_tys);
        let mut state = MoveState::default();
        self.seed_params(&func.params, func_ty, &mut state);
        // For reach purposes each borrowed parameter's provenance must name
        // itself as the owner (the body seed deliberately leaves owners
        // empty so self-mutation doesn't invalidate the seed).
        for param in &func.params {
            if let Ok(symbol) = param.name.symbol()
                && self.borrowed_params.contains(&symbol)
            {
                let place = Place::root(symbol);
                let kind = state
                    .borrowed_roots
                    .get(&symbol)
                    .copied()
                    .unwrap_or(Perm::Shared);
                state.provenances.insert(
                    place.clone(),
                    Provenance::direct(Origin::BorrowedParam, Some(place), kind),
                );
            }
        }
        let provenance = self.expr_provenance(tail, &state);
        self.borrowed_params = saved_borrowed;
        self.param_tys = saved_param_tys;

        let mut indices = vec![];
        for loan in &provenance.loans {
            let Some(owner) = &loan.owner else { continue };
            if let Some(index) = func
                .params
                .iter()
                .position(|param| param.name.symbol().ok() == Some(owner.root))
                && !indices.contains(&index)
            {
                indices.push(index);
            }
        }
        indices
    }

    fn origin_of_root(&self, root: crate::name_resolution::symbol::Symbol) -> Origin {
        use crate::name_resolution::symbol::Symbol;
        match root {
            Symbol::ParamLocal(_) => {
                if self.borrowed_params.contains(&root) {
                    Origin::BorrowedParam
                } else {
                    Origin::OwnedParam
                }
            }
            Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) => Origin::Local,
            Symbol::Global(_) => Origin::Static,
            _ => Origin::Unknown,
        }
    }

    pub(crate) fn call_provenance(
        &mut self,
        callee: &hir::Expr,
        args: &[hir::CallArg],
        state: &MoveState,
    ) -> Provenance {
        // Method call: a borrowed self parameter means the result borrows
        // from the receiver.
        if let ExprKind::Member(Some(receiver), _) = &callee.kind {
            let self_is_borrow = self
                .member_callable_params(callee)
                .as_ref()
                .and_then(|params| params.first())
                .is_some_and(|param| matches!(param, Ty::Borrow(..)));
            if self_is_borrow {
                if let Some(receiver_place) = self.place(receiver) {
                    let root = Place::root(receiver_place.root);
                    if let Some(provenance) = state
                        .provenances
                        .get(&receiver_place)
                        .or_else(|| state.provenances.get(&root))
                    {
                        return provenance.clone();
                    }
                    return Provenance::direct(
                        self.origin_of_root(receiver_place.root),
                        Some(receiver_place),
                        Perm::Shared,
                    );
                }
                // A chained receiver (itself a call) carries its own
                // provenance through.
                return self.expr_provenance(receiver, state);
            }
            // Owned-self method: borrows can only come from the value
            // parameters (falling back to the callee expression's own
            // bound-method type when the member's scheme is unavailable).
            let value_params = self
                .member_callable_params(callee)
                .map(|params| params.get(1..).unwrap_or(&[]).to_vec())
                .or_else(|| callee_param_tys(callee));
            return match value_params {
                Some(params) => self.per_param_provenance(args, &params, None, state),
                None => Provenance::unknown(Perm::Shared),
            };
        }

        // Constructor: borrowed content flows from the borrow-relevant
        // payload arguments (all arguments when the parameter types are
        // unknown).
        if matches!(callee.kind, ExprKind::Constructor(_)) {
            match callee_param_tys(callee) {
                Some(params) => return self.per_param_provenance(args, &params, None, state),
                None => {
                    let mut provenance = Provenance::default();
                    for arg in args {
                        provenance = provenance.union(self.expr_provenance(&arg.value, state));
                    }
                    return provenance;
                }
            }
        }

        // Free function: restrict to the parameter indices the callee's
        // returned borrow can actually reach, when the summary is known.
        let reach = match &callee.kind {
            ExprKind::Variable(name) => name
                .symbol()
                .ok()
                .and_then(|symbol| self.return_reach.get(&symbol).cloned()),
            _ => None,
        };
        match callee_param_tys(callee) {
            Some(params) => self.per_param_provenance(args, &params, reach.as_deref(), state),
            None => Provenance::unknown(Perm::Shared),
        }
    }

    /// Per-parameter provenance (the legacy `input_provenance` shape): a
    /// `&`-typed parameter borrows its argument directly; a borrow-containing
    /// parameter carries the argument's provenance; everything else
    /// contributes nothing. Restricted to the reached indices when the
    /// callee's summary is known. An empty result means "borrows nothing" —
    /// distinct from unknown.
    fn per_param_provenance(
        &mut self,
        args: &[hir::CallArg],
        params: &[Ty],
        reach: Option<&[usize]>,
        state: &MoveState,
    ) -> Provenance {
        let mut provenance = Provenance::default();
        for (index, (arg, param)) in args.iter().zip(params).enumerate() {
            if let Some(reach) = reach
                && !reach.contains(&index)
            {
                continue;
            }
            match param {
                Ty::Borrow(kind, _) => {
                    provenance =
                        provenance.union(self.direct_borrow_provenance(&arg.value, *kind, state));
                }
                _ if self.grades.contains_borrowed(param) => {
                    provenance = provenance.union(self.expr_provenance(&arg.value, state));
                }
                _ => {}
            }
        }
        provenance
    }

    /// A `&`-typed parameter borrows its argument place at `kind`.
    fn direct_borrow_provenance(
        &mut self,
        expr: &hir::Expr,
        kind: Perm,
        state: &MoveState,
    ) -> Provenance {
        if let Some(place) = self.place(expr) {
            let root = Place::root(place.root);
            if let Some(provenance) = state
                .provenances
                .get(&place)
                .or_else(|| state.provenances.get(&root))
            {
                return provenance.clone().with_kind(kind);
            }
            return Provenance::direct(self.origin_of_root(place.root), Some(place), kind);
        }
        self.expr_provenance(expr, state).with_kind(kind)
    }

    /// Install a borrowed binding: conflict-check and record each loan, and
    /// remember the borrower's provenance and borrow classification.
    pub(crate) fn install_provenance(
        &mut self,
        node: NodeID,
        borrower: Place,
        borrower_ty: &Ty,
        provenance: Provenance,
        state: &mut MoveState,
    ) {
        // A global binder may only borrow other globals — everything else
        // dies before the global does. Owners recorded in `global_borrows`
        // become immutable program-wide (`check_flow` rejects function-body
        // assignments to them, so the borrow cannot dangle).
        if matches!(
            borrower.root,
            crate::name_resolution::symbol::Symbol::Global(_)
        ) && borrower.fields.is_empty()
        {
            for loan in &provenance.loans {
                match &loan.owner {
                    Some(owner)
                        if matches!(
                            owner.root,
                            crate::name_resolution::symbol::Symbol::Global(_)
                        ) =>
                    {
                        if self.recording {
                            self.global_borrows.insert(owner.root, borrower.root);
                        }
                    }
                    _ => {
                        let error = OwnershipError::BorrowedGlobal {
                            name: self.render(&borrower),
                            ty: borrower_ty.render_mono(),
                        };
                        self.error(error, node);
                    }
                }
            }
        }
        for loan in &provenance.loans {
            if let Some(owner) = &loan.owner {
                self.check_borrow_conflicts(node, owner, loan.kind, Some(&borrower), state);
                if self.recording {
                    self.facts.borrows.push(super::FlowBorrowFact {
                        node,
                        borrower: self.render(&borrower),
                        owner: self.render(owner),
                        exclusive: loan.kind.is_exclusive(),
                    });
                }
                state.add_loan(borrower.clone(), owner.clone(), loan.kind);
            }
        }
        if self.grades.is_borrowed_value(borrower_ty) && borrower.fields.is_empty() {
            let kind = match borrower_ty {
                Ty::Borrow(perm, _) => *perm,
                _ => provenance
                    .loans
                    .first()
                    .map(|loan| loan.kind)
                    .unwrap_or(Perm::Shared),
            };
            state.borrowed_roots.insert(borrower.root, kind);
            if !kind.is_exclusive() {
                state.shared_borrow_roots.insert(borrower.root);
            }
        }
        state.invalid_borrows.remove(&borrower);
        state.provenances.insert(borrower, provenance);
    }

    /// Local binding of a borrow-containing value: unknown provenance is an
    /// error unless the type is a plain `&T` of a copy inner.
    pub(crate) fn validate_local_provenance(
        &mut self,
        node: NodeID,
        ty: &Ty,
        provenance: &Provenance,
    ) {
        if !provenance.has_unknown() {
            return;
        }
        if let Ty::Borrow(_, inner) = ty
            && self.grades.is_copy(inner)
        {
            return;
        }
        if self.core_raw_ptr_exception(ty) {
            return;
        }
        let error = OwnershipError::UnknownBorrowProvenance {
            ty: ty.render_mono(),
        };
        self.error(error, node);
    }

    /// Returning a borrow-containing value: tier 1 (parameter-derived) is
    /// fine; unknown provenance and function-owned borrows are errors.
    pub(crate) fn check_return_provenance(&mut self, expr: &hir::Expr, state: &MoveState) {
        let provenance = self.expr_provenance(expr, state);
        if provenance.has_unknown() {
            if self.core_raw_ptr_exception(&expr.ty) {
                return;
            }
            let error = OwnershipError::UnknownBorrowProvenance {
                ty: expr.ty.render_mono(),
            };
            self.error(error, expr.id);
            return;
        }
        if provenance.has_function_owned() {
            let error = OwnershipError::ReturningLocalBorrow {
                ty: expr.ty.render_mono(),
            };
            self.error(error, expr.id);
        }
    }

    /// Core builds borrowed views over raw pointers; those provenances are
    /// legitimately unknown there.
    fn core_raw_ptr_exception(&self, ty: &Ty) -> bool {
        use std::ops::ControlFlow;
        self.module_id == crate::compiling::module::ModuleId::Core
            && ty
                .try_visit(&mut |t| match t {
                    Ty::Nominal(symbol, _)
                        if *symbol == crate::name_resolution::symbol::Symbol::RawPtr =>
                    {
                        ControlFlow::Break(())
                    }
                    _ => ControlFlow::Continue(()),
                })
                .is_break()
    }
}

/// A syntactic `&T` in stored position (not under a function type: a
/// function value whose signature mentions borrows is fine to store).
fn stores_borrow(ty: &Ty) -> bool {
    match ty {
        Ty::Borrow(..) => true,
        Ty::Unique(inner) => stores_borrow(inner),
        Ty::Nominal(_, args) => args.iter().any(stores_borrow),
        Ty::Tuple(items) => items.iter().any(stores_borrow),
        Ty::Record(row) => row.fields.iter().any(|(_, field)| stores_borrow(field)),
        Ty::Func(..) | Ty::Any { .. } | Ty::Proj(..) | Ty::Var(_) | Ty::Param(_) | Ty::Error => {
            false
        }
    }
}

fn callee_param_tys(callee: &hir::Expr) -> Option<Vec<Ty>> {
    super::moves::func_params(&callee.ty)
}

pub(crate) fn perm_name(perm: Perm) -> &'static str {
    if perm.is_exclusive() {
        "mutable"
    } else {
        "shared"
    }
}
