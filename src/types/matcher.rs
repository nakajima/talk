use derive_visitor::Drive;
use derive_visitor::Visitor;
use indexmap::{IndexSet, indexset};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    diagnostic::{Diagnostic, Severity},
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        row::Row,
        ty::Ty,
        type_error::TypeError,
        type_session::Types,
        typed_ast::{
            TypedAST, TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern, TypedPatternKind,
            TypedRecordFieldPattern, TypedRecordFieldPatternKind,
        },
    },
};

pub struct MatcherCheckResult {
    pub diagnostics: IndexSet<Diagnostic<TypeError>>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum RequiredConstructor {
    LiteralTrue,
    LiteralFalse,
    Int,
    Variant { name: String },
    Tuple,
    Record,
    Nominal,
    Infinite,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum Constructor {
    LiteralTrue,
    LiteralFalse,
    LiteralInt(String),
    LiteralFloat(String),
    Variant(String),
    Tuple,
    Record,
}

enum ConstructorSet {
    Finite(IndexSet<Constructor>),
    Infinite,
}

type PatternMatrix = Vec<Vec<TypedPattern<Ty>>>;

impl From<Constructor> for RequiredConstructor {
    fn from(value: Constructor) -> Self {
        match value {
            Constructor::LiteralTrue => Self::LiteralTrue,
            Constructor::LiteralFalse => Self::LiteralFalse,
            Constructor::Variant(name) => Self::Variant { name },
            Constructor::Tuple => Self::Tuple,
            Constructor::Record => Self::Record,
            Constructor::LiteralInt(_) | Constructor::LiteralFloat(_) => Self::Infinite,
        }
    }
}

pub fn check_ast(
    ast: &TypedAST<Ty>,
    types: &Types,
    symbol_names: &FxHashMap<Symbol, String>,
) -> MatcherCheckResult {
    let mut checker = PatternChecker::new(types, symbol_names);

    for root in ast.roots() {
        root.drive(&mut checker);
    }

    MatcherCheckResult {
        diagnostics: checker.diagnostics,
    }
}

type TypedExprTy = TypedExpr<Ty>;

#[derive(Visitor)]
#[visitor(TypedExprTy(enter))]
struct PatternChecker<'a> {
    types: &'a Types,
    symbol_names: &'a FxHashMap<Symbol, String>,
    diagnostics: IndexSet<Diagnostic<TypeError>>,
}

impl<'a> PatternChecker<'a> {
    fn new(types: &'a Types, symbol_names: &'a FxHashMap<Symbol, String>) -> Self {
        Self {
            types,
            symbol_names,
            diagnostics: Default::default(),
        }
    }

    fn enter_typed_expr_ty(&mut self, expr: &TypedExprTy) {
        if let TypedExprKind::Match(scrutinee, arms) = &expr.kind {
            for arm in arms {
                self.check_pattern(&arm.pattern);
            }
            self.check_match(scrutinee, arms);
        }
    }

    fn check_pattern(&mut self, pattern: &TypedPattern<Ty>) {
        match &pattern.kind {
            TypedPatternKind::Or(patterns) => {
                if let Some(first) = patterns.first() {
                    let expected = self.binder_set(first);
                    for alt in patterns.iter().skip(1) {
                        let actual = self.binder_set(alt);
                        if actual != expected {
                            self.diagnostics.insert(Diagnostic {
                                id: pattern.id,
                                severity: Severity::Error,
                                kind: TypeError::OrPatternBinderMismatch,
                            });
                            break;
                        }
                    }
                }

                for pattern in patterns {
                    self.check_pattern(pattern);
                }
            }
            TypedPatternKind::Tuple(patterns) => {
                for pattern in patterns {
                    self.check_pattern(pattern);
                }
            }
            TypedPatternKind::Variant { fields, .. } => {
                for pattern in fields {
                    self.check_pattern(pattern);
                }
            }
            TypedPatternKind::Record { fields } => {
                self.check_record_pattern(pattern, fields);
                for field in fields {
                    if let TypedRecordFieldPatternKind::Equals { value, .. } = &field.kind {
                        self.check_pattern(value);
                    }
                }
            }
            TypedPatternKind::Struct { fields, .. } => {
                for field in fields {
                    self.check_pattern(field);
                }
            }
            TypedPatternKind::Bind(_)
            | TypedPatternKind::Wildcard
            | TypedPatternKind::LiteralInt(_)
            | TypedPatternKind::LiteralFloat(_)
            | TypedPatternKind::LiteralTrue
            | TypedPatternKind::LiteralFalse => {}
        }
    }

    fn check_match(&mut self, scrutinee: &TypedExpr<Ty>, arms: &[TypedMatchArm<Ty>]) {
        let patterns: Vec<TypedPattern<Ty>> = arms.iter().map(|arm| arm.pattern.clone()).collect();
        self.check_match_patterns(scrutinee, &patterns);
    }

    fn check_match_patterns(&mut self, scrutinee: &TypedExpr<Ty>, patterns: &[TypedPattern<Ty>]) {
        let mut matrix: PatternMatrix = vec![];
        for pattern in patterns {
            let row = vec![pattern.clone()];
            if !self.is_useful(&matrix, &row) {
                self.diagnostics.insert(Diagnostic {
                    id: pattern.id,
                    severity: Severity::Warn,
                    kind: TypeError::UselessMatchArm,
                });
            }
            matrix.push(row);
        }

        let wildcard_row = vec![self.wildcard_pattern(scrutinee.ty.clone())];
        if self.is_useful(&matrix, &wildcard_row) {
            let mut missing = self.missing_constructors(&matrix, &scrutinee.ty);
            if missing.is_empty() {
                missing.push(RequiredConstructor::Infinite);
            }
            self.diagnostics.insert(Diagnostic {
                id: scrutinee.id,
                severity: Severity::Error,
                kind: TypeError::NonExhaustiveMatch(missing),
            });
        }
    }

    fn is_useful(&self, matrix: &PatternMatrix, row: &[TypedPattern<Ty>]) -> bool {
        if row.is_empty() {
            return matrix.is_empty();
        }

        let head = &row[0];
        let tail = &row[1..];

        if let TypedPatternKind::Or(patterns) = &head.kind {
            return patterns.iter().any(|pattern| {
                let mut expanded = Vec::with_capacity(row.len());
                expanded.push(pattern.clone());
                expanded.extend_from_slice(tail);
                self.is_useful(matrix, &expanded)
            });
        }

        if self.is_wildcard(head) {
            let constructors = self.constructors_in_matrix(matrix);
            match self.constructors_for_type(&head.ty) {
                ConstructorSet::Finite(full) if full.is_subset(&constructors) => {
                    for constructor in full.iter() {
                        let specialized_matrix =
                            self.specialize_matrix(matrix, constructor, &head.ty);
                        let mut specialized_row =
                            self.wildcards_for_constructor(constructor, &head.ty);
                        specialized_row.extend_from_slice(tail);
                        if self.is_useful(&specialized_matrix, &specialized_row) {
                            return true;
                        }
                    }
                    false
                }
                _ => {
                    let default = self.default_matrix(matrix);
                    self.is_useful(&default, tail)
                }
            }
        } else {
            let Some(constructor) = self.pattern_constructor(head) else {
                return true;
            };
            let specialized_matrix = self.specialize_matrix(matrix, &constructor, &head.ty);
            let mut specialized_row = self.specialize_row(head, &constructor, &head.ty);
            specialized_row.extend_from_slice(tail);
            self.is_useful(&specialized_matrix, &specialized_row)
        }
    }

    fn constructors_for_type(&self, ty: &Ty) -> ConstructorSet {
        match ty {
            Ty::Primitive(sym) => match *sym {
                Symbol::Bool => ConstructorSet::Finite(indexset! {
                    Constructor::LiteralTrue,
                    Constructor::LiteralFalse,
                }),
                Symbol::Int | Symbol::Float => ConstructorSet::Infinite,
                _ => ConstructorSet::Infinite,
            },
            Ty::Tuple(_) => ConstructorSet::Finite(indexset! { Constructor::Tuple }),
            Ty::Record(_, _) => ConstructorSet::Finite(indexset! { Constructor::Record }),
            Ty::Nominal { symbol, .. } => {
                let Some(nominal) = self.types.catalog.nominals.get(symbol) else {
                    return ConstructorSet::Infinite;
                };
                if nominal.variants.is_empty() {
                    return ConstructorSet::Infinite;
                }
                let constructors = nominal
                    .variants
                    .keys()
                    .map(|label| Constructor::Variant(label.to_string()))
                    .collect::<IndexSet<_>>();
                ConstructorSet::Finite(constructors)
            }
            Ty::Func(..) | Ty::Constructor { .. } | Ty::Param(..) => ConstructorSet::Infinite,
        }
    }

    fn constructors_in_matrix(&self, matrix: &PatternMatrix) -> IndexSet<Constructor> {
        let mut constructors = IndexSet::new();
        for row in matrix {
            for expanded in self.expand_or_row_head(row) {
                let Some(head) = expanded.first() else {
                    continue;
                };
                if let Some(constructor) = self.pattern_constructor(head) {
                    constructors.insert(constructor);
                }
            }
        }
        constructors
    }

    fn pattern_constructor(&self, pattern: &TypedPattern<Ty>) -> Option<Constructor> {
        match &pattern.kind {
            TypedPatternKind::LiteralTrue => Some(Constructor::LiteralTrue),
            TypedPatternKind::LiteralFalse => Some(Constructor::LiteralFalse),
            TypedPatternKind::LiteralInt(value) => Some(Constructor::LiteralInt(value.clone())),
            TypedPatternKind::LiteralFloat(value) => Some(Constructor::LiteralFloat(value.clone())),
            TypedPatternKind::Variant { variant_name, .. } => {
                Some(Constructor::Variant(variant_name.clone()))
            }
            TypedPatternKind::Tuple(_) => Some(Constructor::Tuple),
            TypedPatternKind::Record { .. } => Some(Constructor::Record),
            TypedPatternKind::Bind(_) | TypedPatternKind::Wildcard | TypedPatternKind::Or(_) => {
                None
            }
            TypedPatternKind::Struct { .. } => None,
        }
    }

    fn expand_or_row_head(&self, row: &[TypedPattern<Ty>]) -> PatternMatrix {
        let Some(head) = row.first() else {
            return vec![vec![]];
        };

        if let TypedPatternKind::Or(patterns) = &head.kind {
            let mut expanded = Vec::with_capacity(patterns.len());
            let tail = &row[1..];
            for pattern in patterns {
                let mut expanded_row = Vec::with_capacity(row.len());
                expanded_row.push(pattern.clone());
                expanded_row.extend_from_slice(tail);
                expanded.push(expanded_row);
            }
            return expanded;
        }

        vec![row.to_vec()]
    }

    fn default_matrix(&self, matrix: &PatternMatrix) -> PatternMatrix {
        let mut result = vec![];
        for row in matrix {
            for expanded in self.expand_or_row_head(row) {
                if expanded.is_empty() {
                    continue;
                }
                if self.is_wildcard(&expanded[0]) {
                    result.push(expanded[1..].to_vec());
                }
            }
        }
        result
    }

    fn specialize_matrix(
        &self,
        matrix: &PatternMatrix,
        constructor: &Constructor,
        column_ty: &Ty,
    ) -> PatternMatrix {
        let mut result = vec![];
        for row in matrix {
            for expanded in self.expand_or_row_head(row) {
                if expanded.is_empty() {
                    continue;
                }
                if self.row_head_matches_constructor(&expanded[0], constructor) {
                    let mut specialized = self.specialize_row(&expanded[0], constructor, column_ty);
                    specialized.extend_from_slice(&expanded[1..]);
                    result.push(specialized);
                }
            }
        }
        result
    }

    fn row_head_matches_constructor(
        &self,
        head: &TypedPattern<Ty>,
        constructor: &Constructor,
    ) -> bool {
        if self.is_wildcard(head) {
            return true;
        }
        self.pattern_constructor(head)
            .map(|ctor| &ctor == constructor)
            .unwrap_or(false)
    }

    fn specialize_row(
        &self,
        head: &TypedPattern<Ty>,
        constructor: &Constructor,
        column_ty: &Ty,
    ) -> Vec<TypedPattern<Ty>> {
        if self.is_wildcard(head) {
            return self.wildcards_for_constructor(constructor, column_ty);
        }

        match (&head.kind, constructor) {
            (TypedPatternKind::Tuple(items), Constructor::Tuple) => items.clone(),
            (TypedPatternKind::Record { .. }, Constructor::Record) => {
                if let Ty::Record(_, row) = column_ty {
                    self.record_subpatterns(head, row)
                } else {
                    vec![]
                }
            }
            (TypedPatternKind::Variant { fields, .. }, Constructor::Variant(_)) => fields.clone(),
            (
                TypedPatternKind::LiteralTrue
                | TypedPatternKind::LiteralFalse
                | TypedPatternKind::LiteralInt(_)
                | TypedPatternKind::LiteralFloat(_),
                _,
            ) => vec![],
            _ => vec![],
        }
    }

    fn wildcards_for_constructor(
        &self,
        constructor: &Constructor,
        column_ty: &Ty,
    ) -> Vec<TypedPattern<Ty>> {
        let subtypes = self.constructor_subtypes(constructor, column_ty);
        subtypes
            .into_iter()
            .map(|ty| self.wildcard_pattern(ty))
            .collect()
    }

    fn constructor_subtypes(&self, constructor: &Constructor, column_ty: &Ty) -> Vec<Ty> {
        match constructor {
            Constructor::Tuple => match column_ty {
                Ty::Tuple(items) => items.clone(),
                _ => vec![],
            },
            Constructor::Record => match column_ty {
                Ty::Record(_, row) => self
                    .collect_row_fields(row)
                    .0
                    .into_iter()
                    .map(|(_, ty)| ty)
                    .collect(),
                _ => vec![],
            },
            Constructor::Variant(name) => match column_ty {
                Ty::Nominal { symbol, type_args } => {
                    let Some(nominal) = self.types.catalog.nominals.get(symbol) else {
                        return vec![];
                    };
                    let variants = nominal.substituted_variant_values(type_args);
                    let label = self.label_from_name(name);
                    variants.get(&label).cloned().unwrap_or_default()
                }
                _ => vec![],
            },
            Constructor::LiteralTrue
            | Constructor::LiteralFalse
            | Constructor::LiteralInt(_)
            | Constructor::LiteralFloat(_) => vec![],
        }
    }

    fn record_subpatterns(&self, pattern: &TypedPattern<Ty>, row: &Row) -> Vec<TypedPattern<Ty>> {
        let TypedPatternKind::Record { fields } = &pattern.kind else {
            return vec![];
        };
        let (row_fields, _) = self.collect_row_fields(row);

        let mut field_map: FxHashMap<Label, RecordFieldValue> = FxHashMap::default();
        let mut has_rest = false;
        for field in fields {
            match &field.kind {
                TypedRecordFieldPatternKind::Bind(symbol) => {
                    if let Some(label) = self.label_for_symbol(*symbol) {
                        field_map.insert(
                            label,
                            RecordFieldValue::Bind {
                                id: field.id,
                                symbol: *symbol,
                            },
                        );
                    }
                }
                TypedRecordFieldPatternKind::Equals { name, value } => {
                    if let Some(label) = self.label_for_symbol(*name) {
                        field_map.insert(label, RecordFieldValue::Value(value.clone()));
                    }
                }
                TypedRecordFieldPatternKind::Rest => {
                    has_rest = true;
                }
            }
        }

        row_fields
            .into_iter()
            .map(|(label, ty)| match field_map.get(&label) {
                Some(RecordFieldValue::Bind { id, symbol }) => TypedPattern {
                    id: *id,
                    ty,
                    kind: TypedPatternKind::Bind(*symbol),
                },
                Some(RecordFieldValue::Value(value)) => value.clone(),
                None if has_rest => self.wildcard_pattern(ty),
                None => self.wildcard_pattern(ty),
            })
            .collect()
    }

    fn wildcard_pattern(&self, ty: Ty) -> TypedPattern<Ty> {
        TypedPattern {
            id: NodeID::SYNTHESIZED,
            ty,
            kind: TypedPatternKind::Wildcard,
        }
    }

    fn is_wildcard(&self, pattern: &TypedPattern<Ty>) -> bool {
        matches!(
            pattern.kind,
            TypedPatternKind::Wildcard | TypedPatternKind::Bind(_)
        )
    }

    fn label_for_symbol(&self, symbol: Symbol) -> Option<Label> {
        self.symbol_names
            .get(&symbol)
            .map(|name| Label::Named(name.clone()))
    }

    fn label_from_name(&self, name: &str) -> Label {
        name.parse()
            .unwrap_or_else(|_| Label::Named(name.to_string()))
    }

    fn missing_constructors(&self, matrix: &PatternMatrix, ty: &Ty) -> Vec<RequiredConstructor> {
        let constructors = self.constructors_in_matrix(matrix);
        match self.constructors_for_type(ty) {
            ConstructorSet::Finite(full) => full
                .into_iter()
                .filter(|ctor| !constructors.contains(ctor))
                .map(RequiredConstructor::from)
                .collect(),
            ConstructorSet::Infinite => vec![RequiredConstructor::Infinite],
        }
    }

    fn collect_row_fields(&self, row: &Row) -> (Vec<(Label, Ty)>, bool) {
        let mut fields = vec![];
        let open = self.collect_row_fields_inner(row, &mut fields);
        (fields, open)
    }

    fn collect_row_fields_inner(&self, row: &Row, fields: &mut Vec<(Label, Ty)>) -> bool {
        match row {
            Row::Empty(_) => false,
            Row::Param(_) => true,
            Row::Extend { row, label, ty } => {
                fields.push((label.clone(), ty.clone()));
                self.collect_row_fields_inner(row, fields)
            }
        }
    }

    fn check_record_pattern(
        &mut self,
        pattern: &TypedPattern<Ty>,
        fields: &[TypedRecordFieldPattern<Ty>],
    ) {
        let Ty::Record(_, row) = &pattern.ty else {
            return;
        };

        let (row_fields, open) = self.collect_row_fields(row);
        let has_rest = fields
            .iter()
            .any(|field| matches!(field.kind, TypedRecordFieldPatternKind::Rest));

        if open && !has_rest {
            self.diagnostics.insert(Diagnostic {
                id: pattern.id,
                severity: Severity::Error,
                kind: TypeError::RecordPatternNeedsRest,
            });
        }

        if !open && !has_rest {
            let used_labels = self.record_pattern_labels(fields);
            let missing: Vec<String> = row_fields
                .iter()
                .filter(|(label, _)| !used_labels.contains(label))
                .map(|(label, _)| label.to_string())
                .collect();

            if !missing.is_empty() {
                self.diagnostics.insert(Diagnostic {
                    id: pattern.id,
                    severity: Severity::Error,
                    kind: TypeError::RecordPatternMissingFields(missing),
                });
            }
        }
    }

    fn record_pattern_labels(&self, fields: &[TypedRecordFieldPattern<Ty>]) -> IndexSet<Label> {
        let mut labels = IndexSet::new();
        for field in fields {
            match &field.kind {
                TypedRecordFieldPatternKind::Bind(symbol) => {
                    if let Some(label) = self.label_for_symbol(*symbol) {
                        labels.insert(label);
                    }
                }
                TypedRecordFieldPatternKind::Equals { name, .. } => {
                    if let Some(label) = self.label_for_symbol(*name) {
                        labels.insert(label);
                    }
                }
                TypedRecordFieldPatternKind::Rest => {}
            }
        }
        labels
    }

    fn binder_set(&self, pattern: &TypedPattern<Ty>) -> FxHashSet<Symbol> {
        let mut binders = FxHashSet::default();
        self.collect_binders(pattern, &mut binders);
        binders
    }

    fn collect_binders(&self, pattern: &TypedPattern<Ty>, binders: &mut FxHashSet<Symbol>) {
        match &pattern.kind {
            TypedPatternKind::Bind(symbol) => {
                binders.insert(*symbol);
            }
            TypedPatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.collect_binders(pattern, binders);
                }
            }
            TypedPatternKind::Tuple(patterns) => {
                for pattern in patterns {
                    self.collect_binders(pattern, binders);
                }
            }
            TypedPatternKind::Variant { fields, .. } => {
                for pattern in fields {
                    self.collect_binders(pattern, binders);
                }
            }
            TypedPatternKind::Record { fields } => {
                for field in fields {
                    match &field.kind {
                        TypedRecordFieldPatternKind::Bind(symbol) => {
                            binders.insert(*symbol);
                        }
                        TypedRecordFieldPatternKind::Equals { name, value } => {
                            binders.insert(*name);
                            self.collect_binders(value, binders);
                        }
                        TypedRecordFieldPatternKind::Rest => {}
                    }
                }
            }
            TypedPatternKind::Struct { fields, .. } => {
                for field in fields {
                    self.collect_binders(field, binders);
                }
            }
            TypedPatternKind::Wildcard
            | TypedPatternKind::LiteralInt(_)
            | TypedPatternKind::LiteralFloat(_)
            | TypedPatternKind::LiteralTrue
            | TypedPatternKind::LiteralFalse => {}
        }
    }
}

enum RecordFieldValue {
    Bind { id: NodeID, symbol: Symbol },
    Value(TypedPattern<Ty>),
}

pub struct Matcher<'a> {
    pub scrutinee: TypedExpr<Ty>,
    pub patterns: Vec<TypedPattern<Ty>>,
    types: &'a Types,
    symbol_names: &'a FxHashMap<Symbol, String>,
}

impl<'a> Matcher<'a> {
    pub fn check(&self) -> MatcherCheckResult {
        let mut checker = PatternChecker::new(self.types, self.symbol_names);
        checker.check_match_patterns(&self.scrutinee, &self.patterns);
        MatcherCheckResult {
            diagnostics: checker.diagnostics,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use indexmap::{IndexSet, indexset};

    use super::*;
    use crate::{
        compiling::driver::{Driver, DriverConfig, Source, Typed},
        diagnostic::Severity,
        node_id::NodeID,
        types::typed_ast::{TypedExpr, TypedExprKind, TypedStmt, TypedStmtKind},
    };

    fn matcher_for<'a>(code: &str) -> Matcher<'a> {
        let typed = Driver::new(vec![Source::from(code)], DriverConfig::new("MatcherTests"))
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let Typed {
            ast,
            types,
            resolved_names,
            ..
        } = typed.phase;

        let TypedStmt {
            kind:
                TypedStmtKind::Expr(TypedExpr {
                    kind: TypedExprKind::Match(box scrutinee, arms),
                    ..
                }),
            ..
        } = ast.stmts.into_iter().last().expect("didn't get last stmt")
        else {
            panic!("didn't get match expr");
        };

        Matcher {
            scrutinee,
            patterns: arms.into_iter().map(|arm| arm.pattern).collect(),
            types: Box::leak(Box::new(types)),
            symbol_names: Box::leak(Box::new(resolved_names.symbol_names)),
        }
    }

    fn diagnostics_for(code: &str) -> IndexSet<Diagnostic<TypeError>> {
        let typed = Driver::new(vec![Source::from(code)], DriverConfig::new("MatcherTests"))
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let Typed {
            ast,
            types,
            resolved_names,
            ..
        } = typed.phase;

        check_ast(&ast, &types, &resolved_names.symbol_names).diagnostics
    }

    #[test]
    fn match_bools() {
        assert!(
            matcher_for("match true { true -> 1, false -> 2, }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert!(
            matcher_for("match true { true | false -> 1 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert!(
            matcher_for("match true { _ -> 1 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert_eq!(
            matcher_for("match true { true -> 1}").check().diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::LiteralFalse]) }
            }
        );

        assert_eq!(
            matcher_for("match true { true | false -> 1, true -> 2 }")
                .check()
                .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Warn, kind: TypeError::UselessMatchArm }
            }
        )
    }

    #[test]
    fn match_floats() {
        assert!(
            matcher_for("match 1.5 { 1.5 -> 1, _ -> 0 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert_eq!(
            matcher_for("match 1.5 { 1.5 -> 1 }").check().diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::Infinite]) }
            }
        );
    }

    #[test]
    fn match_ints() {
        assert_eq!(
            matcher_for("match 123 { 1 -> 1, 2 -> 2, _ -> 1 }")
                .check()
                .diagnostics,
            indexset! {}
        );

        assert_eq!(
            matcher_for("match 123 { 1 -> 1, 2 -> 2 }")
                .check()
                .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::Infinite]) }
            }
        );

        assert_eq!(
            matcher_for("match 123 { _ -> 1, 1 -> 2 }")
                .check()
                .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Warn, kind: TypeError::UselessMatchArm }
            }
        );
    }

    #[test]
    fn match_tuples() {
        assert!(
            matcher_for("match (true, false) { (true, _) -> 1, (false, _) -> 2 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert!(
            matcher_for("match (true, false) { (true, true | false) -> 1, (false, _) -> 2 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert_eq!(
            matcher_for("match (true, false) { (true, _) -> 1 }")
                .check()
                .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::Infinite]) }
            }
        );

        assert_eq!(
            matcher_for(
                "match (true, false) { (true, _) -> 1, (true, false) -> 2, (false, _) -> 3 }"
            )
            .check()
            .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Warn, kind: TypeError::UselessMatchArm }
            }
        );
    }

    #[test]
    fn match_variants() {
        assert!(
            matcher_for(
                "enum Maybe<T> { case some(T) case none }\n\
                 let m = Maybe.some(1)\n\
                 match m { .some(_) -> 1, .none -> 0 }"
            )
            .check()
            .diagnostics
            .is_empty()
        );

        assert!(
            matcher_for(
                "enum Maybe<T> { case some(T) case none }\n\
                 let m = Maybe.some(1)\n\
                 match m { .some(_) | .none -> 1 }"
            )
            .check()
            .diagnostics
            .is_empty()
        );

        assert_eq!(
            matcher_for(
                "enum Maybe<T> { case some(T) case none }\n\
                 let m = Maybe.some(1)\n\
                 match m { .some(_) -> 1 }"
            )
            .check()
            .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::Variant { name: "none".into() }]) }
            }
        );

        assert_eq!(
            matcher_for(
                "enum Maybe<T> { case some(T) case none }\n\
                 let m = Maybe.some(1)\n\
                 match m { .some(_) -> 1, .none -> 0, .some(1) -> 2 }"
            )
            .check()
            .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Warn, kind: TypeError::UselessMatchArm }
            }
        );
    }

    #[test]
    fn or_pattern_binder_mismatch() {
        assert_eq!(
            diagnostics_for("match true { x | _ -> 1 }"),
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::OrPatternBinderMismatch }
            }
        );
    }

    #[test]
    fn record_patterns() {
        assert_eq!(
            diagnostics_for("let r = { x: 1, y: 2 }\nmatch r { { x } -> 1 }"),
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::RecordPatternMissingFields(vec!["y".into()]) }
            }
        );

        assert!(diagnostics_for("let r = { x: 1, y: 2 }\nmatch r { { x, .. } -> 1 }").is_empty());

        assert_eq!(
            diagnostics_for("func f(r) { match r { { x } -> 1 } }"),
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::RecordPatternNeedsRest }
            }
        );

        assert!(diagnostics_for("func f(r) { match r { { x, .. } -> 1 } }").is_empty());
    }
}
