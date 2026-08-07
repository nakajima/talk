use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    compiling::module::ModuleId,
    name::Name,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        parameter::Parameter,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        record_field::RecordField,
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
};

/// One scope carried by a hygienic syntax identifier.
///
/// Lexical scopes identify an existing source scope. Expansion scopes are
/// fresh per expansion and distinguish introduced bindings from caller names.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum SyntaxScope {
    Lexical(NodeID),
    Expansion { namespace: u64, ordinal: u64 },
    Module(ModuleId),
}

/// An immutable set of scopes attached to one identifier occurrence.
#[derive(
    Clone,
    Debug,
    Default,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    serde::Serialize,
    serde::Deserialize,
)]
pub struct SyntaxContext(Vec<SyntaxScope>);

impl SyntaxContext {
    pub fn new(scopes: impl IntoIterator<Item = SyntaxScope>) -> Self {
        let mut scopes: Vec<_> = scopes.into_iter().collect();
        scopes.sort_unstable();
        scopes.dedup();
        Self(scopes)
    }

    pub fn lexical(scope: NodeID) -> Self {
        Self(vec![SyntaxScope::Lexical(scope)])
    }

    pub fn with_scope(&self, scope: SyntaxScope) -> Self {
        Self::new(self.0.iter().copied().chain(std::iter::once(scope)))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn has_expansion_scope(&self) -> bool {
        self.0
            .iter()
            .any(|scope| matches!(scope, SyntaxScope::Expansion { .. }))
    }

    pub fn lexical_scopes(&self) -> impl Iterator<Item = NodeID> + '_ {
        self.0.iter().filter_map(|scope| match scope {
            SyntaxScope::Lexical(node) => Some(*node),
            SyntaxScope::Expansion { .. } | SyntaxScope::Module(_) => None,
        })
    }

    pub fn definition_module(&self) -> Option<ModuleId> {
        self.0.iter().find_map(|scope| match scope {
            SyntaxScope::Module(module) => Some(*module),
            SyntaxScope::Lexical(_) | SyntaxScope::Expansion { .. } => None,
        })
    }

    pub fn scopes(&self) -> &[SyntaxScope] {
        &self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SyntaxOrigin {
    UseSite,
    DefinitionSite,
}

/// One identifier emitted by Talk-side syntax materialization.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MaterializedIdentifier {
    pub text: String,
    pub span: Span,
    pub lexeme: Span,
    pub context: SyntaxContext,
    pub origin: SyntaxOrigin,
    pub source_span: Span,
    pub source_lexeme: Span,
}

/// Hygiene metadata parallel to a materialized AST.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SyntaxMetadata {
    pub identifiers: Vec<MaterializedIdentifier>,
}

impl SyntaxMetadata {
    pub fn new(identifiers: Vec<MaterializedIdentifier>) -> Self {
        Self { identifiers }
    }

    pub fn context_at(&self, lexeme: Span, text: &str) -> Option<&SyntaxContext> {
        self.identifiers
            .iter()
            .find(|identifier| identifier.lexeme == lexeme && identifier.text == text)
            .map(|identifier| &identifier.context)
    }

    fn context_within(&self, span: Span, text: &str) -> Option<&SyntaxContext> {
        self.identifiers
            .iter()
            .find(|identifier| {
                identifier.text == text
                    && identifier.lexeme.file_id == span.file_id
                    && identifier.lexeme.start >= span.start
                    && identifier.lexeme.end <= span.end
            })
            .map(|identifier| &identifier.context)
    }

    pub fn apply(&self, roots: &mut [Node]) {
        let mut annotator = SyntaxAnnotator { metadata: self };
        for root in roots {
            root.drive_mut(&mut annotator);
        }
    }
}

#[derive(VisitorMut)]
#[visitor(
    Decl(enter),
    Expr(enter),
    Func(enter),
    FuncSignature(enter),
    GenericDecl(enter),
    Parameter(enter),
    Pattern(enter),
    RecordField(enter),
    Stmt(enter),
    TypeAnnotation(enter)
)]
struct SyntaxAnnotator<'a> {
    metadata: &'a SyntaxMetadata,
}

impl SyntaxAnnotator<'_> {
    fn annotate(&self, name: &mut Name, span: Span) {
        if !name.is_unresolved() {
            return;
        }
        let text = name.name_str();
        let context = self
            .metadata
            .context_at(span, &text)
            .or_else(|| self.metadata.context_within(span, &text));
        if let Some(context) = context
            && !context.is_empty()
        {
            *name = Name::Syntax(text, context.clone());
        }
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        match &mut decl.kind {
            DeclKind::Effect {
                name, name_span, ..
            }
            | DeclKind::Struct {
                name, name_span, ..
            }
            | DeclKind::Protocol {
                name, name_span, ..
            }
            | DeclKind::Property {
                name, name_span, ..
            }
            | DeclKind::Enum {
                name, name_span, ..
            }
            | DeclKind::EnumVariant {
                name, name_span, ..
            } => self.annotate(name, *name_span),
            DeclKind::TypeAlias(name, span, _) => self.annotate(name, *span),
            DeclKind::Import(_)
            | DeclKind::Macro { .. }
            | DeclKind::MacroCall { .. }
            | DeclKind::Let { .. }
            | DeclKind::Init { .. }
            | DeclKind::Method { .. }
            | DeclKind::Associated { .. }
            | DeclKind::Func(_)
            | DeclKind::Extend { .. }
            | DeclKind::FuncSignature(_)
            | DeclKind::MethodRequirement { .. }
            | DeclKind::InitRequirement { .. } => {}
        }
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Variable(name) | ExprKind::Constructor(name, _) => {
                self.annotate(name, expr.span)
            }
            ExprKind::CallEffect {
                effect_name,
                effect_name_span,
                ..
            } => self.annotate(effect_name, *effect_name_span),
            _ => {}
        }
    }

    fn enter_func(&mut self, func: &mut Func) {
        self.annotate(&mut func.name, func.name_span);
        for (name, span) in func.effects.names.iter_mut().zip(&func.effects.spans) {
            self.annotate(name, *span);
        }
        for capture in &mut func.captures {
            self.annotate(&mut capture.name, capture.span);
        }
    }

    fn enter_func_signature(&mut self, signature: &mut FuncSignature) {
        self.annotate(&mut signature.name, signature.span);
        for (name, span) in signature
            .effects
            .names
            .iter_mut()
            .zip(&signature.effects.spans)
        {
            self.annotate(name, *span);
        }
    }

    fn enter_generic_decl(&mut self, generic: &mut GenericDecl) {
        self.annotate(&mut generic.name, generic.name_span);
    }

    fn enter_parameter(&mut self, parameter: &mut Parameter) {
        self.annotate(&mut parameter.name, parameter.name_span);
    }

    fn enter_pattern(&mut self, pattern: &mut Pattern) {
        match &mut pattern.kind {
            PatternKind::Bind(name) => self.annotate(name, pattern.span),
            PatternKind::Variant {
                enum_name: Some(name),
                ..
            }
            | PatternKind::Struct {
                struct_name: Some(name),
                ..
            } => self.annotate(name, pattern.span),
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => self.annotate(name, field.span),
                        RecordFieldPatternKind::Equals {
                            name, name_span, ..
                        } => self.annotate(name, *name_span),
                        RecordFieldPatternKind::Rest => {}
                    }
                }
            }
            _ => {}
        }
    }

    fn enter_record_field(&mut self, field: &mut RecordField) {
        self.annotate(&mut field.label, field.label_span);
    }

    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } = &mut stmt.kind
        {
            self.annotate(effect_name, *effect_name_span);
        }
    }

    fn enter_type_annotation(&mut self, annotation: &mut TypeAnnotation) {
        match &mut annotation.kind {
            TypeAnnotationKind::SelfType(name) => self.annotate(name, annotation.span),
            TypeAnnotationKind::Nominal {
                name, name_span, ..
            } => self.annotate(name, *name_span),
            _ => {}
        }
    }
}
