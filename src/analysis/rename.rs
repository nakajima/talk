use derive_visitor::{Drive, Visitor};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::occurrence::{
    construction_callee_symbol, member_resolution_symbol, occurrence_at, symbol_exported_by_import,
    symbol_for_any_assoc_binding, symbol_for_associated_type_member,
};
use crate::analysis::workspace::Workspace;
use crate::analysis::{DocumentId, TextRange};
use crate::name_resolution::symbol::{EffectId, Symbol};
use crate::node_kinds::{
    decl::Decl,
    expr::Expr,
    func::Func,
    func_signature::FuncSignature,
    generic_decl::GenericDecl,
    parameter::Parameter,
    pattern::{Pattern, RecordFieldPattern},
    stmt::Stmt,
    type_annotation::TypeAnnotation,
};
use crate::token_kind::TokenKind;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkspaceEdit {
    pub documents: Vec<DocumentEdit>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocumentEdit {
    pub document_id: DocumentId,
    pub edits: Vec<TextEdit>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub range: TextRange,
    pub replacement: String,
}

fn is_valid_identifier(name: &str) -> bool {
    // The frontend's lexing surface (ADR 0043 Stage 5): valid means
    // the whole string lexes to exactly one identifier token.
    let Ok((tokens, complete)) = crate::compiling::frontend::lex(name) else {
        return false;
    };
    complete && tokens.len() == 1 && tokens[0].kind == TokenKind::Identifier
}

fn is_symbol_renamable(module: &Workspace, symbol: Symbol) -> bool {
    use crate::name_resolution::symbol::{
        AssociatedTypeId, EnumId, GlobalId, InstanceMethodId, MethodRequirementId, PropertyId,
        ProtocolId, StaticMethodId, StructId, TypeAliasId, VariantId,
    };

    match symbol {
        Symbol::Builtin(..)
        | Symbol::Main
        | Symbol::Library
        | Symbol::Synthesized(..)
        | Symbol::Initializer(..) => false,

        Symbol::Struct(StructId { module_id, .. })
        | Symbol::Enum(EnumId { module_id, .. })
        | Symbol::TypeAlias(TypeAliasId { module_id, .. })
        | Symbol::Global(GlobalId { module_id, .. })
        | Symbol::Property(PropertyId { module_id, .. })
        | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
        | Symbol::StaticMethod(StaticMethodId { module_id, .. })
        | Symbol::Variant(VariantId { module_id, .. })
        | Symbol::Protocol(ProtocolId { module_id, .. })
        | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
        | Symbol::Effect(EffectId { module_id, .. })
        | Symbol::MethodRequirement(MethodRequirementId { module_id, .. }) => {
            module_id == module.local_module_id
        }

        Symbol::TypeParameter(..)
        | Symbol::DeclaredLocal(..)
        | Symbol::PatternBindLocal(..)
        | Symbol::ParamLocal(..) => true,
    }
}

pub fn rename_at(
    module: &Workspace,
    document_id: &DocumentId,
    byte_offset: u32,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    if !is_valid_identifier(new_name) {
        return None;
    }

    let symbol = rename_symbol_at_offset(module, document_id, byte_offset)?;
    if !is_symbol_renamable(module, symbol) {
        return None;
    }

    // A rename never manufactures a collision (ADR 0042): refuse
    // conservatively when the new name is already bound to a different
    // symbol in any scope that binds the renamed one.
    let creates_collision = module.resolved_names.scopes.values().any(|scope| {
        let binds_symbol = scope
            .types
            .values()
            .chain(scope.values.values())
            .any(|&bound| bound == symbol);
        binds_symbol
            && scope
                .types
                .get(new_name)
                .or_else(|| scope.values.get(new_name))
                .is_some_and(|&existing| existing != symbol)
    });
    if creates_collision {
        return None;
    }

    let mut documents = Vec::new();
    for (idx, doc_id) in module.file_id_to_document.iter().enumerate() {
        let Some(ast) = module.asts.get(idx).and_then(|ast| ast.as_ref()) else {
            continue;
        };
        let (spans, label_expansions) = rename_spans_in_ast(module, ast, symbol);
        let mut edits: Vec<TextEdit> = spans
            .into_iter()
            .map(|(start, end)| TextEdit {
                range: TextRange::new(start, end),
                // A same-name labeled parameter keeps its external label
                // by expanding to the two-name form (ADR 0041).
                replacement: match label_expansions.get(&(start, end)) {
                    Some(label) => format!("{label} {new_name}"),
                    None => new_name.to_string(),
                },
            })
            .collect();

        if edits.is_empty() {
            continue;
        }

        edits.sort_by_key(|edit| (edit.range.start, edit.range.end));
        documents.push(DocumentEdit {
            document_id: doc_id.clone(),
            edits,
        });
    }

    if documents.is_empty() {
        return None;
    }

    Some(WorkspaceEdit { documents })
}

fn rename_symbol_at_offset(
    module: &Workspace,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Option<Symbol> {
    occurrence_at(module, document_id, byte_offset).map(|occurrence| occurrence.symbol)
}

fn target_import_aliases(
    module: &Workspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    symbol: Symbol,
) -> FxHashSet<String> {
    use crate::node_kinds::decl::{DeclKind, ImportedSymbols};

    let mut aliases = FxHashSet::default();
    for node in &ast.roots {
        let crate::node::Node::Decl(decl) = node else {
            continue;
        };
        let DeclKind::Import(import) = &decl.kind else {
            continue;
        };
        let ImportedSymbols::Named(imported_symbols) = &import.symbols else {
            continue;
        };
        for imported in imported_symbols {
            if let Some(alias) = &imported.alias
                && symbol_exported_by_import(module, &ast.path, import, &imported.name)
                    == Some(symbol)
            {
                aliases.insert(alias.clone());
            }
        }
    }
    aliases
}

fn rename_spans_in_ast(
    module: &Workspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    symbol: Symbol,
) -> (Vec<(u32, u32)>, FxHashMap<(u32, u32), String>) {
    let target_import_aliases = target_import_aliases(module, ast, symbol);
    let mut collector = RenameCollector {
        module,
        ast,
        target: symbol,
        target_import_aliases,
        spans: FxHashSet::default(),
        label_expansions: FxHashMap::default(),
        func_origins: Vec::new(),
    };

    for root in &ast.roots {
        root.drive(&mut collector);
    }

    let mut spans: Vec<(u32, u32)> = collector.spans.into_iter().collect();
    spans.sort_unstable();
    (spans, collector.label_expansions)
}

#[derive(Visitor)]
#[visitor(
    Decl(enter),
    Expr(enter),
    Func(enter, exit),
    FuncSignature(enter),
    GenericDecl(enter),
    Parameter(enter),
    Pattern(enter),
    RecordFieldPattern(enter),
    Stmt(enter),
    TypeAnnotation(enter)
)]
struct RenameCollector<'a> {
    module: &'a Workspace,
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    target: Symbol,
    target_import_aliases: FxHashSet<String>,
    spans: FxHashSet<(u32, u32)>,
    // Same-name labeled parameter declarations whose external label must
    // survive a binder rename (ADR 0041): declaration span -> label to keep.
    // `func id(value: Int)` renamed to `item` becomes
    // `func id(value item: Int)`.
    label_expansions: FxHashMap<(u32, u32), String>,
    // Enclosing function origins; anonymous closures never expand.
    func_origins: Vec<crate::node_kinds::func::FuncOrigin>,
}

impl RenameCollector<'_> {
    fn push_span(&mut self, span: crate::span::Span) {
        self.spans.insert((span.start, span.end));
    }

    fn push_u32_span(&mut self, start: u32, end: u32) {
        self.spans.insert((start, end));
    }

    fn should_rename_visible_reference(&self, name: &crate::name::Name) -> bool {
        !self.target_import_aliases.contains(&name.name_str())
    }

    fn enter_decl(&mut self, decl: &crate::node_kinds::decl::Decl) {
        use crate::node_kinds::decl::DeclKind;

        match &decl.kind {
            DeclKind::Import(import) => self.enter_import_decl(import),
            DeclKind::Struct {
                name, name_span, ..
            }
            | DeclKind::Protocol {
                name, name_span, ..
            }
            | DeclKind::Enum {
                name, name_span, ..
            }
            | DeclKind::Property {
                name, name_span, ..
            }
            | DeclKind::Effect {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            DeclKind::TypeAlias(name, name_span, ..) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            DeclKind::EnumVariant {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            _ => {}
        }
    }

    fn enter_import_decl(&mut self, import: &crate::node_kinds::decl::Import) {
        use crate::node_kinds::decl::ImportedSymbols;

        let ImportedSymbols::Named(imported_symbols) = &import.symbols else {
            return;
        };

        for imported in imported_symbols {
            let symbol =
                symbol_exported_by_import(self.module, &self.ast.path, import, &imported.name);
            if symbol == Some(self.target) {
                self.push_span(imported.span);
            }
        }
    }

    fn enter_func(&mut self, func: &crate::node_kinds::func::Func) {
        self.func_origins.push(func.origin);
        if func.name.symbol().ok() == Some(self.target) {
            self.push_span(func.name_span);
        }
        self.push_matching_effect_spans(&func.effects);
    }

    fn exit_func(&mut self, _func: &crate::node_kinds::func::Func) {
        self.func_origins.pop();
    }

    fn enter_func_signature(&mut self, sig: &crate::node_kinds::func_signature::FuncSignature) {
        if sig.name.symbol().ok() == Some(self.target)
            && let Some(meta) = self.ast.meta.get(&sig.id)
            && let Some(tok) = meta.identifiers.first()
        {
            self.push_u32_span(tok.start, tok.end);
        }
        self.push_matching_effect_spans(&sig.effects);
    }

    fn enter_generic_decl(&mut self, generic: &crate::node_kinds::generic_decl::GenericDecl) {
        if generic.name.symbol().ok() == Some(self.target) {
            self.push_span(generic.name_span);
        }
    }

    fn enter_parameter(&mut self, param: &crate::node_kinds::parameter::Parameter) {
        if param.name.symbol().ok() == Some(self.target) {
            self.push_span(param.name_span);
            // A named callable's same-name label expands so a binder rename
            // preserves the external API (ADR 0041). Bare parameters are
            // positional, and anonymous closure parameters have no labels.
            let in_closure =
                self.func_origins.last() == Some(&crate::node_kinds::func::FuncOrigin::Expr);
            if param.uses_same_name_label_syntax() && !in_closure {
                let Some(crate::node_kinds::parameter::ParamLabel::Named(label)) = &param.label
                else {
                    unreachable!("same-name label syntax must carry a named label")
                };
                self.label_expansions
                    .insert((param.name_span.start, param.name_span.end), label.clone());
            }
        }
    }

    fn enter_pattern(&mut self, pattern: &crate::node_kinds::pattern::Pattern) {
        use crate::node_kinds::pattern::PatternKind;

        match &pattern.kind {
            PatternKind::Bind(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(pattern.span);
                }
            }
            PatternKind::Variant {
                variant_name_span, ..
            } => {
                if member_resolution_symbol(self.module.facts.member_resolutions.get(&pattern.id))
                    == Some(self.target)
                {
                    self.push_span(*variant_name_span);
                }
            }
            _ => {}
        }
    }

    fn enter_record_field_pattern(
        &mut self,
        field: &crate::node_kinds::pattern::RecordFieldPattern,
    ) {
        use crate::node_kinds::pattern::RecordFieldPatternKind;

        match &field.kind {
            RecordFieldPatternKind::Bind(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(field.span);
                }
            }
            RecordFieldPatternKind::Equals {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            RecordFieldPatternKind::Rest => {}
        }
    }

    fn enter_type_annotation(&mut self, ty: &crate::node_kinds::type_annotation::TypeAnnotation) {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;

        match &ty.kind {
            TypeAnnotationKind::Nominal {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target)
                    && self.should_rename_visible_reference(name)
                {
                    self.push_span(*name_span);
                }
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_span,
                ..
            } => {
                if symbol_for_associated_type_member(self.module, base, member) == Some(self.target)
                {
                    self.push_span(*member_span);
                }
            }
            TypeAnnotationKind::Any {
                protocol,
                assoc_bindings,
            } => {
                for binding in assoc_bindings {
                    if symbol_for_any_assoc_binding(self.module, protocol, binding)
                        == Some(self.target)
                    {
                        self.push_span(binding.name_span);
                    }
                }
            }
            TypeAnnotationKind::Func { effects, .. } => {
                self.push_matching_effect_spans(effects);
            }
            _ => {}
        }
    }

    fn enter_stmt(&mut self, stmt: &crate::node_kinds::stmt::Stmt) {
        use crate::node_kinds::stmt::StmtKind;

        let StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } = &stmt.kind
        else {
            return;
        };

        if effect_name.symbol().ok() == Some(self.target) {
            self.push_span(*effect_name_span);
        }
    }

    fn enter_expr(&mut self, expr: &crate::node_kinds::expr::Expr) {
        use crate::node_kinds::expr::ExprKind;

        match &expr.kind {
            ExprKind::Variable(name) | ExprKind::Constructor(name, ..) => {
                if name.symbol().ok() == Some(self.target)
                    && self.should_rename_visible_reference(name)
                {
                    self.push_span(expr.span);
                }
            }
            ExprKind::Member(_, _, label_span) => {
                if member_resolution_symbol(self.module.facts.member_resolutions.get(&expr.id))
                    == Some(self.target)
                {
                    self.push_span(*label_span);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                if let Some(struct_info) = construction_callee_symbol(callee)
                    .and_then(|symbol| self.module.types.catalog.structs.get(&symbol))
                {
                    for arg in args {
                        if struct_info
                            .fields
                            .get(&arg.label.to_string())
                            .is_some_and(|(symbol, _)| *symbol == self.target)
                        {
                            self.push_span(arg.label_span);
                        }
                    }
                }
            }
            ExprKind::CallEffect {
                effect_name,
                effect_name_span,
                ..
            } => {
                if effect_name.symbol().ok() == Some(self.target) {
                    self.push_span(*effect_name_span);
                }
            }
            _ => {}
        }
    }

    fn push_matching_effect_spans(&mut self, effects: &crate::node_kinds::func::EffectSet) {
        for (name, span) in effects.names.iter().zip(effects.spans.iter()) {
            if name.symbol().ok() == Some(self.target) {
                self.push_span(*span);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analysis::{DocumentInput, Workspace, rename_at};

    fn apply_rename(code: &str, target_offset: u32, new_name: &str) -> String {
        let doc = DocumentInput {
            id: "rename_test.tlk".to_string(),
            path: "rename_test.tlk".to_string(),
            version: 0,
            text: code.into(),
        };
        let workspace = Workspace::new(vec![doc]).expect("workspace");
        let edit = rename_at(
            &workspace,
            &"rename_test.tlk".to_string(),
            target_offset,
            new_name,
        )
        .expect("workspace edit");
        let mut text = code.to_string();
        let mut edits = edit.documents[0].edits.clone();
        edits.sort_by_key(|edit| std::cmp::Reverse(edit.range.start));
        for edit in edits {
            text.replace_range(
                edit.range.start as usize..edit.range.end as usize,
                &edit.replacement,
            );
        }
        text
    }

    // ADR 0042: a rename never manufactures a collision — refuse when
    // the new name is already bound in a scope binding the renamed
    // symbol.
    #[test]
    fn rename_refuses_to_create_a_collision() {
        let code = "let first = 1\nlet second = 2\nfirst + second\n";
        let doc = DocumentInput {
            id: "rename_collision.tlk".to_string(),
            path: "rename_collision.tlk".to_string(),
            version: 0,
            text: code.into(),
        };
        let workspace = Workspace::new(vec![doc]).expect("workspace");
        let offset = code.rfind("first").expect("target") as u32;
        assert!(
            rename_at(
                &workspace,
                &"rename_collision.tlk".to_string(),
                offset,
                "second",
            )
            .is_none(),
            "rename onto an existing binding must refuse"
        );
        assert!(
            rename_at(
                &workspace,
                &"rename_collision.tlk".to_string(),
                offset,
                "renamed",
            )
            .is_some(),
            "an unclaimed name still renames"
        );
    }

    #[test]
    fn parameter_rename_expands_same_name_label_to_preserve_the_api() {
        // ADR 0041: renaming the local binder must not change id(value:).
        let code = "func id(value: Int) -> Int {\n\tvalue\n}\nid(value: 1)\n";
        let body_use = code.rfind("value\n").expect("body reference") as u32;
        assert_eq!(
            apply_rename(code, body_use, "item"),
            "func id(value item: Int) -> Int {\n\titem\n}\nid(value: 1)\n"
        );
    }

    #[test]
    fn bare_parameter_rename_stays_positional() {
        let code = "func id(value) {\n\tvalue\n}\nid(1)\n";
        let body_use = code.rfind("value\n").expect("body reference") as u32;
        assert_eq!(
            apply_rename(code, body_use, "item"),
            "func id(item) {\n\titem\n}\nid(1)\n"
        );
    }

    #[test]
    fn two_name_parameter_rename_keeps_the_label() {
        let code = "func split(foo fizz: Int) -> Int {\n\tfizz\n}\nsplit(foo: 1)\n";
        let body_use = code.rfind("fizz\n").expect("body reference") as u32;
        assert_eq!(
            apply_rename(code, body_use, "buzz"),
            "func split(foo buzz: Int) -> Int {\n\tbuzz\n}\nsplit(foo: 1)\n"
        );
    }

    #[test]
    fn closure_parameter_rename_stays_same_name() {
        // Anonymous closure parameters are local binders only; no label
        // expansion applies.
        let code = "let f = func(value: Int) -> Int {\n\tvalue\n}\nf(1)\n";
        let body_use = code.rfind("value\n").expect("body reference") as u32;
        assert_eq!(
            apply_rename(code, body_use, "item"),
            "let f = func(item: Int) -> Int {\n\titem\n}\nf(1)\n"
        );
    }

    #[test]
    fn rename_a_struct_from_a_type_annotation() {
        let code = "struct Box {\n\tlet value: Int\n}\nfunc f(b: Box) -> Box {\n\tb\n}\nf(b: Box(value: 1))\n";
        let annotation = code.find("Box) ->").expect("annotation") as u32;
        assert_eq!(
            apply_rename(code, annotation, "Crate"),
            "struct Crate {\n\tlet value: Int\n}\nfunc f(b: Crate) -> Crate {\n\tb\n}\nf(b: Crate(value: 1))\n"
        );
    }

    #[test]
    fn rename_an_associated_type_from_a_nominal_path_member() {
        let code = "protocol Producer {\n\tassociated Element\n\tfunc get() -> Element\n}\nfunc first<T: Producer>(x: T) -> T.Element {\n\tx.get()\n}\n";
        let member = code.rfind("Element").expect("nominal path member") as u32;
        assert_eq!(
            apply_rename(code, member, "Item"),
            "protocol Producer {\n\tassociated Item\n\tfunc get() -> Item\n}\nfunc first<T: Producer>(x: T) -> T.Item {\n\tx.get()\n}\n"
        );
    }

    #[test]
    fn rename_an_associated_type_from_an_any_binding() {
        let code = "protocol Producer {\n\tassociated Element\n\tfunc get() -> Element\n}\nstruct IntProducer {\n\tlet value: Int\n}\nextend IntProducer: Producer {\n\tfunc get() -> Int {\n\t\tself.value\n\t}\n}\nfunc make() -> any Producer<Element = Int> {\n\tIntProducer(value: 1)\n}\n";
        let binding = code.rfind("Element").expect("assoc binding") as u32;
        assert_eq!(
            apply_rename(code, binding, "Item"),
            "protocol Producer {\n\tassociated Item\n\tfunc get() -> Item\n}\nstruct IntProducer {\n\tlet value: Int\n}\nextend IntProducer: Producer {\n\tfunc get() -> Int {\n\t\tself.value\n\t}\n}\nfunc make() -> any Producer<Item = Int> {\n\tIntProducer(value: 1)\n}\n"
        );
    }

    #[test]
    fn rename_an_effect_from_a_handler() {
        let code = "effect 'bail(error) -> Never\nfunc build() 'bail -> Int {\n\t'bail(\"stop\")\n}\n#handle 'bail { err in\n\t0\n}\nbuild()\n";
        let handler = code.find("'bail {").expect("handler") as u32;
        assert_eq!(
            apply_rename(code, handler, "halt"),
            "effect 'halt(error) -> Never\nfunc build() 'halt -> Int {\n\t'halt(\"stop\")\n}\n#handle 'halt { err in\n\t0\n}\nbuild()\n"
        );
    }

    #[test]
    fn rename_an_imported_symbol_edits_both_documents() {
        let main = "use package::other::{ answer }\nprint(answer)\n";
        let other = "pub let answer = 42\n";
        let docs = vec![
            DocumentInput {
                id: "src/main.tlk".to_string(),
                path: "src/main.tlk".to_string(),
                version: 0,
                text: main.into(),
            },
            DocumentInput {
                id: "src/other.tlk".to_string(),
                path: "src/other.tlk".to_string(),
                version: 0,
                text: other.into(),
            },
        ];
        let workspace = Workspace::new(docs).expect("workspace");
        let offset = main.find("answer }").expect("import entry") as u32;
        let edit = rename_at(&workspace, &"src/main.tlk".to_string(), offset, "meaning")
            .expect("workspace edit");

        let mut main_edits = Vec::new();
        let mut other_edits = Vec::new();
        for document in &edit.documents {
            match document.document_id.as_str() {
                "src/main.tlk" => main_edits = document.edits.clone(),
                "src/other.tlk" => other_edits = document.edits.clone(),
                other => panic!("unexpected document {other}"),
            }
        }
        // The import entry and the use site in main, the export in other.
        assert_eq!(main_edits.len(), 2, "{main_edits:?}");
        assert_eq!(other_edits.len(), 1, "{other_edits:?}");
        let export = &other_edits[0];
        assert_eq!(
            &other[export.range.start as usize..export.range.end as usize],
            "answer"
        );
    }
}
