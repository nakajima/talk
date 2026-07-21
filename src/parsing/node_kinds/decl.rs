use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name::Name,
    node_id::NodeID,
    node_kinds::{
        block::Block, body::Body, expr::Expr, func::Func, func_signature::FuncSignature,
        generic_decl::GenericDecl, parameter::Parameter, pattern::Pattern,
        type_annotation::TypeAnnotation, type_application::TypeApplication,
        where_clause::WhereClause,
    },
    parsing::span::Span,
};

/// Visibility of a declaration - defaults to private (internal to file)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Drive, DriveMut)]
pub enum Visibility {
    #[default]
    Private,
    Public,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Drive, DriveMut)]
pub enum ReceiverMode {
    #[default]
    None,
    Ref,
    Consuming,
}

/// Path in an import statement
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum ImportPath {
    /// Local source module path rooted at package, self, or super.
    Local(#[drive(skip)] String),
    /// External package name like collections or http.
    Package(#[drive(skip)] String),
}

/// A single symbol being imported, with optional alias
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct ImportedSymbol {
    #[drive(skip)]
    pub name: String,
    #[drive(skip)]
    pub alias: Option<String>,
    #[drive(skip)]
    pub span: Span,
}

/// What symbols to import
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum ImportedSymbols {
    /// Named imports: { a, b, c }
    Named(Vec<ImportedSymbol>),
    /// Import all public symbols.
    All,
}

/// Full import statement
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Import {
    pub symbols: ImportedSymbols,
    pub path: ImportPath,
    #[drive(skip)]
    pub path_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum DeclKind {
    Import(Import),
    /// A module-local declarative expression macro rule (ADR 0026's first
    /// implementation slice). Expansion removes these before name resolution.
    Macro {
        #[drive(skip)]
        name: String,
        #[drive(skip)]
        name_span: Span,
        #[drive(skip)]
        params: Vec<MacroParameter>,
        template: Expr,
    },
    Effect {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>,
        where_clause: Option<WhereClause>,
        params: Vec<Parameter>,
        ret: TypeAnnotation,
    },
    Struct {
        #[drive(skip)]
        name: Name, /* name */
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>, /* generics */
        where_clause: Option<WhereClause>,
        body: Body, /* body */
        /// Declared `'linear`: values must be consumed exactly once.
        #[drive(skip)]
        linear: bool,
        /// Declared `'heap`: reference semantics, region-allocated.
        #[drive(skip)]
        heap: bool,
    },

    Let {
        lhs: Pattern,
        type_annotation: Option<TypeAnnotation>,
        rhs: Option<Expr>,
    },

    Protocol {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>,
        where_clause: Option<WhereClause>,
        body: Body,
        conformances: Vec<TypeAnnotation>,
    },

    Init {
        #[drive(skip)]
        name: Name,
        params: Vec<Parameter>, /* params tuple */
        body: Block,
    },

    Property {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        #[drive(skip)]
        is_static: bool,
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<Expr>,
    },

    Method {
        func: Box<Func>,
        #[drive(skip)]
        is_static: bool,
        #[drive(skip)]
        receiver_mode: ReceiverMode,
    },

    Associated {
        generic: GenericDecl,
        where_clause: Option<WhereClause>,
    },

    // Function stuff
    Func(Func),

    Extend {
        /// Explicit instance binders from `extend<T> Head<T> ...`.
        binders: Vec<GenericDecl>,
        /// The extended nominal or protocol application. The head grammar
        /// admits only a name plus arguments; arguments never declare
        /// parameters.
        head: TypeApplication,
        conformances: Vec<TypeAnnotation>,
        where_clause: Option<WhereClause>,
        body: Body,
    },

    // Enum declaration
    Enum {
        #[drive(skip)]
        name: Name, // TypeRepr name: Option
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>, // Generics TypeParams <T>
        where_clause: Option<WhereClause>,
        body: Body,
        /// Declared `linear`: values must be consumed exactly once.
        #[drive(skip)]
        linear: bool,
    },

    // Individual enum variant in declaration
    EnumVariant {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        generics: Vec<GenericDecl>,
        /// Payload types stay positional. A label, when present, is metadata
        /// for constructing and matching that payload slot.
        payloads: Vec<TypeAnnotation>,
        #[drive(skip)]
        payload_labels: Vec<Option<Name>>,
        result: Option<TypeAnnotation>,
    },

    FuncSignature(FuncSignature),
    MethodRequirement {
        signature: FuncSignature,
        #[drive(skip)]
        receiver_mode: ReceiverMode,
    },
    /// A protocol initializer requirement: `init(params)`, bodyless.
    /// Desugar stamps the implicit `-> Self` return; no `self` receiver
    /// is prepended.
    InitRequirement {
        signature: FuncSignature,
    },

    TypeAlias(#[drive(skip)] Name, #[drive(skip)] Span, TypeAnnotation),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroParameter {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Decl {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: DeclKind,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub visibility: Visibility,
}

impl_into_node!(Decl);
