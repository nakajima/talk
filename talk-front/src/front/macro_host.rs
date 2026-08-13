//! The toolchain seam macro expansion works through (ADR 0057
//! slice 3b). Expansion is frontend logic, but three of its inputs come
//! from the built toolchain: token-kind tags from the self-hosted
//! frontend's ABI, re-parses of expansion output through the self-hosted
//! parser, and compiled procedural-macro execution (the VM). The
//! frontend cannot depend on any of that, so expansion consumes this
//! trait; the root crate implements it over `compiling::frontend`,
//! `compiling::bridge`, and `procedural_macros`.
//!
//! The bridged result types live here because they are frontend data —
//! parse trees, node metadata, spans — that the bridge merely constructs.

use crate::node::Node;
use crate::node_id::FileID;
use crate::node_kinds::expr::MacroToken;
use crate::parsing::ast::{AST, Parsed};
use crate::parsing::hygiene::SyntaxMetadata;
use crate::parsing::node_meta_storage::NodeMetaStorage;
use crate::span::Span;
use crate::token_kind::TokenKind;

/// A structured frontend failure: code, message, and (when the reporter
/// had one) the source span and expected token.
#[derive(Debug, Clone)]
pub struct BridgedFail {
    pub code: String,
    pub message: String,
    pub span: Option<Span>,
    pub expected: Option<TokenKind>,
}

/// A decoded parse result from the self-hosted frontend.
pub struct BridgedParse {
    pub roots: Vec<Node>,
    pub meta: NodeMetaStorage,
    pub comments: Vec<(u32, u32)>,
    pub failure: Option<BridgedFail>,
    pub diags: Vec<BridgedFail>,
    /// The highest node id minted; consumers continue their own
    /// minting (desugaring, typing) above it.
    pub next_node_id: u32,
}

/// A decoded procedural-macro expansion: the generated source, its
/// parse, the hygiene metadata to apply, and any structured failure.
pub struct BridgedExprMacro {
    pub source: String,
    pub parse: Option<BridgedParse>,
    pub metadata: SyntaxMetadata,
    pub failure: Option<BridgedFail>,
}

/// What macro expansion may ask of the toolchain.
pub trait MacroHost {
    /// The ABI tag of a `TokenKind` variant (declarative token
    /// templates classify their operands by it).
    fn token_kind_tag(&self, variant: &str) -> Result<u32, String>;
    /// Parse one grammar category's source text through the self-hosted
    /// frontend (`export` names the parser entry point).
    fn parse_category(
        &self,
        export: &str,
        source: &str,
        file: FileID,
    ) -> Result<BridgedParse, String>;
    /// The procedural macros visible to one file (imports scope the set).
    fn bindings_for<'host>(&'host self, ast: &AST<Parsed>) -> Box<dyn MacroBindings + 'host>;
}

/// One file's procedural-macro table.
pub trait MacroBindings {
    fn resolve(&self, name: &str) -> MacroResolution<'_>;
}

/// How a procedural-macro name resolved.
pub enum MacroResolution<'bindings> {
    Found(&'bindings dyn ProceduralMacro),
    /// The name is exported by more than one package.
    Ambiguous(Vec<String>),
    Missing,
}

/// One resolved procedural macro, ready to execute.
pub trait ProceduralMacro {
    #[allow(clippy::too_many_arguments)]
    fn expand(
        &self,
        source_id: FileID,
        source: &str,
        input_start: u32,
        input_end: u32,
        input_tokens: &[MacroToken],
        expansion_namespace: u64,
        expansion_ordinal: u64,
    ) -> Result<BridgedExprMacro, String>;
}

/// The macro-free table: every lookup misses. The host for compiles
/// with no procedural-macro environment.
pub struct NoProceduralMacros;

impl MacroBindings for NoProceduralMacros {
    fn resolve(&self, _name: &str) -> MacroResolution<'_> {
        MacroResolution::Missing
    }
}
