pub mod completion;
pub mod document;
pub mod semantic_tokens;

#[cfg(feature = "cli")]
pub mod goto_definition;
#[cfg(feature = "cli")]
pub mod rename;
#[cfg(feature = "cli")]
pub mod server;
