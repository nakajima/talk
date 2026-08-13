//! Frontend vocabulary (ADR 0057 slice 3): module identity, source
//! handles, and macro artifacts — the data types the parser, resolver,
//! and checker share with the rest of the compiler. Everything here
//! closes over frontend types only; the driver and backends re-export
//! these under their historical paths and add behavior around them.

pub mod macro_artifact;
pub mod macro_host;
pub mod module;
pub mod module_path;
pub mod source;
