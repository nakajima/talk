use crate::name_resolution::{name_resolver::Scope, symbol::Symbol};

/// Public compiler-provided types that require synthetic Core documentation.
pub const PUBLIC_BUILTIN_TYPES: &[(&str, Symbol)] = &[
    ("Int", Symbol::Int),
    ("Float", Symbol::Float),
    ("Bool", Symbol::Bool),
    ("Void", Symbol::Void),
    ("Never", Symbol::Never),
    ("RawPtr", Symbol::RawPtr),
    ("Byte", Symbol::Byte),
];

pub fn import_builtins(scope: &mut Scope) {
    for &(name, symbol) in PUBLIC_BUILTIN_TYPES {
        scope.types.insert(name.into(), symbol);
    }
    scope.types.insert("__IR".into(), Symbol::IR);
    scope.values.insert("unsafe".into(), Symbol::Unsafe);
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::PUBLIC_BUILTIN_TYPES;

    #[test]
    fn every_public_builtin_has_exactly_one_documentation_stub() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../core/builtins");
        let mut documented = std::fs::read_dir(root)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "md"))
            .map(|path| path.file_stem().unwrap().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        documented.sort();

        let mut registered = PUBLIC_BUILTIN_TYPES
            .iter()
            .map(|(name, _)| (*name).to_string())
            .collect::<Vec<_>>();
        registered.sort();

        assert_eq!(documented, registered);
    }
}
