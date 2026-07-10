use std::{
    collections::HashSet,
    fmt::{Display, Formatter},
    fs, io,
    path::{Component, Path, PathBuf},
    process::{Command, Output},
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sha2::{Digest, Sha256};

use crate::{
    label::Label,
    lexer::Lexer,
    lexing::unescape,
    name::Name,
    node::Node,
    node_id::FileID,
    node_kinds::{
        call_arg::CallArg,
        expr::{Expr, ExprKind},
        stmt::StmtKind,
    },
    parser::Parser,
};

use super::{
    core::LibraryTyped,
    driver::{CompilationMode, Driver, DriverConfig, Lowered, Source},
    module::{Module, ModuleEnvironment, ModuleId},
};

const MANIFEST_FILE: &str = "package.tlk";
const LOCK_FILE: &str = "package.lock";
const LOCK_FORMAT: u64 = 1;
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug)]
pub enum PackageError {
    Io {
        context: String,
        source: io::Error,
    },
    Manifest {
        path: PathBuf,
        message: String,
    },
    Lock {
        path: PathBuf,
        message: String,
    },
    Command {
        program: String,
        arguments: Vec<String>,
        status: Option<i32>,
        stderr: String,
    },
    Cache(String),
    Resolution(String),
    Compile(String),
}

impl Display for PackageError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io { context, source } => write!(f, "{context}: {source}"),
            Self::Manifest { path, message } => {
                write!(f, "invalid package manifest {}: {message}", path.display())
            }
            Self::Lock { path, message } => {
                write!(f, "invalid package lockfile {}: {message}", path.display())
            }
            Self::Command {
                program,
                arguments,
                status,
                stderr,
            } => {
                write!(
                    f,
                    "{program} {} failed{}: {}",
                    arguments.join(" "),
                    status
                        .map(|code| format!(" with status {code}"))
                        .unwrap_or_default(),
                    stderr.trim()
                )
            }
            Self::Cache(message) | Self::Resolution(message) | Self::Compile(message) => {
                f.write_str(message)
            }
        }
    }
}

impl std::error::Error for PackageError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackageArtifact {
    Library { from: String },
    Binary { name: String, from: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackageSource {
    Git { url: String, rev: String },
    Tar { url: String, sha256: String },
    Path { path: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageDependency {
    pub package: String,
    pub source: PackageSource,
}

#[derive(Clone, Debug)]
pub struct PackageManifest {
    pub name: String,
    pub version: String,
    pub builds: Vec<PackageArtifact>,
    pub dependencies: Vec<PackageDependency>,
}

impl PackageManifest {
    pub fn read(root: &Path) -> Result<Self, PackageError> {
        let path = root.join(MANIFEST_FILE);
        let source = fs::read_to_string(&path).map_err(|source| PackageError::Io {
            context: format!("failed to read {}", path.display()),
            source,
        })?;
        Self::parse(&path, &source)
    }

    fn parse(path: &Path, source: &str) -> Result<Self, PackageError> {
        let parser = Parser::new(path.to_string_lossy(), FileID(0), Lexer::new(source));
        let (ast, diagnostics) = parser.parse().map_err(|error| PackageError::Manifest {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
        if !diagnostics.is_empty() {
            return Err(PackageError::Manifest {
                path: path.to_path_buf(),
                message: format!("{diagnostics:?}"),
            });
        }
        let [Node::Stmt(statement)] = ast.roots.as_slice() else {
            return Err(PackageError::Manifest {
                path: path.to_path_buf(),
                message: "the manifest must contain exactly one Package(...) expression".into(),
            });
        };
        let StmtKind::Expr(expression) = &statement.kind else {
            return Err(PackageError::Manifest {
                path: path.to_path_buf(),
                message: "the manifest must contain exactly one Package(...) expression".into(),
            });
        };
        let args = Self::call_args(path, expression, "Package")?;
        Self::only_fields(path, args, &["name", "version", "builds", "dependencies"])?;

        let name = Self::string_field(path, args, "name")?;
        if name.is_empty() {
            return Err(Self::manifest_error(path, "name must not be empty"));
        }
        let import_name = normalized_import_name(&name);
        if is_compiler_module_name(&import_name) {
            return Err(Self::manifest_error(
                path,
                format!("package import name {import_name:?} is reserved by Talk"),
            ));
        }
        let version = Self::string_field(path, args, "version")?;
        let builds = Self::array_field(path, args, "builds")?
            .iter()
            .map(|value| Self::artifact(path, value))
            .collect::<Result<Vec<_>, _>>()?;
        let libraries = builds
            .iter()
            .filter(|artifact| matches!(artifact, PackageArtifact::Library { .. }))
            .count();
        if libraries > 1 {
            return Err(Self::manifest_error(
                path,
                "a package may declare only one library",
            ));
        }
        let mut binary_names = HashSet::new();
        for artifact in &builds {
            if let PackageArtifact::Binary { name, .. } = artifact
                && !binary_names.insert(name)
            {
                return Err(Self::manifest_error(
                    path,
                    format!("binary target {name:?} is declared more than once"),
                ));
            }
        }

        let dependencies = Self::array_field(path, args, "dependencies")?
            .iter()
            .map(|value| Self::dependency(path, value))
            .collect::<Result<Vec<_>, _>>()?;
        let mut dependency_names = HashSet::new();
        let mut import_names = HashSet::new();
        for dependency in &dependencies {
            if !dependency_names.insert(&dependency.package) {
                return Err(Self::manifest_error(
                    path,
                    format!(
                        "dependency {:?} is declared more than once",
                        dependency.package
                    ),
                ));
            }
            let import_name = normalized_import_name(&dependency.package);
            if is_compiler_module_name(&import_name) {
                return Err(Self::manifest_error(
                    path,
                    format!("dependency import name {import_name:?} is reserved by Talk"),
                ));
            }
            if !import_names.insert(import_name.clone()) {
                return Err(Self::manifest_error(
                    path,
                    format!("dependencies normalize to the same Talk import name {import_name:?}"),
                ));
            }
        }

        Ok(Self {
            name,
            version,
            builds,
            dependencies,
        })
    }

    pub fn import_name(&self) -> String {
        normalized_import_name(&self.name)
    }

    pub fn library(&self) -> Option<&str> {
        self.builds.iter().find_map(|artifact| match artifact {
            PackageArtifact::Library { from } => Some(from.as_str()),
            PackageArtifact::Binary { .. } => None,
        })
    }

    pub fn binary(&self, requested: Option<&str>) -> Result<&PackageArtifact, PackageError> {
        let binaries = self
            .builds
            .iter()
            .filter(|artifact| matches!(artifact, PackageArtifact::Binary { .. }))
            .collect::<Vec<_>>();
        match requested {
            Some(name) => binaries
                .into_iter()
                .find(|artifact| {
                    matches!(artifact, PackageArtifact::Binary { name: candidate, .. } if candidate == name)
                })
                .ok_or_else(|| PackageError::Resolution(format!("package has no binary named {name:?}"))),
            None if binaries.len() == 1 => Ok(binaries[0]),
            None if binaries.is_empty() => Err(PackageError::Resolution(
                "package has no binary targets".into(),
            )),
            None => Err(PackageError::Resolution(
                "package has multiple binary targets; pass --bin <name>".into(),
            )),
        }
    }

    pub fn source_path(&self, root: &Path, source: &str) -> Result<PathBuf, PackageError> {
        let source_root = root
            .join("src")
            .canonicalize()
            .map_err(|source| PackageError::Io {
                context: format!(
                    "failed to find package source directory under {}",
                    root.display()
                ),
                source,
            })?;
        let candidate = root
            .join(source)
            .canonicalize()
            .map_err(|source| PackageError::Io {
                context: format!("failed to find package target {source:?}"),
                source,
            })?;
        if !candidate.starts_with(&source_root) {
            return Err(PackageError::Manifest {
                path: root.join(MANIFEST_FILE),
                message: format!("target {source:?} must be under src/"),
            });
        }
        if !candidate.is_file() {
            return Err(PackageError::Manifest {
                path: root.join(MANIFEST_FILE),
                message: format!("target {source:?} is not a file"),
            });
        }
        Ok(candidate)
    }

    pub fn dependency_fingerprint(&self) -> String {
        let mut hasher = Sha256::new();
        for dependency in &self.dependencies {
            hasher.update(dependency.package.as_bytes());
            hasher.update([0]);
            match &dependency.source {
                PackageSource::Git { url, rev } => {
                    hasher.update(b"git\0");
                    hasher.update(url.as_bytes());
                    hasher.update([0]);
                    hasher.update(rev.as_bytes());
                }
                PackageSource::Tar { url, sha256 } => {
                    hasher.update(b"tar\0");
                    hasher.update(url.as_bytes());
                    hasher.update([0]);
                    hasher.update(sha256.as_bytes());
                }
                PackageSource::Path { path } => {
                    hasher.update(b"path\0");
                    hasher.update(path.as_bytes());
                }
            }
            hasher.update([0]);
        }
        hex_digest(hasher.finalize())
    }

    fn artifact(path: &Path, expression: &Expr) -> Result<PackageArtifact, PackageError> {
        let (name, args) = Self::member_call(path, expression)?;
        match name {
            "lib" => {
                Self::only_fields(path, args, &["from"])?;
                Ok(PackageArtifact::Library {
                    from: Self::string_field(path, args, "from")?,
                })
            }
            "bin" => {
                Self::only_fields(path, args, &["named", "from"])?;
                Ok(PackageArtifact::Binary {
                    name: Self::string_field(path, args, "named")?,
                    from: Self::string_field(path, args, "from")?,
                })
            }
            other => Err(Self::manifest_error(
                path,
                format!("unknown package build target .{other}"),
            )),
        }
    }

    fn dependency(path: &Path, expression: &Expr) -> Result<PackageDependency, PackageError> {
        let (name, args) = Self::member_call(path, expression)?;
        match name {
            "git" => {
                Self::only_fields(path, args, &["package", "url", "rev"])?;
                Ok(PackageDependency {
                    package: Self::string_field(path, args, "package")?,
                    source: PackageSource::Git {
                        url: Self::string_field(path, args, "url")?,
                        rev: Self::string_field(path, args, "rev")?,
                    },
                })
            }
            "tar" => {
                Self::only_fields(path, args, &["package", "url", "sha256"])?;
                let sha256 = Self::string_field(path, args, "sha256")?;
                if !is_sha256(&sha256) {
                    return Err(Self::manifest_error(
                        path,
                        "tar sha256 must be a 64-character hexadecimal digest",
                    ));
                }
                Ok(PackageDependency {
                    package: Self::string_field(path, args, "package")?,
                    source: PackageSource::Tar {
                        url: Self::string_field(path, args, "url")?,
                        sha256: sha256.to_ascii_lowercase(),
                    },
                })
            }
            "path" => {
                Self::only_fields(path, args, &["package", "path"])?;
                let local_path = Self::string_field(path, args, "path")?;
                if Path::new(&local_path).is_absolute() {
                    return Err(Self::manifest_error(
                        path,
                        "path dependencies must use a path relative to package.tlk",
                    ));
                }
                Ok(PackageDependency {
                    package: Self::string_field(path, args, "package")?,
                    source: PackageSource::Path { path: local_path },
                })
            }
            other => Err(Self::manifest_error(
                path,
                format!("unknown package dependency source .{other}"),
            )),
        }
    }

    fn call_args<'a>(
        path: &Path,
        expression: &'a Expr,
        expected: &str,
    ) -> Result<&'a [CallArg], PackageError> {
        let ExprKind::Call {
            callee,
            args,
            type_args,
            trailing_block,
        } = &expression.kind
        else {
            return Err(Self::manifest_error(
                path,
                format!("expected {expected}(...)"),
            ));
        };
        if !type_args.is_empty()
            || trailing_block.is_some()
            || Self::variable_name(callee) != Some(expected)
        {
            return Err(Self::manifest_error(
                path,
                format!("expected {expected}(...)"),
            ));
        }
        Ok(args)
    }

    fn member_call<'a>(
        path: &Path,
        expression: &'a Expr,
    ) -> Result<(&'a str, &'a [CallArg]), PackageError> {
        let ExprKind::Call {
            callee,
            args,
            type_args,
            trailing_block,
        } = &expression.kind
        else {
            return Err(Self::manifest_error(
                path,
                "expected a .git(...), .tar(...), .path(...), .lib(...), or .bin(...) form",
            ));
        };
        let ExprKind::Member(None, Label::Named(name), _) = &callee.kind else {
            return Err(Self::manifest_error(
                path,
                "expected a package manifest member form",
            ));
        };
        if !type_args.is_empty() || trailing_block.is_some() {
            return Err(Self::manifest_error(
                path,
                "package manifest calls cannot have type arguments or blocks",
            ));
        }
        Ok((name, args))
    }

    fn variable_name(expression: &Expr) -> Option<&str> {
        let ExprKind::Variable(Name::Raw(name)) = &expression.kind else {
            return None;
        };
        Some(name)
    }

    fn only_fields(path: &Path, args: &[CallArg], allowed: &[&str]) -> Result<(), PackageError> {
        let mut seen = HashSet::new();
        for arg in args {
            let Label::Named(name) = &arg.label else {
                return Err(Self::manifest_error(
                    path,
                    "package manifest arguments must be labeled",
                ));
            };
            if !allowed.contains(&name.as_str()) {
                return Err(Self::manifest_error(
                    path,
                    format!("unknown field {name:?}"),
                ));
            }
            if !seen.insert(name) {
                return Err(Self::manifest_error(
                    path,
                    format!("field {name:?} appears more than once"),
                ));
            }
        }
        Ok(())
    }

    fn field<'a>(path: &Path, args: &'a [CallArg], field: &str) -> Result<&'a Expr, PackageError> {
        args.iter()
            .find_map(|arg| match &arg.label {
                Label::Named(name) if name == field => Some(&arg.value),
                _ => None,
            })
            .ok_or_else(|| Self::manifest_error(path, format!("missing required field {field:?}")))
    }

    fn string_field(path: &Path, args: &[CallArg], field: &str) -> Result<String, PackageError> {
        Self::string(path, Self::field(path, args, field)?)
    }

    fn array_field<'a>(
        path: &Path,
        args: &'a [CallArg],
        field: &str,
    ) -> Result<&'a [Expr], PackageError> {
        let ExprKind::LiteralArray(values) = &Self::field(path, args, field)?.kind else {
            return Err(Self::manifest_error(
                path,
                format!("field {field:?} must be an array"),
            ));
        };
        Ok(values)
    }

    fn string(path: &Path, expression: &Expr) -> Result<String, PackageError> {
        let ExprKind::LiteralString(value) = &expression.kind else {
            return Err(Self::manifest_error(path, "expected a string literal"));
        };
        unescape(value).map_err(|error| Self::manifest_error(path, error.message()))
    }

    fn manifest_error(path: &Path, message: impl Into<String>) -> PackageError {
        PackageError::Manifest {
            path: path.to_path_buf(),
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LockedSource {
    Git {
        url: String,
        requested_rev: String,
        commit: String,
    },
    Tar {
        url: String,
        sha256: String,
    },
    Path {
        path: String,
        base: PathBase,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum PathBase {
    Root,
    Package(String),
}

impl LockedSource {
    fn id(&self) -> String {
        let mut hasher = Sha256::new();
        match self {
            Self::Git { url, commit, .. } => {
                hasher.update(b"git\0");
                hasher.update(url.as_bytes());
                hasher.update([0]);
                hasher.update(commit.as_bytes());
            }
            Self::Tar { url, sha256 } => {
                hasher.update(b"tar\0");
                hasher.update(url.as_bytes());
                hasher.update([0]);
                hasher.update(sha256.as_bytes());
            }
            Self::Path { path, base } => {
                hasher.update(b"path\0");
                match base {
                    PathBase::Root => hasher.update(b"root"),
                    PathBase::Package(package) => hasher.update(package.as_bytes()),
                }
                hasher.update([0]);
                hasher.update(path.as_bytes());
            }
        }
        hex_digest(hasher.finalize())
    }
}

#[derive(Clone, Debug)]
struct LockedPackage {
    id: String,
    name: String,
    version: String,
    source: LockedSource,
    dependencies: Vec<String>,
}

#[derive(Clone, Debug)]
struct PackageLock {
    fingerprint: String,
    root_dependencies: Vec<String>,
    packages: Vec<LockedPackage>,
}

impl PackageLock {
    fn read(path: &Path) -> Result<Self, PackageError> {
        let source = fs::read_to_string(path).map_err(|source| PackageError::Io {
            context: format!("failed to read {}", path.display()),
            source,
        })?;
        let parser = Parser::new(path.to_string_lossy(), FileID(0), Lexer::new(&source));
        let (ast, diagnostics) = parser.parse().map_err(|error| PackageError::Lock {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
        if !diagnostics.is_empty() {
            return Err(PackageError::Lock {
                path: path.to_path_buf(),
                message: format!("{diagnostics:?}"),
            });
        }
        let [Node::Stmt(statement)] = ast.roots.as_slice() else {
            return Err(Self::error(
                path,
                "the lockfile must contain exactly one Lock(...) expression",
            ));
        };
        let StmtKind::Expr(expression) = &statement.kind else {
            return Err(Self::error(
                path,
                "the lockfile must contain exactly one Lock(...) expression",
            ));
        };
        let args = PackageManifest::call_args(path, expression, "Lock")
            .map_err(|error| Self::from_manifest_error(path, error))?;
        PackageManifest::only_fields(
            path,
            args,
            &["format", "fingerprint", "root_dependencies", "packages"],
        )
        .map_err(|error| Self::from_manifest_error(path, error))?;
        let ExprKind::LiteralInt(format) = &PackageManifest::field(path, args, "format")
            .map_err(|error| Self::from_manifest_error(path, error))?
            .kind
        else {
            return Err(Self::error(path, "lockfile format must be an integer"));
        };
        let format = format
            .parse::<u64>()
            .map_err(|_| Self::error(path, "lockfile format must be an integer"))?;
        if format != LOCK_FORMAT {
            return Err(Self::error(
                path,
                format!("unsupported lockfile format {format}"),
            ));
        }
        let fingerprint = PackageManifest::string_field(path, args, "fingerprint")
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let root_dependencies = Self::string_array(path, args, "root_dependencies")?;
        let package_values = PackageManifest::array_field(path, args, "packages")
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let packages = package_values
            .iter()
            .map(|value| Self::locked_package(path, value))
            .collect::<Result<Vec<_>, _>>()?;
        let lock = Self {
            fingerprint,
            root_dependencies,
            packages,
        };
        lock.validate(path)?;
        Ok(lock)
    }

    fn write(&self, path: &Path) -> Result<(), PackageError> {
        let temporary = path.with_file_name(format!(
            ".{}-{}.{}.tmp",
            LOCK_FILE,
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::write(&temporary, self.render()).map_err(|source| PackageError::Io {
            context: format!("failed to write {}", temporary.display()),
            source,
        })?;
        fs::rename(&temporary, path).map_err(|source| PackageError::Io {
            context: format!("failed to replace {}", path.display()),
            source,
        })
    }

    fn validate(&self, path: &Path) -> Result<(), PackageError> {
        let ids = self
            .packages
            .iter()
            .map(|package| package.id.as_str())
            .collect::<HashSet<_>>();
        if ids.len() != self.packages.len() {
            return Err(Self::error(path, "a package appears more than once"));
        }
        for root_dependency in &self.root_dependencies {
            if !ids.contains(root_dependency.as_str()) {
                return Err(Self::error(
                    path,
                    "root dependency does not exist in package list",
                ));
            }
        }
        for package in &self.packages {
            if package.id != package.source.id() {
                return Err(Self::error(
                    path,
                    format!("package {} has an invalid source id", package.name),
                ));
            }
            if let LockedSource::Path {
                base: PathBase::Package(base),
                ..
            } = &package.source
                && !ids.contains(base.as_str())
            {
                return Err(Self::error(
                    path,
                    format!("path package {} has a missing base package", package.name),
                ));
            }
            for dependency in &package.dependencies {
                if !ids.contains(dependency.as_str()) {
                    return Err(Self::error(
                        path,
                        format!("package {} references a missing dependency", package.name),
                    ));
                }
            }
        }
        Ok(())
    }

    fn matches(&self, manifest: &PackageManifest) -> bool {
        self.fingerprint == manifest.dependency_fingerprint()
    }

    fn prune(&mut self) {
        let packages = self
            .packages
            .iter()
            .map(|package| (package.id.as_str(), &package.dependencies))
            .collect::<FxHashMap<_, _>>();
        let mut reachable = FxHashSet::default();
        let mut pending = self.root_dependencies.clone();
        while let Some(id) = pending.pop() {
            if !reachable.insert(id.clone()) {
                continue;
            }
            if let Some(dependencies) = packages.get(id.as_str()) {
                pending.extend(dependencies.iter().cloned());
            }
        }
        self.packages
            .retain(|package| reachable.contains(&package.id));
    }

    fn package_roots(
        &self,
        root: &Path,
        store: &PackageStore,
    ) -> Result<FxHashMap<String, PathBuf>, PackageError> {
        let mut package_roots = FxHashMap::default();
        let mut resolving = FxHashSet::default();
        for package in &self.packages {
            self.package_root(&package.id, root, store, &mut package_roots, &mut resolving)?;
        }
        Ok(package_roots)
    }

    fn package_root(
        &self,
        id: &str,
        root: &Path,
        store: &PackageStore,
        package_roots: &mut FxHashMap<String, PathBuf>,
        resolving: &mut FxHashSet<String>,
    ) -> Result<PathBuf, PackageError> {
        if let Some(package_root) = package_roots.get(id) {
            return Ok(package_root.clone());
        }
        if !resolving.insert(id.to_string()) {
            return Err(PackageError::Resolution(format!(
                "path dependency bases form a cycle at {id}"
            )));
        }
        let package = self
            .packages
            .iter()
            .find(|package| package.id == id)
            .ok_or_else(|| PackageError::Resolution(format!("missing locked package {id}")))?;
        let path_base = match &package.source {
            LockedSource::Path {
                base: PathBase::Root,
                ..
            } => Some(root.to_path_buf()),
            LockedSource::Path {
                base: PathBase::Package(base),
                ..
            } => Some(self.package_root(base, root, store, package_roots, resolving)?),
            LockedSource::Git { .. } | LockedSource::Tar { .. } => None,
        };
        let package_root = store.materialize(&package.source, path_base.as_deref())?;
        resolving.remove(id);
        package_roots.insert(id.to_string(), package_root.clone());
        Ok(package_root)
    }

    fn locked_package(path: &Path, expression: &Expr) -> Result<LockedPackage, PackageError> {
        let (kind, args) = PackageManifest::member_call(path, expression)
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let (source, expected_fields) = match kind {
            "git" => (
                LockedSource::Git {
                    url: PackageManifest::string_field(path, args, "url")
                        .map_err(|error| Self::from_manifest_error(path, error))?,
                    requested_rev: PackageManifest::string_field(path, args, "requested_rev")
                        .map_err(|error| Self::from_manifest_error(path, error))?,
                    commit: PackageManifest::string_field(path, args, "commit")
                        .map_err(|error| Self::from_manifest_error(path, error))?,
                },
                &[
                    "id",
                    "package",
                    "version",
                    "url",
                    "requested_rev",
                    "commit",
                    "dependencies",
                ][..],
            ),
            "tar" => (
                LockedSource::Tar {
                    url: PackageManifest::string_field(path, args, "url")
                        .map_err(|error| Self::from_manifest_error(path, error))?,
                    sha256: PackageManifest::string_field(path, args, "sha256")
                        .map_err(|error| Self::from_manifest_error(path, error))?,
                },
                &["id", "package", "version", "url", "sha256", "dependencies"][..],
            ),
            "path" => {
                let path_value = PackageManifest::string_field(path, args, "path")
                    .map_err(|error| Self::from_manifest_error(path, error))?;
                if Path::new(&path_value).is_absolute() {
                    return Err(Self::error(
                        path,
                        "locked path dependencies must be relative",
                    ));
                }
                let base = PackageManifest::string_field(path, args, "base")
                    .map_err(|error| Self::from_manifest_error(path, error))?;
                let base = if base == "root" {
                    PathBase::Root
                } else {
                    PathBase::Package(base)
                };
                (
                    LockedSource::Path {
                        path: path_value,
                        base,
                    },
                    &["id", "package", "version", "path", "base", "dependencies"][..],
                )
            }
            other => return Err(Self::error(path, format!("unknown locked source .{other}"))),
        };
        PackageManifest::only_fields(path, args, expected_fields)
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let id = PackageManifest::string_field(path, args, "id")
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let name = PackageManifest::string_field(path, args, "package")
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let version = PackageManifest::string_field(path, args, "version")
            .map_err(|error| Self::from_manifest_error(path, error))?;
        let dependencies = Self::string_array(path, args, "dependencies")?;
        Ok(LockedPackage {
            id,
            name,
            version,
            source,
            dependencies,
        })
    }

    fn string_array(
        path: &Path,
        args: &[CallArg],
        field: &str,
    ) -> Result<Vec<String>, PackageError> {
        PackageManifest::array_field(path, args, field)
            .map_err(|error| Self::from_manifest_error(path, error))?
            .iter()
            .map(|value| {
                PackageManifest::string(path, value)
                    .map_err(|error| Self::from_manifest_error(path, error))
            })
            .collect()
    }

    fn render(&self) -> String {
        let mut rendered = String::new();
        rendered.push_str("Lock(\n");
        rendered.push_str(&format!("    format: {LOCK_FORMAT},\n"));
        rendered.push_str(&format!(
            "    fingerprint: {},\n",
            Self::quote(&self.fingerprint)
        ));
        rendered.push_str("    root_dependencies: [");
        Self::render_strings(&mut rendered, &self.root_dependencies);
        rendered.push_str("],\n");
        rendered.push_str("    packages: [\n");
        for package in &self.packages {
            match &package.source {
                LockedSource::Git {
                    url,
                    requested_rev,
                    commit,
                } => {
                    rendered.push_str("        .git(\n");
                    rendered.push_str(&format!("            id: {},\n", Self::quote(&package.id)));
                    rendered.push_str(&format!(
                        "            package: {},\n",
                        Self::quote(&package.name)
                    ));
                    rendered.push_str(&format!(
                        "            version: {},\n",
                        Self::quote(&package.version)
                    ));
                    rendered.push_str(&format!("            url: {},\n", Self::quote(url)));
                    rendered.push_str(&format!(
                        "            requested_rev: {},\n",
                        Self::quote(requested_rev)
                    ));
                    rendered.push_str(&format!("            commit: {},\n", Self::quote(commit)));
                }
                LockedSource::Tar { url, sha256 } => {
                    rendered.push_str("        .tar(\n");
                    rendered.push_str(&format!("            id: {},\n", Self::quote(&package.id)));
                    rendered.push_str(&format!(
                        "            package: {},\n",
                        Self::quote(&package.name)
                    ));
                    rendered.push_str(&format!(
                        "            version: {},\n",
                        Self::quote(&package.version)
                    ));
                    rendered.push_str(&format!("            url: {},\n", Self::quote(url)));
                    rendered.push_str(&format!("            sha256: {},\n", Self::quote(sha256)));
                }
                LockedSource::Path { path, base } => {
                    rendered.push_str("        .path(\n");
                    rendered.push_str(&format!("            id: {},\n", Self::quote(&package.id)));
                    rendered.push_str(&format!(
                        "            package: {},\n",
                        Self::quote(&package.name)
                    ));
                    rendered.push_str(&format!(
                        "            version: {},\n",
                        Self::quote(&package.version)
                    ));
                    rendered.push_str(&format!("            path: {},\n", Self::quote(path)));
                    let base = match base {
                        PathBase::Root => "root",
                        PathBase::Package(package) => package,
                    };
                    rendered.push_str(&format!("            base: {},\n", Self::quote(base)));
                }
            }
            rendered.push_str("            dependencies: [");
            Self::render_strings(&mut rendered, &package.dependencies);
            rendered.push_str("],\n        ),\n");
        }
        rendered.push_str("    ]\n)\n");
        rendered
    }

    fn render_strings(rendered: &mut String, values: &[String]) {
        for (index, value) in values.iter().enumerate() {
            if index > 0 {
                rendered.push_str(", ");
            }
            rendered.push_str(&Self::quote(value));
        }
    }

    fn quote(value: &str) -> String {
        let mut quoted = String::from("\"");
        for ch in value.chars() {
            match ch {
                '\\' => quoted.push_str("\\\\"),
                '\"' => quoted.push_str("\\\""),
                '\n' => quoted.push_str("\\n"),
                '\r' => quoted.push_str("\\r"),
                '\t' => quoted.push_str("\\t"),
                _ => quoted.push(ch),
            }
        }
        quoted.push('\"');
        quoted
    }

    fn error(path: &Path, message: impl Into<String>) -> PackageError {
        PackageError::Lock {
            path: path.to_path_buf(),
            message: message.into(),
        }
    }

    fn from_manifest_error(path: &Path, error: PackageError) -> PackageError {
        match error {
            PackageError::Manifest { message, .. } => Self::error(path, message),
            other => other,
        }
    }
}

#[derive(Clone, Debug)]
struct PackageStore {
    root: PathBuf,
    offline: bool,
}

impl PackageStore {
    fn new(offline: bool) -> Result<Self, PackageError> {
        let root = std::env::var_os("TALK_PACKAGE_CACHE")
            .filter(|path| !path.is_empty())
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("XDG_CACHE_HOME")
                    .filter(|path| !path.is_empty())
                    .map(|path| PathBuf::from(path).join("talk/packages"))
            })
            .or_else(|| {
                std::env::var_os("HOME")
                    .filter(|path| !path.is_empty())
                    .map(|path| PathBuf::from(path).join(".cache/talk/packages"))
            })
            .unwrap_or_else(|| std::env::temp_dir().join("talk/packages"));
        fs::create_dir_all(&root).map_err(|source| PackageError::Io {
            context: format!("failed to create package cache {}", root.display()),
            source,
        })?;
        Ok(Self { root, offline })
    }

    fn fetch(
        &self,
        dependency: &PackageDependency,
        base_root: &Path,
        base: PathBase,
    ) -> Result<(LockedSource, PathBuf), PackageError> {
        match &dependency.source {
            PackageSource::Git { url, rev } => self.fetch_git(url, rev),
            PackageSource::Tar { url, sha256 } => self.fetch_tar(url, sha256),
            PackageSource::Path { path } => self.fetch_path(path, base_root, base),
        }
    }

    fn materialize(
        &self,
        source: &LockedSource,
        path_base: Option<&Path>,
    ) -> Result<PathBuf, PackageError> {
        match source {
            LockedSource::Git { url, commit, .. } => {
                self.fetch_git(url, commit).map(|(_, path)| path)
            }
            LockedSource::Tar { url, sha256 } => self.fetch_tar(url, sha256).map(|(_, path)| path),
            LockedSource::Path { path, .. } => {
                let base = path_base.ok_or_else(|| {
                    PackageError::Cache(format!("path dependency {path:?} has no resolution base"))
                })?;
                self.local_path(path, base)
            }
        }
    }

    fn fetch_path(
        &self,
        path: &str,
        base_root: &Path,
        base: PathBase,
    ) -> Result<(LockedSource, PathBuf), PackageError> {
        let root = self.local_path(path, base_root)?;
        Ok((
            LockedSource::Path {
                path: path.to_string(),
                base,
            },
            root,
        ))
    }

    fn local_path(&self, path: &str, base: &Path) -> Result<PathBuf, PackageError> {
        if Path::new(path).is_absolute() {
            return Err(PackageError::Resolution(format!(
                "path dependency {path:?} must be relative"
            )));
        }
        let root = base
            .join(path)
            .canonicalize()
            .map_err(|source| PackageError::Io {
                context: format!(
                    "failed to find path dependency {path:?} from {}",
                    base.display()
                ),
                source,
            })?;
        if !root.is_dir() {
            return Err(PackageError::Resolution(format!(
                "path dependency {path:?} is not a directory"
            )));
        }
        Ok(root)
    }

    fn fetch_git(
        &self,
        url: &str,
        revision: &str,
    ) -> Result<(LockedSource, PathBuf), PackageError> {
        if self.offline {
            let exact_key = Self::git_key(url, revision);
            let exact_path = self.root.join("git").join(exact_key);
            if exact_path.is_dir() {
                return Ok((
                    LockedSource::Git {
                        url: url.to_string(),
                        requested_rev: revision.to_string(),
                        commit: revision.to_string(),
                    },
                    exact_path,
                ));
            }
            return Err(PackageError::Cache(format!(
                "offline mode cannot fetch Git dependency {url} at {revision}"
            )));
        }
        let temporary = self.temporary_dir("git")?;
        let result = (|| {
            self.command(
                "git",
                &[
                    "clone",
                    "--no-checkout",
                    "--",
                    url,
                    &temporary.to_string_lossy(),
                ],
                None,
            )?;
            let commit = self.git_commit(&temporary, revision)?;
            self.command(
                "git",
                &[
                    "-C",
                    &temporary.to_string_lossy(),
                    "checkout",
                    "--detach",
                    &commit,
                ],
                None,
            )?;
            let destination = self.root.join("git").join(Self::git_key(url, &commit));
            if destination.is_dir() {
                fs::remove_dir_all(&temporary).map_err(|source| PackageError::Io {
                    context: format!(
                        "failed to remove temporary checkout {}",
                        temporary.display()
                    ),
                    source,
                })?;
            } else {
                let parent = destination.parent().ok_or_else(|| {
                    PackageError::Cache(format!(
                        "cache path {} has no parent",
                        destination.display()
                    ))
                })?;
                fs::create_dir_all(parent).map_err(|source| PackageError::Io {
                    context: format!("failed to create cache directory {}", parent.display()),
                    source,
                })?;
                fs::rename(&temporary, &destination).map_err(|source| PackageError::Io {
                    context: format!("failed to store Git package at {}", destination.display()),
                    source,
                })?;
            }
            Ok((
                LockedSource::Git {
                    url: url.to_string(),
                    requested_rev: revision.to_string(),
                    commit,
                },
                destination,
            ))
        })();
        if result.is_err() {
            let _ = fs::remove_dir_all(&temporary);
        }
        result
    }

    fn fetch_tar(&self, url: &str, sha256: &str) -> Result<(LockedSource, PathBuf), PackageError> {
        let sha256 = sha256.to_ascii_lowercase();
        if !is_sha256(&sha256) {
            return Err(PackageError::Cache(format!("invalid SHA-256 for {url}")));
        }
        let destination = self.root.join("tar").join(&sha256);
        if destination.is_dir() {
            return Ok((
                LockedSource::Tar {
                    url: url.to_string(),
                    sha256,
                },
                destination,
            ));
        }
        if self.offline {
            return Err(PackageError::Cache(format!(
                "offline mode cannot fetch tar dependency {url}"
            )));
        }
        let temporary = self.temporary_dir("tar")?;
        let result = (|| {
            let archive = temporary.join("package.tar");
            self.command(
                "curl",
                &[
                    "--fail",
                    "--location",
                    "--silent",
                    "--show-error",
                    "--output",
                    &archive.to_string_lossy(),
                    "--",
                    url,
                ],
                None,
            )?;
            let bytes = fs::read(&archive).map_err(|source| PackageError::Io {
                context: format!("failed to read downloaded archive {}", archive.display()),
                source,
            })?;
            let actual = hex_digest(Sha256::digest(&bytes));
            if actual != sha256 {
                return Err(PackageError::Cache(format!(
                    "downloaded archive checksum for {url} was {actual}, expected {sha256}"
                )));
            }
            let listing = self.command("tar", &["-tf", &archive.to_string_lossy()], None)?;
            let listing = String::from_utf8_lossy(&listing.stdout);
            for entry in listing.lines() {
                let entry_path = Path::new(entry);
                if entry_path.is_absolute()
                    || entry_path
                        .components()
                        .any(|component| matches!(component, Component::ParentDir))
                {
                    return Err(PackageError::Cache(format!(
                        "archive {url} contains unsafe path {entry:?}"
                    )));
                }
            }
            let extracted = temporary.join("extracted");
            fs::create_dir_all(&extracted).map_err(|source| PackageError::Io {
                context: format!(
                    "failed to create extraction directory {}",
                    extracted.display()
                ),
                source,
            })?;
            self.command(
                "tar",
                &[
                    "-xf",
                    &archive.to_string_lossy(),
                    "-C",
                    &extracted.to_string_lossy(),
                ],
                None,
            )?;
            self.reject_symlinks(&extracted, url)?;
            let source_root = self.archive_package_root(&extracted, url)?;
            let parent = destination.parent().ok_or_else(|| {
                PackageError::Cache(format!(
                    "cache path {} has no parent",
                    destination.display()
                ))
            })?;
            fs::create_dir_all(parent).map_err(|source| PackageError::Io {
                context: format!("failed to create cache directory {}", parent.display()),
                source,
            })?;
            fs::rename(&source_root, &destination).map_err(|source| PackageError::Io {
                context: format!(
                    "failed to store extracted package at {}",
                    destination.display()
                ),
                source,
            })?;
            Ok((
                LockedSource::Tar {
                    url: url.to_string(),
                    sha256,
                },
                destination,
            ))
        })();
        let _ = fs::remove_dir_all(&temporary);
        result
    }

    fn git_commit(&self, checkout: &Path, revision: &str) -> Result<String, PackageError> {
        let local_revision = format!("{revision}^{{commit}}");
        let output = self
            .command(
                "git",
                &[
                    "-C",
                    &checkout.to_string_lossy(),
                    "rev-parse",
                    "--verify",
                    &local_revision,
                ],
                None,
            )
            .or_else(|_| {
                let remote_revision = format!("origin/{revision}^{{commit}}");
                self.command(
                    "git",
                    &[
                        "-C",
                        &checkout.to_string_lossy(),
                        "rev-parse",
                        "--verify",
                        &remote_revision,
                    ],
                    None,
                )
            })?;
        let commit = String::from_utf8(output.stdout)
            .map_err(|_| PackageError::Cache("git returned a non-UTF-8 commit id".into()))?;
        let commit = commit.trim();
        if commit.is_empty() {
            return Err(PackageError::Cache(
                "git resolved an empty commit id".into(),
            ));
        }
        Ok(commit.to_string())
    }

    fn reject_symlinks(&self, root: &Path, url: &str) -> Result<(), PackageError> {
        let entries = fs::read_dir(root).map_err(|source| PackageError::Io {
            context: format!("failed to inspect extracted archive {url}"),
            source,
        })?;
        for entry in entries {
            let entry = entry.map_err(|source| PackageError::Io {
                context: format!("failed to inspect extracted archive {url}"),
                source,
            })?;
            let file_type = entry.file_type().map_err(|source| PackageError::Io {
                context: format!("failed to inspect extracted archive {url}"),
                source,
            })?;
            if file_type.is_symlink() {
                return Err(PackageError::Cache(format!(
                    "archive {url} contains a symlink at {}",
                    entry.path().display()
                )));
            }
            if file_type.is_dir() {
                self.reject_symlinks(&entry.path(), url)?;
            }
        }
        Ok(())
    }

    fn archive_package_root(&self, extracted: &Path, url: &str) -> Result<PathBuf, PackageError> {
        if extracted.join(MANIFEST_FILE).is_file() {
            return Ok(extracted.to_path_buf());
        }
        let entries = fs::read_dir(extracted).map_err(|source| PackageError::Io {
            context: format!("failed to inspect extracted archive {url}"),
            source,
        })?;
        let roots = entries
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.is_dir() && path.join(MANIFEST_FILE).is_file())
            .collect::<Vec<_>>();
        match roots.as_slice() {
            [root] => Ok(root.clone()),
            [] => Err(PackageError::Cache(format!(
                "archive {url} contains no package.tlk at its root"
            ))),
            _ => Err(PackageError::Cache(format!(
                "archive {url} contains more than one package root"
            ))),
        }
    }

    fn command(
        &self,
        program: &str,
        arguments: &[&str],
        current_dir: Option<&Path>,
    ) -> Result<Output, PackageError> {
        let mut command = Command::new(program);
        command.args(arguments);
        if let Some(current_dir) = current_dir {
            command.current_dir(current_dir);
        }
        let output = command.output().map_err(|source| PackageError::Io {
            context: format!("failed to run {program}"),
            source,
        })?;
        if output.status.success() {
            return Ok(output);
        }
        Err(PackageError::Command {
            program: program.to_string(),
            arguments: arguments
                .iter()
                .map(|argument| (*argument).to_string())
                .collect(),
            status: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })
    }

    fn temporary_dir(&self, kind: &str) -> Result<PathBuf, PackageError> {
        let temporary_root = self.root.join(".tmp");
        fs::create_dir_all(&temporary_root).map_err(|source| PackageError::Io {
            context: format!(
                "failed to create temporary package directory {}",
                temporary_root.display()
            ),
            source,
        })?;
        for _ in 0..100 {
            let suffix = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = temporary_root.join(format!("{kind}-{}-{suffix}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(path),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(source) => {
                    return Err(PackageError::Io {
                        context: format!(
                            "failed to create temporary package directory {}",
                            path.display()
                        ),
                        source,
                    });
                }
            }
        }
        Err(PackageError::Cache(
            "could not allocate a temporary package directory".into(),
        ))
    }

    fn git_key(url: &str, commit: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(url.as_bytes());
        hasher.update([0]);
        hasher.update(commit.as_bytes());
        hex_digest(hasher.finalize())
    }
}

struct PackageResolver {
    store: PackageStore,
    packages: IndexMap<String, LockedPackage>,
    resolving: FxHashSet<String>,
    resolving_roots: FxHashSet<PathBuf>,
}

impl PackageResolver {
    fn new(store: PackageStore) -> Self {
        Self {
            store,
            packages: IndexMap::new(),
            resolving: FxHashSet::default(),
            resolving_roots: FxHashSet::default(),
        }
    }

    fn resolve(
        mut self,
        manifest: &PackageManifest,
        root: &Path,
    ) -> Result<PackageLock, PackageError> {
        let root_dependencies = manifest
            .dependencies
            .iter()
            .map(|dependency| self.resolve_dependency(dependency, root, PathBase::Root))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(PackageLock {
            fingerprint: manifest.dependency_fingerprint(),
            root_dependencies,
            packages: self.packages.into_values().collect(),
        })
    }

    fn resolve_dependency(
        &mut self,
        dependency: &PackageDependency,
        base_root: &Path,
        base: PathBase,
    ) -> Result<String, PackageError> {
        let (source, root) = self.store.fetch(dependency, base_root, base)?;
        let id = source.id();
        if self.packages.contains_key(&id) && !matches!(&source, LockedSource::Path { .. }) {
            return Ok(id);
        }
        if !self.resolving.insert(id.clone()) {
            return Err(PackageError::Resolution(format!(
                "package dependency cycle includes {}",
                dependency.package
            )));
        }
        if !self.resolving_roots.insert(root.clone()) {
            return Err(PackageError::Resolution(format!(
                "package dependency cycle includes {}",
                dependency.package
            )));
        }
        let manifest = PackageManifest::read(&root)?;
        if manifest.name != dependency.package {
            self.resolving.remove(&id);
            self.resolving_roots.remove(&root);
            return Err(PackageError::Resolution(format!(
                "dependency at {} declares package {:?}, expected {:?}",
                root.display(),
                manifest.name,
                dependency.package
            )));
        }
        let dependencies = manifest
            .dependencies
            .iter()
            .map(|child| self.resolve_dependency(child, &root, PathBase::Package(id.clone())))
            .collect::<Result<Vec<_>, _>>()?;
        self.resolving.remove(&id);
        self.resolving_roots.remove(&root);
        self.packages.insert(
            id.clone(),
            LockedPackage {
                id: id.clone(),
                name: manifest.name,
                version: manifest.version,
                source,
                dependencies,
            },
        );
        Ok(id)
    }
}

#[derive(Clone)]
struct CompiledLibrary {
    module: Module,
    typed: Arc<LibraryTyped>,
    module_id: ModuleId,
}

pub struct PackageProject {
    root: PathBuf,
    manifest: PackageManifest,
    lock: PackageLock,
    package_roots: FxHashMap<String, PathBuf>,
}

impl PackageProject {
    pub fn create_executable_at(
        root: impl AsRef<Path>,
        name: &str,
        version: &str,
        binary_name: &str,
    ) -> Result<(), PackageError> {
        let root = root.as_ref();
        if root.as_os_str().is_empty() {
            return Err(PackageError::Resolution(
                "package directory must not be empty".into(),
            ));
        }
        if root.exists() {
            return Err(PackageError::Resolution(format!(
                "package directory {} already exists",
                root.display()
            )));
        }
        if version.is_empty() {
            return Err(PackageError::Manifest {
                path: root.join(MANIFEST_FILE),
                message: "version must not be empty".into(),
            });
        }
        if binary_name.is_empty() {
            return Err(PackageError::Manifest {
                path: root.join(MANIFEST_FILE),
                message: "binary name must not be empty".into(),
            });
        }

        let parent = root.parent().ok_or_else(|| {
            PackageError::Resolution(format!(
                "package directory {} has no parent",
                root.display()
            ))
        })?;
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|source| PackageError::Io {
                context: format!("failed to create package parent {}", parent.display()),
                source,
            })?;
        }
        let directory_name = root
            .file_name()
            .ok_or_else(|| {
                PackageError::Resolution(format!(
                    "package directory {} has no name",
                    root.display()
                ))
            })?
            .to_string_lossy();
        let temporary = root.with_file_name(format!(
            ".{directory_name}-{}-{}.tmp",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&temporary).map_err(|source| PackageError::Io {
            context: format!(
                "failed to create temporary package directory {}",
                temporary.display()
            ),
            source,
        })?;

        let result = (|| {
            let manifest_path = temporary.join(MANIFEST_FILE);
            let manifest_source = Self::new_manifest_source(name, version, binary_name);
            let manifest = PackageManifest::parse(&manifest_path, &manifest_source)?;
            fs::write(&manifest_path, manifest_source).map_err(|source| PackageError::Io {
                context: format!("failed to write {}", manifest_path.display()),
                source,
            })?;

            let source_directory = temporary.join("src");
            fs::create_dir(&source_directory).map_err(|source| PackageError::Io {
                context: format!("failed to create {}", source_directory.display()),
                source,
            })?;
            let main_source = source_directory.join("main.tlk");
            fs::write(&main_source, "print(\"Hello, Talk!\")\n").map_err(|source| {
                PackageError::Io {
                    context: format!("failed to write {}", main_source.display()),
                    source,
                }
            })?;

            let tests_directory = temporary.join("tests");
            fs::create_dir(&tests_directory).map_err(|source| PackageError::Io {
                context: format!("failed to create {}", tests_directory.display()),
                source,
            })?;
            let test_source = tests_directory.join(format!("{name}.test.tlk"));
            fs::write(
                &test_source,
                "test(\"example\") {\n    assert(1 + 1 == 2)\n}\n",
            )
            .map_err(|source| PackageError::Io {
                context: format!("failed to write {}", test_source.display()),
                source,
            })?;

            PackageLock {
                fingerprint: manifest.dependency_fingerprint(),
                root_dependencies: Vec::new(),
                packages: Vec::new(),
            }
            .write(&temporary.join(LOCK_FILE))
        })();
        if let Err(error) = result {
            let _ = fs::remove_dir_all(&temporary);
            return Err(error);
        }

        fs::rename(&temporary, root).map_err(|source| PackageError::Io {
            context: format!("failed to create package directory {}", root.display()),
            source,
        })
    }

    fn new_manifest_source(name: &str, version: &str, binary_name: &str) -> String {
        format!(
            "Package(\n    name: {},\n    version: {},\n    builds: [.bin(named: {}, from: \"src/main.tlk\")],\n    dependencies: []\n)\n",
            Self::quote_manifest_string(name),
            Self::quote_manifest_string(version),
            Self::quote_manifest_string(binary_name),
        )
    }

    fn quote_manifest_string(value: &str) -> String {
        let mut quoted = String::from("\"");
        for ch in value.chars() {
            match ch {
                '\\' => quoted.push_str("\\\\"),
                '\"' => quoted.push_str("\\\""),
                '\n' => quoted.push_str("\\n"),
                '\r' => quoted.push_str("\\r"),
                '\t' => quoted.push_str("\\t"),
                _ => quoted.push(ch),
            }
        }
        quoted.push('\"');
        quoted
    }

    pub fn install_at(
        root: impl AsRef<Path>,
        offline: bool,
        update: bool,
    ) -> Result<Self, PackageError> {
        let root = root
            .as_ref()
            .canonicalize()
            .map_err(|source| PackageError::Io {
                context: format!(
                    "failed to find package directory {}",
                    root.as_ref().display()
                ),
                source,
            })?;
        let manifest = PackageManifest::read(&root)?;
        let lock_path = root.join(LOCK_FILE);
        let store = PackageStore::new(offline)?;
        let lock = if lock_path.is_file() && !update {
            let lock = PackageLock::read(&lock_path)?;
            if !lock.matches(&manifest) {
                return Err(PackageError::Resolution(
                    "package.tlk dependencies changed; run talk update to refresh package.lock"
                        .into(),
                ));
            }
            lock
        } else {
            let lock = PackageResolver::new(store.clone()).resolve(&manifest, &root)?;
            lock.write(&lock_path)?;
            lock
        };
        Self::from_lock(root, manifest, lock, store)
    }

    pub fn update_at(
        root: impl AsRef<Path>,
        offline: bool,
        selected: &[String],
    ) -> Result<Self, PackageError> {
        if selected.is_empty() {
            return Self::install_at(root, offline, true);
        }
        let root = root
            .as_ref()
            .canonicalize()
            .map_err(|source| PackageError::Io {
                context: format!(
                    "failed to find package directory {}",
                    root.as_ref().display()
                ),
                source,
            })?;
        let manifest = PackageManifest::read(&root)?;
        let lock_path = root.join(LOCK_FILE);
        let previous = PackageLock::read(&lock_path)?;
        if !previous.matches(&manifest) {
            return Err(PackageError::Resolution(
                "package.tlk dependencies changed; run talk update without package names".into(),
            ));
        }
        let direct_names = manifest
            .dependencies
            .iter()
            .map(|dependency| dependency.package.as_str())
            .collect::<HashSet<_>>();
        for package in selected {
            if !direct_names.contains(package.as_str()) {
                return Err(PackageError::Resolution(format!(
                    "{package:?} is not a direct dependency of this package"
                )));
            }
        }
        let selected = selected.iter().map(String::as_str).collect::<HashSet<_>>();
        let mut resolver = PackageResolver::new(PackageStore::new(offline)?);
        resolver.packages = previous
            .packages
            .iter()
            .cloned()
            .map(|package| (package.id.clone(), package))
            .collect();
        let mut root_dependencies = Vec::with_capacity(manifest.dependencies.len());
        for (index, dependency) in manifest.dependencies.iter().enumerate() {
            if selected.contains(dependency.package.as_str()) {
                root_dependencies.push(resolver.resolve_dependency(
                    dependency,
                    &root,
                    PathBase::Root,
                )?);
            } else {
                root_dependencies.push(previous.root_dependencies[index].clone());
            }
        }
        let mut lock = PackageLock {
            fingerprint: manifest.dependency_fingerprint(),
            root_dependencies,
            packages: resolver.packages.into_values().collect(),
        };
        lock.prune();
        lock.validate(&lock_path)?;
        lock.write(&lock_path)?;
        Self::from_lock(root, manifest, lock, PackageStore::new(offline)?)
    }

    pub fn open_at(root: impl AsRef<Path>, offline: bool) -> Result<Self, PackageError> {
        let root = root
            .as_ref()
            .canonicalize()
            .map_err(|source| PackageError::Io {
                context: format!(
                    "failed to find package directory {}",
                    root.as_ref().display()
                ),
                source,
            })?;
        let manifest = PackageManifest::read(&root)?;
        let lock_path = root.join(LOCK_FILE);
        if !lock_path.is_file() {
            return Err(PackageError::Resolution(
                "package.lock is missing; run talk install first".into(),
            ));
        }
        let lock = PackageLock::read(&lock_path)?;
        if !lock.matches(&manifest) {
            return Err(PackageError::Resolution(
                "package.tlk dependencies changed; run talk update to refresh package.lock".into(),
            ));
        }
        Self::from_lock(root, manifest, lock, PackageStore::new(offline)?)
    }

    pub fn exists_at(root: impl AsRef<Path>) -> bool {
        root.as_ref().join(MANIFEST_FILE).is_file()
    }

    pub fn compile_binary(&self, requested: Option<&str>) -> Result<Driver<Lowered>, PackageError> {
        let graph = self.compile_graph()?;
        let binary = self.manifest.binary(requested)?;
        let PackageArtifact::Binary { from, .. } = binary else {
            return Err(PackageError::Compile(
                "selected target is not a binary".into(),
            ));
        };
        let mut environment =
            self.environment_for(&self.lock.root_dependencies, &graph.dependencies)?;
        let mut libraries = graph
            .dependencies
            .values()
            .map(|library| Arc::clone(&library.typed))
            .collect::<Vec<_>>();
        if let Some(library) = &graph.root_library {
            environment
                .import_compiled(library.module.clone(), library.module_id)
                .map_err(PackageError::Compile)?;
            libraries.push(Arc::clone(&library.typed));
        }
        let source = self.manifest.source_path(&self.root, from)?;
        let workspace_root =
            self.root
                .join("src")
                .canonicalize()
                .map_err(|source| PackageError::Io {
                    context: format!(
                        "failed to find package source directory under {}",
                        self.root.display()
                    ),
                    source,
                })?;
        let mut config = DriverConfig::new(format!("{} binary", self.manifest.name)).executable();
        config.modules = Rc::new(environment);
        config.workspace_root = Some(workspace_root);
        config.libraries = libraries;
        let driver = Driver::new_bare(vec![Source::from(source)], config);
        self.lower(driver)
    }

    pub fn run_tests(&self) -> Result<crate::testing::Outcome, PackageError> {
        let Some(runner) = self.test_runner()? else {
            return Ok(crate::testing::Outcome::NoTests);
        };
        runner
            .run()
            .map_err(|error| PackageError::Compile(error.to_string()))
    }

    pub fn run_tests_json(&self) -> Result<crate::testing::JsonOutcome, PackageError> {
        let Some(runner) = self.test_runner()? else {
            return Ok(crate::testing::JsonOutcome::NoTests);
        };
        runner
            .run_json()
            .map_err(|error| PackageError::Compile(error.to_string()))
    }

    fn test_runner(&self) -> Result<Option<crate::testing::Runner>, PackageError> {
        let tests_root = self.root.join("tests");
        if !tests_root.is_dir() {
            return Ok(None);
        }
        let graph = self.compile_graph()?;
        let mut environment =
            self.environment_for(&self.lock.root_dependencies, &graph.dependencies)?;
        let mut libraries = graph
            .dependencies
            .values()
            .map(|library| Arc::clone(&library.typed))
            .collect::<Vec<_>>();
        if let Some(library) = &graph.root_library {
            environment
                .import_compiled(library.module.clone(), library.module_id)
                .map_err(PackageError::Compile)?;
            libraries.push(Arc::clone(&library.typed));
        }
        let mut config = DriverConfig::new(format!("{} tests", self.manifest.name));
        config.modules = Rc::new(environment);
        config.workspace_root = Some(self.root.clone());
        config.libraries = libraries;
        Ok(Some(crate::testing::Runner::with_config(
            [tests_root],
            config,
        )))
    }

    fn from_lock(
        root: PathBuf,
        manifest: PackageManifest,
        lock: PackageLock,
        store: PackageStore,
    ) -> Result<Self, PackageError> {
        let package_roots = lock.package_roots(&root, &store)?;
        for package in &lock.packages {
            let package_root = package_roots.get(&package.id).ok_or_else(|| {
                PackageError::Resolution(format!(
                    "missing source root for locked package {}",
                    package.name
                ))
            })?;
            let installed = PackageManifest::read(package_root)?;
            if installed.name != package.name || installed.version != package.version {
                return Err(PackageError::Resolution(format!(
                    "cached package at {} does not match locked {} {}",
                    package_root.display(),
                    package.name,
                    package.version
                )));
            }
        }
        Ok(Self {
            root,
            manifest,
            lock,
            package_roots,
        })
    }

    fn compile_graph(&self) -> Result<CompiledGraph, PackageError> {
        let base = Self::base_environment();
        let mut next_id = base.next_module_id().0;
        let mut ids = FxHashMap::default();
        for package in &self.lock.packages {
            ids.insert(package.id.clone(), ModuleId(next_id));
            next_id = next_id.checked_add(1).ok_or_else(|| {
                PackageError::Compile("too many packages to assign module ids".into())
            })?;
        }
        let root_id = ModuleId(next_id);
        let mut dependencies = IndexMap::new();
        for package in &self.lock.packages {
            let root = self.package_roots.get(&package.id).ok_or_else(|| {
                PackageError::Compile(format!(
                    "missing installed source for package {}",
                    package.name
                ))
            })?;
            let manifest = PackageManifest::read(root)?;
            let library = manifest.library().ok_or_else(|| {
                PackageError::Compile(format!(
                    "dependency {} has no library target",
                    manifest.name
                ))
            })?;
            let environment = self.environment_for(&package.dependencies, &dependencies)?;
            let module_id = *ids.get(&package.id).ok_or_else(|| {
                PackageError::Compile(format!("missing module id for package {}", package.name))
            })?;
            let compiled =
                self.compile_library(&manifest, root, library, module_id, environment)?;
            dependencies.insert(package.id.clone(), compiled);
        }
        let root_library = match self.manifest.library() {
            Some(library) => Some(self.compile_library(
                &self.manifest,
                &self.root,
                library,
                root_id,
                self.environment_for(&self.lock.root_dependencies, &dependencies)?,
            )?),
            None => None,
        };
        Ok(CompiledGraph {
            dependencies,
            root_library,
        })
    }

    fn compile_library(
        &self,
        manifest: &PackageManifest,
        root: &Path,
        library: &str,
        module_id: ModuleId,
        environment: ModuleEnvironment,
    ) -> Result<CompiledLibrary, PackageError> {
        let source = manifest.source_path(root, library)?;
        let workspace_root =
            root.join("src")
                .canonicalize()
                .map_err(|source| PackageError::Io {
                    context: format!(
                        "failed to find package source directory under {}",
                        root.display()
                    ),
                    source,
                })?;
        let mut config = DriverConfig::new(manifest.import_name());
        config.module_id = module_id;
        config.mode = CompilationMode::Library;
        config.modules = Rc::new(environment);
        config.workspace_root = Some(workspace_root);
        let driver = Driver::new_bare(vec![Source::from(source)], config);
        let parsed = driver.parse().map_err(|error| {
            PackageError::Compile(format!("failed to parse {}: {error:?}", manifest.name))
        })?;
        let resolved = parsed.resolve_names().map_err(|error| {
            PackageError::Compile(format!("failed to resolve {}: {error:?}", manifest.name))
        })?;
        let typed = resolved.type_check();
        if typed.has_errors() {
            return Err(PackageError::Compile(
                typed
                    .diagnostics()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("\n"),
            ));
        }
        let typed_library = Arc::new(LibraryTyped {
            program: typed.phase.program.clone(),
            checked_mir: typed.phase.checked_mir.clone(),
        });
        let module = typed.module(manifest.import_name());
        Ok(CompiledLibrary {
            module,
            typed: typed_library,
            module_id,
        })
    }

    fn lower(&self, driver: Driver) -> Result<Driver<Lowered>, PackageError> {
        let parsed = driver.parse().map_err(|error| {
            PackageError::Compile(format!("failed to parse package binary: {error:?}"))
        })?;
        let resolved = parsed.resolve_names().map_err(|error| {
            PackageError::Compile(format!("failed to resolve package binary: {error:?}"))
        })?;
        let typed = resolved.type_check();
        if typed.has_errors() {
            return Err(PackageError::Compile(
                typed
                    .diagnostics()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("\n"),
            ));
        }
        let lowered = typed.lower();
        if !lowered.phase.diagnostics.is_empty() {
            return Err(PackageError::Compile(lowered.phase.diagnostics.join("\n")));
        }
        Ok(lowered)
    }

    fn base_environment() -> ModuleEnvironment {
        let mut environment = ModuleEnvironment::default();
        environment.import_core(super::core::compile());
        for module in super::stdlib::modules() {
            environment.import((*module).clone());
        }
        environment
    }

    fn environment_for(
        &self,
        dependency_ids: &[String],
        compiled: &IndexMap<String, CompiledLibrary>,
    ) -> Result<ModuleEnvironment, PackageError> {
        let mut environment = Self::base_environment();
        for dependency_id in dependency_ids {
            let dependency = compiled.get(dependency_id).ok_or_else(|| {
                PackageError::Compile(format!("dependency {dependency_id} was not compiled first"))
            })?;
            environment
                .import_compiled(dependency.module.clone(), dependency.module_id)
                .map_err(PackageError::Compile)?;
        }
        Ok(environment)
    }
}

struct CompiledGraph {
    dependencies: IndexMap<String, CompiledLibrary>,
    root_library: Option<CompiledLibrary>,
}

pub fn normalized_import_name(package_name: &str) -> String {
    let mut normalized = package_name
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect::<String>();
    let starts_with_letter = normalized
        .as_bytes()
        .first()
        .is_some_and(u8::is_ascii_alphabetic);
    let is_identifier = starts_with_letter || (normalized.starts_with('_') && normalized.len() > 1);
    if !is_identifier || is_talk_keyword(&normalized) {
        normalized.insert_str(0, "pkg_");
    }
    normalized
}

fn is_talk_keyword(name: &str) -> bool {
    matches!(
        name,
        "any"
            | "as"
            | "func"
            | "let"
            | "if"
            | "else"
            | "true"
            | "false"
            | "loop"
            | "enum"
            | "case"
            | "match"
            | "return"
            | "struct"
            | "extend"
            | "break"
            | "init"
            | "protocol"
            | "import"
            | "use"
            | "public"
            | "linear"
            | "static"
            | "associated"
            | "typealias"
            | "effect"
            | "handling"
            | "in"
            | "continue"
            | "mut"
            | "consuming"
            | "for"
    )
}

fn is_compiler_module_name(name: &str) -> bool {
    matches!(name, "Core" | "fs" | "ansi" | "testing")
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn hex_digest(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes_package_names_to_talk_imports() {
        assert_eq!(normalized_import_name("talk-html"), "talk_html");
        assert_eq!(normalized_import_name("3d-tools"), "pkg_3d_tools");
        assert_eq!(normalized_import_name("let"), "pkg_let");
        assert_eq!(normalized_import_name("_"), "pkg__");
    }

    #[test]
    fn parses_a_declarative_manifest() {
        let path = Path::new("package.tlk");
        let manifest = PackageManifest::parse(
            path,
            r#"Package(
                name: "talk-html",
                version: "0.1.0",
                builds: [.lib(from: "src/lib.tlk")],
                dependencies: [.git(package: "talk-wasm", url: "https://example.test/wasm", rev: "main")]
            )"#,
        )
        .expect("manifest parses");
        assert_eq!(manifest.import_name(), "talk_html");
        assert_eq!(manifest.library(), Some("src/lib.tlk"));
        assert_eq!(manifest.dependencies.len(), 1);
    }

    #[test]
    fn creates_a_runnable_package_scaffold() {
        let parent = std::env::temp_dir().join(format!(
            "talk-package-new-test-{}-{}",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&parent).expect("create package parent");
        let root = parent.join("hello-world");
        PackageProject::create_executable_at(&root, "hello-world", "0.1.0", "main")
            .expect("create package");
        let manifest = PackageManifest::read(&root).expect("read generated manifest");
        assert_eq!(manifest.name, "hello-world");
        assert_eq!(manifest.library(), None);
        assert!(matches!(
            manifest.binary(None),
            Ok(PackageArtifact::Binary { name, from }) if name == "main" && from == "src/main.tlk"
        ));
        assert!(root.join("src/main.tlk").is_file());
        assert!(root.join("tests/hello-world.test.tlk").is_file());
        fs::remove_dir_all(parent).expect("remove package parent");
    }

    #[test]
    fn installs_a_relative_path_dependency_without_network_access() {
        let temporary = std::env::temp_dir().join(format!(
            "talk-package-path-test-{}-{}",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let dependency = temporary.join("dependency");
        let root = temporary.join("root");
        fs::create_dir_all(dependency.join("src")).expect("create dependency source");
        fs::create_dir_all(root.join("src")).expect("create root source");
        fs::write(
            dependency.join(MANIFEST_FILE),
            "Package(name: \"local-lib\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
        )
        .expect("write dependency manifest");
        fs::write(
            dependency.join("src/lib.tlk"),
            "public func answer() -> Int { 42 }",
        )
        .expect("write dependency source");
        fs::write(
            root.join(MANIFEST_FILE),
            "Package(name: \"root\", version: \"0.1.0\", builds: [], dependencies: [.path(package: \"local-lib\", path: \"../dependency\")])",
        )
        .expect("write root manifest");
        PackageProject::install_at(&root, true, false).expect("install path dependency");
        let project = PackageProject::open_at(&root, true).expect("open locked path dependency");
        assert_eq!(project.lock.packages.len(), 1);
        assert!(matches!(
            project.lock.packages[0].source,
            LockedSource::Path {
                base: PathBase::Root,
                ..
            }
        ));
        assert!(root.join(LOCK_FILE).is_file());
        fs::remove_dir_all(temporary).expect("remove temporary directory");
    }

    #[test]
    fn lockfile_round_trips() {
        let root = std::env::temp_dir().join(format!(
            "talk-package-lock-test-{}-{}",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).expect("create temporary directory");
        let path = root.join(LOCK_FILE);
        let source = LockedSource::Git {
            url: "https://example.test/talk-wasm".into(),
            requested_rev: "main".into(),
            commit: "0123456789012345678901234567890123456789".into(),
        };
        let id = source.id();
        let lock = PackageLock {
            fingerprint: "fingerprint".into(),
            root_dependencies: vec![id.clone()],
            packages: vec![LockedPackage {
                id,
                name: "talk-wasm".into(),
                version: "0.1.0".into(),
                source,
                dependencies: vec![],
            }],
        };
        lock.write(&path).expect("write lockfile");
        let parsed = PackageLock::read(&path).expect("read lockfile");
        assert_eq!(parsed.root_dependencies, lock.root_dependencies);
        assert_eq!(parsed.packages[0].name, "talk-wasm");
        fs::remove_dir_all(root).expect("remove temporary directory");
    }

    #[test]
    fn resolves_a_git_dependency_to_a_commit() {
        let temporary = std::env::temp_dir().join(format!(
            "talk-package-git-test-{}-{}",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let dependency = temporary.join("dependency");
        let cache = temporary.join("cache");
        fs::create_dir_all(dependency.join("src")).expect("create dependency source");
        fs::write(
            dependency.join(MANIFEST_FILE),
            "Package(name: \"remote-lib\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
        )
        .expect("write dependency manifest");
        fs::write(
            dependency.join("src/lib.tlk"),
            "public func answer() -> Int { 42 }",
        )
        .expect("write dependency source");
        for arguments in [
            vec!["init", "-q"],
            vec!["add", "."],
            vec![
                "-c",
                "user.name=Talk test",
                "-c",
                "user.email=test@example.com",
                "commit",
                "-qm",
                "initial",
            ],
        ] {
            let status = Command::new("git")
                .args(arguments)
                .current_dir(&dependency)
                .status()
                .expect("run git");
            assert!(status.success(), "git command failed");
        }
        let manifest = PackageManifest::parse(
            Path::new("package.tlk"),
            &format!(
                "Package(name: \"root\", version: \"0.1.0\", builds: [], dependencies: [.git(package: \"remote-lib\", url: \"{}\", rev: \"HEAD\")])",
                dependency.display()
            ),
        )
        .expect("parse root manifest");
        let lock = PackageResolver::new(PackageStore {
            root: cache.clone(),
            offline: false,
        })
        .resolve(&manifest, &temporary)
        .expect("resolve git dependency");
        let [package] = lock.packages.as_slice() else {
            panic!("expected one locked package");
        };
        let LockedSource::Git { commit, .. } = &package.source else {
            panic!("expected a Git source");
        };
        assert!(!commit.is_empty());
        let cached = fs::read_dir(cache.join("git"))
            .expect("read Git cache")
            .next()
            .is_some();
        assert!(cached, "Git checkout was not stored in the cache");
        fs::remove_dir_all(temporary).expect("remove temporary directory");
    }

    #[test]
    fn rejects_colliding_normalized_dependency_names() {
        let error = PackageManifest::parse(
            Path::new("package.tlk"),
            r#"Package(
                name: "root",
                version: "0.1.0",
                builds: [],
                dependencies: [
                    .git(package: "talk-html", url: "https://example.test/a", rev: "main"),
                    .git(package: "talk_html", url: "https://example.test/b", rev: "main")
                ]
            )"#,
        )
        .expect_err("colliding imports fail");
        assert!(error.to_string().contains("same Talk import name"));
    }
}
