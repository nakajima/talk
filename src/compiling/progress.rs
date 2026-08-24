//! Compiler progress events, independent of terminal presentation.
//!
//! The compiler reports semantic phase changes through a scoped reporter.
//! Embedders do nothing by default; the CLI installs its spinner only while
//! running a user-facing compile.

use std::{cell::RefCell, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Parsing,
    ExpandingMacros,
    Desugaring,
    ResolvingNames,
    TypeChecking,
    BuildingTypedProgram,
    CheckingOwnership,
    BuildingMir,
    OptimizingMir,
    AllocatingRegisters,
    GeneratingBytecode,
    EncodingBytecode,
    EmittingC,
    CompilingNative,
}

impl Phase {
    pub fn label(self) -> &'static str {
        match self {
            Self::Parsing => "Parsing",
            Self::ExpandingMacros => "Expanding macros",
            Self::Desugaring => "Desugaring",
            Self::ResolvingNames => "Resolving names",
            Self::TypeChecking => "Type checking",
            Self::BuildingTypedProgram => "Building typed program",
            Self::CheckingOwnership => "Checking ownership",
            Self::BuildingMir => "Building MIR",
            Self::OptimizingMir => "Optimizing MIR",
            Self::AllocatingRegisters => "Allocating registers",
            Self::GeneratingBytecode => "Generating bytecode",
            Self::EncodingBytecode => "Encoding bytecode",
            Self::EmittingC => "Emitting C",
            Self::CompilingNative => "Compiling native executable",
        }
    }
}

pub type Reporter = Arc<dyn Fn(Phase) + Send + Sync>;

thread_local! {
    static REPORTER: RefCell<Option<Reporter>> = RefCell::new(None);
}

struct ReporterGuard(Option<Reporter>);

impl Drop for ReporterGuard {
    fn drop(&mut self) {
        REPORTER.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

pub fn with_reporter<R>(reporter: Reporter, operation: impl FnOnce() -> R) -> R {
    let previous = REPORTER.with(|slot| slot.replace(Some(reporter)));
    let _guard = ReporterGuard(previous);
    operation()
}

pub fn report(phase: Phase) {
    let reporter = REPORTER.with(|slot| slot.borrow().clone());
    if let Some(reporter) = reporter {
        reporter(phase);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    #[test]
    fn reporters_are_scoped_and_restored() {
        let phases = Arc::new(Mutex::new(Vec::new()));
        let outer_phases = phases.clone();
        with_reporter(
            Arc::new(move |phase| {
                outer_phases
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .push(phase);
            }),
            || {
                report(Phase::Parsing);
                with_reporter(Arc::new(|_| {}), || report(Phase::Desugaring));
                report(Phase::TypeChecking);
            },
        );
        report(Phase::BuildingMir);

        assert_eq!(
            *phases
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            vec![Phase::Parsing, Phase::TypeChecking]
        );
    }
}
