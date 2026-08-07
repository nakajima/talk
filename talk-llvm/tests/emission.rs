use talk_mir::{
    BlockData, Constant, Function, Inst, MirSymbol, MirSymbolKind, Module, Operand, ScalarOp, Term,
};

fn string_symbol() -> MirSymbol {
    MirSymbol {
        kind: MirSymbolKind::Struct,
        module: 0,
        local: 1,
    }
}

fn storage_symbol() -> MirSymbol {
    MirSymbol {
        kind: MirSymbolKind::Struct,
        module: 0,
        local: 2,
    }
}

fn module(functions: Vec<Function>) -> Module {
    Module {
        debug_files: Vec::new(),
        functions,
        entry: 0,
        global_slots: 0,
        exports: Vec::new(),
        layout_table: Vec::new(),
        display: Default::default(),
        string_symbol: string_symbol(),
        storage_symbol: storage_symbol(),
    }
}

fn function(name: &str, arity: u16, insts: Vec<Inst>, term: Term) -> Function {
    Function {
        debug_names: None,
        name: name.into(),
        arity,
        locals: talk_mir::LocalInfo::uniform(arity.max(1)),
        blocks: vec![BlockData {
            debug: None,
            params: vec![],
            insts,
            term: Some(term),
        }],
        param_reprs: Vec::new(),
        return_repr: None,
        frame_sites: Default::default(),
    }
}

#[test]
fn emits_a_standalone_language_function_from_the_public_model() {
    let program = module(vec![function(
        "answer",
        0,
        vec![Inst::Scalar {
            dest: 0,
            op: ScalarOp::IntAdd,
            a: Operand::Const(Constant::Int(40)),
            b: Some(Operand::Const(Constant::Int(2))),
        }],
        Term::Return(Operand::Local(0)),
    )]);

    let artifact = talk_llvm::emit(&program).expect("module emits");
    assert!(artifact.ir.contains("define void @talk_fn0"));
    assert!(artifact.ir.contains(" add i64 "));
    assert!(artifact.runtime_c.contains("talk_llvm_entry"));
}

/// A library fixture: an inert entry plus one exported function.
fn library_module() -> Module {
    let mut program = module(vec![
        function(
            "entry",
            0,
            vec![],
            Term::Return(Operand::Const(Constant::Unit)),
        ),
        function(
            "double",
            1,
            vec![Inst::Scalar {
                dest: 0,
                op: ScalarOp::IntMul,
                a: Operand::Local(0),
                b: Some(Operand::Const(Constant::Int(2))),
            }],
            Term::Return(Operand::Local(0)),
        ),
    ]);
    program.exports = vec![("double".to_string(), 1)];
    program
}

#[test]
fn library_emission_namespaces_symbols_and_omits_main() {
    let artifact = talk_llvm::emit_library(&library_module(), "mylib").expect("library emits");
    // Every cross-translation-unit symbol carries the prefix, so two
    // generated libraries link into one process (ADR 0048).
    assert!(
        artifact.ir.contains("define void @mylib_fn1"),
        "{}",
        artifact.ir
    );
    assert!(
        artifact.ir.contains("define void @mylib_llvm_dispatch"),
        "{}",
        artifact.ir
    );
    assert!(!artifact.ir.contains("@talk_llvm_"), "{}", artifact.ir);
    assert!(!artifact.ir.contains("@talk_fn"), "{}", artifact.ir);
    // The process entry point disappears with `main`.
    assert!(!artifact.ir.contains("llvm_entry"), "{}", artifact.ir);
    assert!(
        !artifact.runtime_c.contains("int main("),
        "{}",
        artifact.runtime_c
    );
    assert!(
        artifact.runtime_c.starts_with("#define TALK_LIBRARY 1"),
        "{}",
        artifact.runtime_c
    );
    // The wrapper enters generated code through the renamed dispatch.
    assert!(
        artifact
            .runtime_c
            .contains("int mylib_double(TalkValue *out, const TalkValue *args, size_t argc)"),
        "{}",
        artifact.runtime_c
    );
    assert!(
        artifact
            .runtime_c
            .contains("mylib_llvm_dispatch(&result, 1, NULL, args);"),
        "{}",
        artifact.runtime_c
    );
    assert!(
        !artifact.runtime_c.contains("talk_llvm_"),
        "{}",
        artifact.runtime_c
    );
    assert!(
        artifact.runtime_c.contains("int mylib_init(void)"),
        "{}",
        artifact.runtime_c
    );
    // Header and manifest speak the shared convention.
    assert!(
        artifact
            .header
            .contains("int mylib_double(mylib_value *out, const mylib_value *args, size_t argc);"),
        "{}",
        artifact.header
    );
    assert_eq!(artifact.manifest, "double\tmylib_double\n");
}

#[test]
fn library_emission_reports_adapter_errors() {
    let invalid_prefix = talk_llvm::emit_library(&library_module(), "1bad");
    assert!(
        invalid_prefix.is_err_and(|error| error.message().contains("prefix")),
        "an invalid prefix must be rejected"
    );
    let mut no_exports = library_module();
    no_exports.exports.clear();
    assert!(
        talk_llvm::emit_library(&no_exports, "lib").is_err(),
        "a library with no exports must be rejected"
    );
    let mut missing = library_module();
    missing.exports = vec![("double".to_string(), 9)];
    assert!(
        talk_llvm::emit_library(&missing, "lib").is_err(),
        "an export naming a missing function must be rejected"
    );
}

#[test]
fn rejects_an_entry_that_the_native_process_cannot_call() {
    let program = module(vec![function(
        "parameterized",
        1,
        vec![],
        Term::Return(Operand::Local(0)),
    )]);

    let error = talk_llvm::emit(&program).expect_err("entry must be rejected");
    assert!(error.message().contains("entry function with parameters"));
}
