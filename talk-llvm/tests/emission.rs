use talk_mir::{
    BlockData, Constant, Function, Inst, MirSymbol, MirSymbolKind, Module, Operand, ScalarOp,
    Term,
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
        name: name.into(),
        arity,
        locals: talk_mir::LocalInfo::uniform(arity.max(1)),
        blocks: vec![BlockData {
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
