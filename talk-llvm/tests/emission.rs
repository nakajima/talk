use talk_llvm::{
    BlockData, Constant, DisplayNames, Function, Inst, Operand, Program, Runtime, ScalarOp, Term,
};

fn runtime() -> Runtime<'static, u8> {
    Runtime {
        native_prelude: "",
        display_names: DisplayNames::default(),
        string_symbol: 1,
        storage_symbol: 2,
    }
}

#[test]
fn emits_a_standalone_language_function_from_the_public_model() {
    let program = Program {
        functions: vec![Function {
            name: "answer".into(),
            arity: 0,
            n_locals: 1,
            blocks: vec![BlockData {
                params: vec![],
                insts: vec![Inst::Scalar {
                    dest: 0,
                    op: ScalarOp::IntAdd,
                    a: Operand::Const(Constant::Int(40)),
                    b: Some(Operand::Const(Constant::Int(2))),
                }],
                term: Some(Term::Return(Operand::Local(0))),
            }],
        }],
        entry: 0,
        global_slots: 0,
        layouts: vec![],
    };

    let artifact = talk_llvm::emit(&program, runtime()).expect("module emits");
    assert!(artifact.ir.contains("define void @talk_fn0"));
    assert!(artifact.ir.contains(" add i64 "));
    assert!(artifact.runtime_c.contains("talk_llvm_entry"));
}

#[test]
fn rejects_an_entry_that_the_native_process_cannot_call() {
    let program = Program {
        functions: vec![Function {
            name: "parameterized".into(),
            arity: 1,
            n_locals: 1,
            blocks: vec![BlockData {
                params: vec![],
                insts: vec![],
                term: Some(Term::Return(Operand::Local(0))),
            }],
        }],
        entry: 0,
        global_slots: 0,
        layouts: vec![],
    };

    let error = talk_llvm::emit(&program, runtime()).expect_err("entry must be rejected");
    assert!(error.message().contains("entry function with parameters"));
}
