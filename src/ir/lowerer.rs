use crate::ir::ir_ty::IrTy;
use crate::ir::parse_instruction;
use crate::types::scheme::Scheme;
use crate::{
    ast::AST,
    compiling::driver::Source,
    ir::{
        basic_block::{BasicBlock, BasicBlockId},
        instruction::{Instruction, InstructionMeta},
        ir_error::IRError,
        monomorphizer::Monomorphizer,
        program::Program,
        register::Register,
        terminator::Terminator,
        value::Value,
    },
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, SynthesizedId},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    },
    span::Span,
    types::{
        scheme::ForAll,
        ty::Ty,
        type_session::{TypeEntry, Types},
    },
};
use rustc_hash::FxHashMap;
use tracing::instrument;

#[derive(Debug)]
pub(super) struct CurrentFunction {
    current_block_idx: usize,
    blocks: Vec<BasicBlock<Ty>>,
    pub registers: RegisterAllocator,
}

impl Default for CurrentFunction {
    fn default() -> Self {
        CurrentFunction {
            current_block_idx: 0,
            blocks: vec![BasicBlock::<Ty> {
                id: BasicBlockId(0),
                instructions: Default::default(),
                terminator: Terminator::Unreachable,
            }],
            registers: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Bind {
    Named { symbol: Symbol, value: Register },
    Fresh,
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub(super) struct RegisterAllocator {
    next: u32,
}

impl RegisterAllocator {
    fn next(&mut self) -> Register {
        let i = self.next;
        self.next += 1;
        Register(i)
    }
}

#[derive(Clone)]
pub(super) struct PolyFunction {
    pub name: Name,
    pub _foralls: Vec<ForAll>,
    pub params: Vec<Value>,
    pub blocks: Vec<BasicBlock<Ty>>,
    pub ty: Ty,
}

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer {
    pub(super) asts: FxHashMap<Source, AST<NameResolved>>,
    pub(super) types: Types,
    pub(super) functions: FxHashMap<Symbol, PolyFunction>,
    pub(super) current_functions: Vec<CurrentFunction>,
    pub(super) needs_monomorphization: Vec<Name>,
    pub(super) instantiations: FxHashMap<NodeID, FxHashMap<ForAll, Ty>>,
    bindings: FxHashMap<Symbol, Register>,
}

impl Lowerer {
    pub fn new(asts: FxHashMap<Source, AST<NameResolved>>, types: Types) -> Self {
        Self {
            asts,
            types,
            functions: Default::default(),
            current_functions: Default::default(),
            needs_monomorphization: Default::default(),
            instantiations: Default::default(),
            bindings: Default::default(),
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.asts.is_empty() {
            return Ok(Program::default());
        }

        // Do we have a main func?
        let mut asts = std::mem::take(&mut self.asts);
        let has_main_func = asts.iter_mut().flat_map(|a| &a.1.roots).any(is_main_func);
        if !has_main_func {
            let mut ret_ty = Ty::Void;
            let func = Func {
                id: NodeID(FileID::SYNTHESIZED, 0),
                name: Name::Resolved(Symbol::Synthesized(SynthesizedId::from(0)), "main".into()),
                name_span: Span {
                    start: 0,
                    end: 0,
                    file_id: FileID(0),
                },
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID(FileID(0), 0),
                    args: vec![],
                    span: Span {
                        start: 0,
                        end: 0,
                        file_id: FileID(0),
                    },
                    body: {
                        let roots: Vec<Node> = asts
                            .values_mut()
                            .flat_map(|a| std::mem::take(&mut a.roots))
                            .collect();

                        if let Some(last) = roots.last() {
                            ret_ty = match self
                                .types
                                .get(&last.node_id())
                                .unwrap_or(&TypeEntry::Mono(Ty::Void))
                            {
                                TypeEntry::Mono(ty) => ty.clone(),
                                TypeEntry::Poly(scheme) => scheme.ty.clone(),
                            };
                        }

                        roots
                    },
                },
                ret: None,
                attributes: vec![],
            };

            let ast = asts.iter_mut().next().unwrap();
            ast.1.roots.push(Node::Decl(Decl {
                id: NodeID(FileID::SYNTHESIZED, 0),
                span: Span::SYNTHESIZED,
                kind: DeclKind::Let {
                    lhs: Pattern {
                        id: NodeID(FileID::SYNTHESIZED, 0),
                        span: Span::SYNTHESIZED,
                        kind: PatternKind::Bind(Name::Resolved(
                            SynthesizedId::from(0).into(),
                            "main".into(),
                        )),
                    },
                    type_annotation: None,
                    value: Some(Expr {
                        id: NodeID(FileID::SYNTHESIZED, 0),
                        span: Span::SYNTHESIZED,
                        kind: ExprKind::Func(func),
                    }),
                },
            }));

            self.types.define(
                NodeID(FileID::SYNTHESIZED, 0),
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into())),
            );
        }

        self.current_functions.push(CurrentFunction::default());

        for ast in asts.values_mut() {
            for root in ast.roots.iter() {
                self.lower_node(root)?;
            }
        }

        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
        })
    }

    fn lower_node(&mut self, node: &Node) -> Result<Value, IRError> {
        match node {
            Node::Decl(decl) => self.lower_decl(decl),
            Node::Stmt(stmt) => self.lower_stmt(stmt),
            _ => unreachable!("node not handled: {node:?}"),
        }
    }

    #[instrument(skip(self, decl), fields(decl.id = %decl.id))]
    fn lower_decl(&mut self, decl: &Decl) -> Result<Value, IRError> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                value: Some(value),
                ..
            } => {
                let bind = self.lower_pattern(lhs)?;
                self.lower_expr(value, bind)?;
            }
            DeclKind::Init { .. } => todo!(),
            DeclKind::Property { .. } => todo!(),
            DeclKind::Method { .. } => todo!(),
            DeclKind::Associated { .. } => todo!(),
            DeclKind::Func(..) => todo!(),
            DeclKind::Extend { .. } => todo!(),
            DeclKind::Enum { .. } => todo!(),
            DeclKind::EnumVariant(..) => todo!(),
            DeclKind::FuncSignature(..) => todo!(),
            DeclKind::MethodRequirement(..) => todo!(),
            DeclKind::TypeAlias(..) => todo!(),
            _ => (), // Nothing to do
        }

        Ok(Value::Void)
    }

    #[instrument(skip(self, stmt), fields(stmt.id = %stmt.id))]
    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<Value, IRError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.lower_expr(expr, Bind::Fresh),
            StmtKind::If(_expr, _block, _block1) => todo!(),
            StmtKind::Return(_expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(_expr, _expr1) => todo!(),
            StmtKind::Loop(_expr, _block) => todo!(),
        }
    }

    #[instrument(skip(self, pattern), fields(pattern.id = %pattern.id))]
    fn lower_pattern(&mut self, pattern: &Pattern) -> Result<Bind, IRError> {
        match &pattern.kind {
            PatternKind::Bind(name) => {
                let value = self.next_register();
                let symbol = name.symbol().unwrap();
                self.bindings.insert(symbol, value);
                Ok(Bind::Named { symbol, value })
            }
            PatternKind::LiteralInt(_) => todo!(),
            PatternKind::LiteralFloat(_) => todo!(),
            PatternKind::LiteralTrue => todo!(),
            PatternKind::LiteralFalse => todo!(),
            PatternKind::Tuple(..) => todo!(),
            PatternKind::Wildcard => todo!(),
            PatternKind::Variant { .. } => todo!(),
            PatternKind::Record { .. } => todo!(),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(skip(self, expr), fields(expr.id = %expr.id))]
    fn lower_expr(&mut self, expr: &Expr, bind: Bind) -> Result<Value, IRError> {
        match &expr.kind {
            ExprKind::Func(func) => self.lower_func(func, bind),
            ExprKind::LiteralArray(_exprs) => todo!(),
            ExprKind::LiteralInt(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::ConstantInt {
                    dest: ret,
                    val: str::parse(val).unwrap(),
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok(ret.into())
            }
            ExprKind::LiteralFloat(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::ConstantFloat {
                    dest: ret,
                    val: str::parse(val).unwrap(),
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok(ret.into())
            }
            ExprKind::LiteralTrue => todo!(),
            ExprKind::LiteralFalse => todo!(),
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(..) => todo!(),
            ExprKind::Block(..) => todo!(),
            ExprKind::Call {
                box callee, args, ..
            } => self.lower_call(expr.id, callee, args, bind),
            ExprKind::Member(..) => todo!(),
            ExprKind::Variable(name) => self.lower_variable(name),
            ExprKind::Constructor(..) => todo!(),
            ExprKind::If(..) => todo!(),
            ExprKind::Match(..) => todo!(),
            ExprKind::RecordLiteral { .. } => todo!(),
            ExprKind::RowVariable(..) => todo!(),
            _ => unreachable!("cannot lower expr: {expr:?}"),
        }
    }

    #[instrument(skip(self))]
    fn lower_variable(&mut self, name: &Name) -> Result<Value, IRError> {
        let ty = self
            .types
            .get_symbol(&name.symbol().unwrap())
            .unwrap_or_else(|| panic!("did not get variable type: {name:?}"));

        let ret = if matches!(
            ty,
            TypeEntry::Mono(Ty::Func(..))
                | TypeEntry::Poly(Scheme {
                    ty: Ty::Func(..),
                    ..
                })
        ) {
            // It's a func reference so we pass the name
            Value::Func(name.clone())
        } else {
            self.bindings.get(&name.symbol().unwrap()).unwrap().into()
        };

        Ok(ret)
    }

    #[instrument(skip(self))]
    fn lower_call(
        &mut self,
        id: NodeID,
        callee: &Expr,
        args: &[CallArg],
        bind: Bind,
    ) -> Result<Value, IRError> {
        let dest = self.ret(bind);

        // Handle embedded IR call
        if let ExprKind::Variable(name) = &callee.kind
            && name.symbol().unwrap() == Symbol::IR
        {
            let ExprKind::LiteralString(string) = &args[0].value.kind else {
                unreachable!()
            };

            let mut string = string.clone();

            if string.contains("$?") {
                string = string.replace("$?", &format!("%{}", dest.0));
            }

            self.push_instr(parse_instruction::<IrTy>(&string).into());

            return Ok(dest.into());
        }

        let ty = match self.types.get(&id).unwrap() {
            TypeEntry::Mono(ty) => ty.clone(),
            TypeEntry::Poly(scheme) => scheme.ty.clone(),
        };

        let callee = self.lower_expr(callee, Bind::Fresh)?;
        let args = args
            .iter()
            .map(|arg| self.lower_expr(&arg.value, Bind::Fresh))
            .collect::<Result<Vec<_>, _>>()?
            .into();

        self.push_instr(Instruction::Call {
            dest,
            ty,
            callee,
            args,
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok(dest.into())
    }

    #[instrument(skip(self, func), fields(func = %func.name))]
    fn lower_func(&mut self, func: &Func, bind: Bind) -> Result<Value, IRError> {
        let ty = match self
            .types
            .get(&func.id)
            .unwrap_or_else(|| panic!("didn't get func ty: {:?}", func.id))
            .clone()
        {
            TypeEntry::Mono(ty) => (ty, vec![]),
            TypeEntry::Poly(scheme) => (scheme.ty, scheme.foralls),
        };

        let (Ty::Func(param_tys, box ret_ty), _foralls) = ty else {
            panic!("didn't get func ty");
        };

        let _s = tracing::trace_span!("pushing new current function");
        self.current_functions.push(CurrentFunction::default());

        let mut params = vec![];
        for param in func.params.iter() {
            let register = self.next_register();
            params.push(Value::Reg(register.0));
            self.bindings.insert(param.name.symbol().unwrap(), register);
        }

        let mut ret = Value::Void;
        for node in func.body.body.iter() {
            ret = self.lower_node(node)?;
        }
        self.push_terminator(Terminator::Ret {
            val: ret,
            ty: ret_ty.clone(),
        });

        let current_function = self
            .current_functions
            .pop()
            .expect("did not get current function");
        drop(_s);
        self.functions.insert(
            func.name.symbol().unwrap(),
            PolyFunction {
                name: func.name.clone(),
                params,
                blocks: current_function.blocks,
                _foralls: Default::default(),
                ty: Ty::Func(param_tys.clone(), ret_ty.clone().into()),
            },
        );

        let func = Value::Func(func.name.clone());
        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty: Ty::Func(param_tys, ret_ty.into()),
            val: func.clone(),
        });
        Ok(func)
    }

    #[instrument(skip(self))]
    fn push_instr(&mut self, instruction: Instruction<Ty>) {
        let current_function = self.current_functions.last_mut().unwrap();
        current_function.blocks[current_function.current_block_idx]
            .instructions
            .push(instruction);
    }

    #[instrument(skip(self))]
    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let current_function = self.current_functions.last_mut().unwrap();
        current_function.blocks[current_function.current_block_idx].terminator = terminator;
    }

    fn next_register(&mut self) -> Register {
        let current_function = self.current_functions.last_mut().unwrap();
        let register = current_function.registers.next();
        tracing::trace!("allocated register: {register}");
        register
    }

    fn ret(&mut self, bind: Bind) -> Register {
        match bind {
            Bind::Named { value, .. } => value,
            Bind::Fresh => self.next_register(),
        }
    }
}

fn is_main_func(node: &Node) -> bool {
    if let Node::Decl(Decl {
        kind:
            DeclKind::Let {
                value:
                    Some(Expr {
                        kind:
                            ExprKind::Func(Func {
                                name: Name::Resolved(Symbol::Global(..), name),
                                ..
                            }),
                        ..
                    }),
                ..
            },
        ..
    }) = node
        && name == "main"
    {
        return true;
    }

    false
}

#[cfg(test)]
pub mod tests {
    use crate::{
        assert_eq_diff,
        compiling::driver::{Driver, Source},
        fxhashmap,
        ir::{
            basic_block::{BasicBlock, BasicBlockId},
            function::Function,
            instruction::{Instruction, InstructionMeta},
            ir_ty::IrTy,
            lowerer::Lowerer,
            program::Program,
            terminator::Terminator,
            value::Value,
        },
        name::Name,
        name_resolution::symbol::{GlobalId, Symbol, SynthesizedId},
        node_id::{FileID, NodeID},
    };

    pub fn lower(input: &str) -> Program {
        let driver = Driver::new_bare(vec![Source::from(input)], Default::default());
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let lowerer = Lowerer::new(typed.phase.asts, typed.phase.types);
        lowerer.lower().unwrap()
    }

    #[test]
    fn lowers_int_literal() {
        let program = lower("func main() { 123 }");
        assert_eq!(
            program.functions,
            fxhashmap!(GlobalId::from(1).into() => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt { dest: 0.into(), val: 123, meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_float_literal() {
        let program = lower("func main() { 1.23 }");
        assert_eq!(
            program.functions,
            fxhashmap!(GlobalId::from(1).into() => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Float.into()),
                blocks: vec![BasicBlock {
                id: BasicBlockId(0),
                instructions: vec![
                    Instruction::ConstantFloat { dest: 0.into(), val: 1.23, meta: vec![InstructionMeta::Source(NodeID::ANY)].into() }
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(0),
                    ty: IrTy::Float
                }
                }],
            })
        );
    }

    #[test]
    fn synthesizes_main() {
        let program = lower("123");
        assert_eq!(
            program.functions,
            fxhashmap!(SynthesizedId::from(0).into() => Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                    blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt { dest: 0.into(), val: 123, meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_variables() {
        let program = lower("let a = 123 ; a");
        assert_eq!(
            program.functions,
            fxhashmap!(SynthesizedId::from(0).into() => Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                    blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt { dest: 0.into(), val: 123, meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_func_call() {
        let program = lower(
            "
        func foo(x: Int) { x }
        foo(123)
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(0)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                            val: Value::Func(Name::Resolved(
                                GlobalId::from(1).into(),
                                "foo".into()
                            ))
                        },
                        Instruction::ConstantInt {
                            dest: 2.into(),
                            val: 123,
                            meta: vec![InstructionMeta::Source(NodeID(FileID(0), 8))].into(),
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                GlobalId::from(1).into(),
                                "foo".into()
                            )),
                            args: vec![Value::Reg(2)].into(),
                            meta: vec![InstructionMeta::Source(NodeID(FileID(0), 10))].into(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(1),
                        ty: IrTy::Int
                    }
                }],
            }
        );
        assert_eq!(
            *program
                .functions
                .get(&Symbol::from(GlobalId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(GlobalId::from(1).into(), "foo".into()),
                params: vec![Value::Reg(0)].into(),
                ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn embedded_ir() {
        let program = lower(
            "
        __IR<Int>(\"$? = add int 1 2\")
        ",
        );
        assert_eq!(
            program.functions,
            fxhashmap!(SynthesizedId::from(0).into() => Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![Instruction::Add {
                        dest: 0.into(),
                        ty: IrTy::Int,
                        a: Value::Int(1),
                        b: Value::Int(2),
                        meta: vec![].into(),
                    }],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn embedded_ir_uses_variables() {
        let program = lower(
            "
        let a = 1
        let b = 2
        __IR<Int>(\"$? = add int %0 %1\")
        ",
        );
        assert_eq!(
            *program
                .functions
                .get(&SynthesizedId::from(0).into())
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 0.into(),
                            val: 1,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::ConstantInt {
                            dest: 1.into(),
                            val: 2,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Add {
                            dest: 2.into(),
                            ty: IrTy::Int,
                            a: Value::Reg(0),
                            b: Value::Reg(1),
                            meta: vec![].into(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(2),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }
}
