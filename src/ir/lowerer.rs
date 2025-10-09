use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    compiling::driver::Source,
    ir::{
        basic_block::{BasicBlock, BasicBlockId},
        instruction::{Instruction, InstructionMeta},
        monomorphizer::Monomorphizer,
        program::Program,
        register::Register,
        terminator::Terminator,
        value::Value,
    },
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        stmt::{Stmt, StmtKind},
    },
    types::{
        scheme::ForAll,
        ty::Ty,
        type_session::{TypeEntry, Types},
    },
};

#[derive(Debug)]
pub(super) struct CurrentFunction {
    current_block_idx: usize,
    next_block_id: usize,
    blocks: Vec<BasicBlock<Ty>>,
    pub registers: RegisterAllocator,
    pub symbols: FxHashMap<Symbol, Value>,
}

impl Default for CurrentFunction {
    fn default() -> Self {
        CurrentFunction {
            current_block_idx: 0,
            next_block_id: 1,
            blocks: vec![BasicBlock::<Ty> {
                id: BasicBlockId(0),
                instructions: Default::default(),
                terminator: Terminator::Ret {
                    val: Value::Void,
                    ty: Ty::Void,
                },
            }],
            registers: Default::default(),
            symbols: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IRError {}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
struct RegisterAllocator {
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
    pub foralls: Vec<ForAll>,
    pub blocks: Vec<BasicBlock<Ty>>,
    pub ty: Ty,
}

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer<'a> {
    pub(super) asts: &'a FxHashMap<Source, AST<NameResolved>>,
    pub(super) types: &'a Types,
    pub(super) functions: FxHashMap<Name, PolyFunction>,
    pub(super) current_functions: Vec<CurrentFunction>,
    pub(super) needs_monomorphization: Vec<Name>,
    pub(super) instantiations: FxHashMap<NodeID, FxHashMap<ForAll, Ty>>,
}

impl<'a> Lowerer<'a> {
    pub fn new(asts: &'a FxHashMap<Source, AST<NameResolved>>, types: &'a Types) -> Self {
        Self {
            asts,
            types,
            functions: Default::default(),
            current_functions: Default::default(),
            needs_monomorphization: Default::default(),
            instantiations: Default::default(),
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        for ast in self.asts.values() {
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
            _ => Ok(Value::Void), // Nothing to be done
        }
    }

    fn lower_decl(&mut self, decl: &Decl) -> Result<Value, IRError> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                value: Some(value),
                ..
            } => {
                self.lower_expr(value)?;
            }
            DeclKind::Init { name, params, body } => todo!(),
            DeclKind::Property {
                name,
                name_span,
                is_static,
                type_annotation,
                default_value,
            } => todo!(),
            DeclKind::Method { func, is_static } => todo!(),
            DeclKind::Associated { generic } => todo!(),
            DeclKind::Func(func) => todo!(),
            DeclKind::Extend {
                name,
                name_span,
                conformances,
                generics,
                body,
            } => todo!(),
            DeclKind::Enum {
                name,
                name_span,
                conformances,
                generics,
                body,
            } => todo!(),
            DeclKind::EnumVariant(name, span, type_annotations) => todo!(),
            DeclKind::FuncSignature(func_signature) => todo!(),
            DeclKind::MethodRequirement(func_signature) => todo!(),
            DeclKind::TypeAlias(type_annotation, type_annotation1) => todo!(),
            _ => (), // Nothing to do
        }

        Ok(Value::Void)
    }

    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<Value, IRError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.lower_expr(expr),
            StmtKind::If(expr, block, block1) => todo!(),
            StmtKind::Return(expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(expr, expr1) => todo!(),
            StmtKind::Loop(expr, block) => todo!(),
        }
    }

    fn lower_expr(&mut self, expr: &Expr) -> Result<Value, IRError> {
        match &expr.kind {
            ExprKind::Func(func) => self.lower_func(func),

            ExprKind::LiteralArray(exprs) => todo!(),
            ExprKind::LiteralInt(val) => {
                let ret = self.next_register();
                self.push_instr(Instruction::ConstantInt(
                    ret,
                    str::parse(val).unwrap(),
                    vec![InstructionMeta::NodeID(expr.id)],
                ));
                Ok(ret.into())
            }
            ExprKind::LiteralFloat(val) => {
                let ret = self.next_register();
                self.push_instr(Instruction::ConstantFloat(
                    ret,
                    str::parse(val).unwrap(),
                    vec![InstructionMeta::NodeID(expr.id)],
                ));
                Ok(ret.into())
            }
            ExprKind::LiteralTrue => todo!(),
            ExprKind::LiteralFalse => todo!(),
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(token_kind, expr) => todo!(),
            ExprKind::Binary(expr, token_kind, expr1) => todo!(),
            ExprKind::Tuple(exprs) => todo!(),
            ExprKind::Block(block) => todo!(),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => todo!(),
            ExprKind::Member(expr, label, span) => todo!(),
            ExprKind::Variable(name) => todo!(),
            ExprKind::Constructor(name) => todo!(),
            ExprKind::If(expr, block, block1) => todo!(),
            ExprKind::Match(expr, match_arms) => todo!(),
            ExprKind::RecordLiteral { fields, spread } => todo!(),
            ExprKind::RowVariable(name) => todo!(),
            _ => unreachable!("cannot lower expr: {expr:?}"),
        }
    }

    fn lower_func(&mut self, func: &Func) -> Result<Value, IRError> {
        let ty = match self
            .types
            .get(&func.id)
            .expect("didn't get func ty")
            .clone()
        {
            TypeEntry::Mono(ty) => (ty, vec![]),
            TypeEntry::Poly(scheme) => (scheme.ty, scheme.foralls),
        };

        let (Ty::Func(params, box ret_ty), foralls) = ty else {
            panic!("didn't get func ty");
        };

        self.current_functions.push(CurrentFunction::default());

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
        self.functions.insert(
            func.name.clone(),
            PolyFunction {
                name: func.name.clone(),
                blocks: current_function.blocks,
                foralls,
                ty: Ty::Func(params, ret_ty.into()),
            },
        );

        Ok(Value::Void)
    }

    fn push_instr(&mut self, instruction: Instruction<Ty>) {
        let current_function = self.current_functions.last_mut().unwrap();
        current_function.blocks[current_function.current_block_idx]
            .instructions
            .push(instruction);
    }

    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let current_function = self.current_functions.last_mut().unwrap();
        current_function.blocks[current_function.current_block_idx].terminator = terminator;
    }

    fn next_register(&mut self) -> Register {
        let current_function = self.current_functions.last_mut().unwrap();
        current_function.registers.next()
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
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
        name_resolution::symbol::GlobalId,
        node_id::NodeID,
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

        let lowerer = Lowerer::new(&typed.phase.asts, &typed.phase.types);
        lowerer.lower().unwrap()
    }

    #[test]
    fn lowers_int_literal() {
        let program = lower("func main() { 123 }");
        assert_eq!(
            program.functions,
            fxhashmap!(Name::Resolved(GlobalId::from(1).into(), "main".into()) => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![Instruction::ConstantInt(0.into(), 123, vec![InstructionMeta::NodeID(NodeID::ANY)])],
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
            fxhashmap!(Name::Resolved(GlobalId::from(1).into(), "main".into()) => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                ty: IrTy::Func(vec![], IrTy::Float.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![Instruction::ConstantFloat(0.into(), 1.23, vec![InstructionMeta::NodeID(NodeID::ANY)])],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Float
                    }
                }],
            })
        );
    }
}
