use std::fmt::Display;

use crate::compiling::driver::DriverConfig;
use crate::compiling::module::ModuleId;
use crate::formatter;
use crate::ir::basic_block::{Phi, PhiSource};
use crate::ir::instruction::CmpOperator;
use crate::ir::ir_ty::IrTy;
use crate::ir::monomorphizer::uncurry_function;
use crate::ir::parse_instruction;
use crate::ir::value::{Addr, Reference};
use crate::label::Label;
use crate::name_resolution::symbol::{
    GlobalId, InitializerId, InstanceMethodId, StaticMethodId, Symbols,
};
use crate::node_kinds::inline_ir_instruction::{InlineIRInstruction, InlineIRInstructionKind};
use crate::node_kinds::match_arm::MatchArm;
use crate::node_kinds::parameter::Parameter;
use crate::node_kinds::record_field::RecordField;
use crate::node_kinds::type_annotation::TypeAnnotation;
use crate::token_kind::TokenKind;
use crate::types::infer_row::RowParamId;
use crate::types::infer_ty::TypeParamId;
use crate::types::row::Row;
use crate::types::type_catalog::MemberWitness;
use crate::types::type_session::TypeDefKind;
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
use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

#[derive(Debug)]
enum LValue {
    Field {
        base: Box<LValue>,
        field: Label,
        ty: Ty,
    },
    Variable(Symbol),
}

impl Display for LValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug)]
pub(super) struct CurrentFunction {
    current_block_idx: Vec<usize>,
    blocks: Vec<BasicBlock<Ty>>,
    pub registers: RegisterAllocator,
    bindings: FxHashMap<Symbol, Binding<Ty>>,
}

impl Default for CurrentFunction {
    fn default() -> Self {
        CurrentFunction {
            current_block_idx: vec![0],
            blocks: vec![BasicBlock::<Ty> {
                phis: Default::default(),
                id: BasicBlockId(0),
                instructions: Default::default(),
                terminator: Terminator::Unreachable,
            }],
            registers: Default::default(),
            bindings: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct StaticMemory {
    pub data: Vec<u8>,
}

impl StaticMemory {
    pub fn write(&mut self, value: Value) -> usize {
        let addr = self.data.len();
        self.data.extend(value.as_bytes());
        addr
    }

    #[allow(clippy::unwrap_used)]
    #[warn(clippy::todo)]
    pub fn load(&self, at: usize, len: usize, ty: IrTy) -> Value {
        let bytes = &self.data[at..len];
        match ty {
            IrTy::Int => Value::Int(i64::from_le_bytes(bytes.try_into().unwrap())),
            IrTy::Float => Value::Float(f64::from_le_bytes(bytes.try_into().unwrap())),
            IrTy::Bool => Value::Bool(bytes[0] == 1),
            IrTy::Func(..) => Value::Func(Symbol::from_bytes(bytes.try_into().unwrap())),
            IrTy::Record(..) => unreachable!("can only load primitives"),
            IrTy::RawPtr => Value::RawPtr(Addr(usize::from_le_bytes(bytes.try_into().unwrap()))),
            IrTy::Byte => Value::RawBuffer(bytes.to_vec()),
            IrTy::Void => unreachable!("cannot load the void"),
            IrTy::Buffer(..) => Value::RawBuffer(bytes.to_vec()),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Bind {
    Assigned(Register),
    Indirect(Register, Symbol),
    Fresh,
    Discard,
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

#[derive(Default, Clone, Debug)]
pub(super) struct Substitutions {
    pub ty: FxHashMap<TypeParamId, Ty>,
    pub row: FxHashMap<RowParamId, Row>,
    /// Maps MethodRequirement symbols to their concrete implementations for witness specialization
    pub witnesses: FxHashMap<Symbol, Symbol>,
}

impl Substitutions {
    pub fn extend(&mut self, other: Substitutions) {
        self.ty.extend(other.ty);
        self.row.extend(other.row);
        self.witnesses.extend(other.witnesses);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PolyFunction {
    pub name: Name,
    pub params: Vec<Value>,
    pub blocks: Vec<BasicBlock<Ty>>,
    pub ty: Ty,
    pub register_count: usize,
}

#[derive(Debug, Clone)]
pub struct Specialization {
    pub name: Name,
    pub(super) substitutions: Substitutions,
}

#[derive(Debug, Clone)]
pub enum Binding<T> {
    Register(u32),
    Pointer(Value),
    Capture { index: usize, ty: T },
}

impl<T> From<Register> for Binding<T> {
    fn from(value: Register) -> Self {
        Binding::Register(value.0)
    }
}

impl<T> From<Value> for Binding<T> {
    fn from(value: Value) -> Self {
        Binding::Pointer(value)
    }
}

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer<'a> {
    pub(super) asts: &'a mut IndexMap<Source, AST<NameResolved>>,
    pub(super) types: &'a mut Types,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,
    pub(super) config: &'a DriverConfig,

    current_ast_id: usize,
    symbols: &'a mut Symbols,
    pub(super) specializations: IndexMap<Symbol, Vec<Specialization>>,
    static_memory: StaticMemory,
}

#[allow(clippy::panic)]
#[allow(clippy::expect_used)]
impl<'a> Lowerer<'a> {
    pub fn new(
        asts: &'a mut IndexMap<Source, AST<NameResolved>>,
        types: &'a mut Types,
        symbols: &'a mut Symbols,
        config: &'a DriverConfig,
    ) -> Self {
        Self {
            asts,
            types,
            functions: Default::default(),
            current_function_stack: Default::default(),
            symbols,
            specializations: Default::default(),
            static_memory: Default::default(),
            config,
            current_ast_id: 0,
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.asts.is_empty() {
            return Ok(Program::default());
        }

        // Do we have a main func?
        let has_main_func = self.asts.iter().flat_map(|a| &a.1.roots).any(is_main_func);
        if !has_main_func {
            let main_symbol = Symbol::Synthesized(self.symbols.next_synthesized(ModuleId::Current));
            let mut ret_ty = Ty::Void;
            let func = Func {
                id: NodeID(FileID::SYNTHESIZED, 0),
                name: Name::Resolved(main_symbol, "main".into()),
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
                        let roots: Vec<Node> = self
                            .asts
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

            #[allow(clippy::unwrap_used)]
            let ast = self.asts.iter_mut().next().unwrap();
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
                    rhs: Some(Expr {
                        id: NodeID(FileID::SYNTHESIZED, 0),
                        span: Span::SYNTHESIZED,
                        kind: ExprKind::Func(func),
                    }),
                },
            }));

            self.types.define(
                main_symbol,
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into())),
            );
            ast.1
                .phase
                .symbols_to_string
                .insert(main_symbol, "main(synthesized)".to_string());
        }

        self.current_function_stack.push(CurrentFunction::default());

        for i in 0..self.asts.len() {
            self.current_ast_id = i;
            let roots = std::mem::take(&mut self.asts[i].roots);
            for root in roots.iter() {
                self.lower_node(root, &Default::default())?;
            }

            _ = std::mem::replace(&mut self.asts[i].roots, roots);
        }

        // Check for required imports
        let funcs = self.functions.keys().cloned().collect_vec();
        for sym in funcs {
            self.check_import(&sym);
        }

        let static_memory = std::mem::take(&mut self.static_memory);
        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
            polyfunctions: monomorphizer.functions,
            static_memory,
        })
    }

    fn lower_node(
        &mut self,
        node: &Node,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        self.lower_node_with_bind(node, instantiations, Bind::Fresh)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, node), fields(node.id = %node.node_id()))]
    fn lower_node_with_bind(
        &mut self,
        node: &Node,
        instantiations: &Substitutions,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        match node {
            Node::Decl(decl) => self.lower_decl(decl, instantiations),
            Node::Stmt(stmt) => self.lower_stmt(stmt, instantiations, bind),
            _ => unreachable!("node not handled: {node:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl), fields(decl.id = %decl.id))]
    fn lower_decl(
        &mut self,
        decl: &Decl,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                rhs: Some(value),
                ..
            } => {
                let bind = self.lower_pattern(lhs)?;
                if let Bind::Indirect(reg, ..) = &bind {
                    let (val, ty) = self.lower_expr(value, Bind::Fresh, instantiations)?;
                    self.push_instr(Instruction::Store {
                        value: val,
                        ty,
                        addr: reg.into(),
                    });
                } else {
                    self.lower_expr(value, bind, instantiations)?;
                }
            }
            DeclKind::Struct { body, .. } | DeclKind::Protocol { body, .. } => {
                for decl in &body.decls {
                    self.lower_decl(decl, instantiations)?;
                }
            }
            DeclKind::Init { name, params, body } => {
                self.lower_init(decl, name, params, body, instantiations)?;
            }
            DeclKind::Property { .. } => (),
            DeclKind::Method { func, .. } => {
                self.lower_method(func)?;
            }
            DeclKind::Associated { .. } => (),
            DeclKind::Func(..) => (), // Handled by DeclKind::Let
            DeclKind::Extend { body, .. } => {
                for decl in &body.decls {
                    self.lower_decl(decl, instantiations)?;
                }
            }
            DeclKind::Enum { body, .. } => {
                for decl in &body.decls {
                    self.lower_decl(decl, instantiations)?;
                }
            }
            DeclKind::EnumVariant(..) => (),
            DeclKind::FuncSignature(..) => (),
            DeclKind::MethodRequirement(..) => (),
            DeclKind::TypeAlias(..) => (),

            _ => (), // Nothing to do
        }

        Ok((Value::Void, Ty::Void))
    }

    fn lower_method(&mut self, func: &Func) -> Result<(Value, Ty), IRError> {
        self.lower_func(func, Bind::Discard, &Default::default())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, body))]
    fn lower_init(
        &mut self,
        decl: &Decl,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let func_ty = match self
            .types
            .get_symbol(&name.symbol().expect("name not resolved"))
            .unwrap_or_else(|| panic!("did not get func ty for {name:?}"))
        {
            TypeEntry::Mono(ty) => ty.clone(),
            TypeEntry::Poly(scheme) => scheme.ty.clone(),
        };

        let Ty::Func(..) = func_ty else {
            unreachable!();
        };

        let (param_tys, mut ret_ty) = uncurry_function(func_ty.clone());

        // Build param_ty from all params (for now, just use the first one for compatibility)
        let param_ty = if !param_tys.is_empty() {
            param_tys[0].clone()
        } else {
            let meta = Default::default();
            let formatter = formatter::Formatter::new(&meta);
            unreachable!(
                "init has no params - param_tys: {param_tys:?} name: {name:?}, sym: {:?}, ty: {:?}, {:?}",
                #[allow(clippy::unwrap_used)]
                self.types
                    .get_symbol(&name.symbol().expect("name not resolved"))
                    .unwrap(),
                func_ty,
                formatter.format(&[Node::Decl(decl.clone())], 80)
            );
        };

        self.current_function_stack.push(CurrentFunction::default());

        let mut param_values = vec![];
        for param in params.iter() {
            let register = self.next_register();
            param_values.push(Value::Reg(register.0));
            self.insert_binding(
                param.name.symbol().expect("name not resolved"),
                register.into(),
            );
        }

        let mut ret = Value::Void;
        for node in body.body.iter() {
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
        }

        if ret == Value::Poison {
            self.push_terminator(Terminator::Unreachable);
        } else {
            self.push_terminator(Terminator::Ret {
                val: ret.clone(),
                ty: ret_ty.clone(),
            });
        }

        #[allow(clippy::expect_used)]
        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");

        self.functions.insert(
            name.symbol().expect("name not resolved"),
            PolyFunction {
                name: name.clone(),
                params: param_values,
                blocks: current_function.blocks,
                ty: Ty::Func(Box::new(param_ty.clone()), Box::new(ret_ty.clone())),
                register_count: (current_function.registers.next) as usize,
            },
        );

        Ok((ret, ret_ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt), fields(stmt.id = %stmt.id))]
    fn lower_stmt(
        &mut self,
        stmt: &Stmt,
        instantiations: &Substitutions,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.lower_expr(expr, bind, instantiations),
            StmtKind::If(cond, conseq, alt) => {
                self.lower_if_stmt(cond, conseq, alt, instantiations)
            }
            StmtKind::Return(expr) => self.lower_return(expr, bind, instantiations),
            #[allow(clippy::todo)]
            StmtKind::Break => todo!(),
            StmtKind::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs, instantiations),
            StmtKind::Loop(cond, block) => self.lower_loop(cond, block, instantiations),
        }
    }

    fn lower_loop(
        &mut self,
        cond: &Option<Expr>,
        block: &Block,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let top_block_id = self.new_basic_block();
        let body_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();

        self.push_terminator(Terminator::Jump { to: top_block_id });

        self.in_basic_block(top_block_id, |lowerer| {
            if let Some(cond) = cond {
                let (val, _) = lowerer.lower_expr(cond, Bind::Fresh, instantiations)?;
                lowerer.push_terminator(Terminator::Branch {
                    cond: val,
                    conseq: body_block_id,
                    alt: join_block_id,
                });
            } else {
                lowerer.push_terminator(Terminator::Jump { to: body_block_id });
            }

            Ok(())
        })?;

        self.in_basic_block(body_block_id, |lowerer| {
            lowerer.lower_block(block, Bind::Discard, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: top_block_id });

            Ok(())
        })?;

        self.set_current_block(join_block_id);

        Ok((Value::Void, Ty::Void))
    }

    fn lower_return(
        &mut self,
        expr: &Option<Expr>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (val, ty) = if let Some(expr) = expr {
            self.lower_expr(expr, bind, instantiations)?
        } else {
            (Value::Void, Ty::Void)
        };

        self.push_terminator(Terminator::Ret {
            val: val.clone(),
            ty: ty.clone(),
        });

        Ok((val, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn lower_if_expr(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Block,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let cond_ir = self.lower_expr(cond, Bind::Fresh, instantiations)?;

        let conseq_block_id = self.new_basic_block();
        let alt_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();

        let conseq_val = self.in_basic_block(conseq_block_id, |lowerer| {
            let (val, _) = lowerer.lower_block(conseq, Bind::Fresh, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(val)
        })?;

        let alt_val = self.in_basic_block(alt_block_id, |lowerer| {
            let (val, _) = lowerer.lower_block(alt, Bind::Fresh, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(val)
        })?;

        self.push_terminator(Terminator::Branch {
            cond: cond_ir.0,
            conseq: conseq_block_id,
            alt: alt_block_id,
        });

        let ret = self.ret(bind);
        let ty = self.ty_from_id(&conseq.id)?;

        self.set_current_block(join_block_id);
        self.push_phi(Phi {
            dest: ret,
            ty: ty.clone(),
            sources: vec![
                PhiSource {
                    from_id: conseq_block_id,
                    value: conseq_val,
                },
                PhiSource {
                    from_id: alt_block_id,
                    value: alt_val,
                },
            ]
            .into(),
        });

        Ok((ret.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn lower_if_stmt(
        &mut self,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let cond_ir = self.lower_expr(cond, Bind::Fresh, instantiations)?;

        let conseq_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();

        self.in_basic_block(conseq_block_id, |lowerer| {
            lowerer.lower_block(conseq, Bind::Discard, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(())
        })?;

        let else_id = if let Some(alt) = alt {
            let alt_block_id = self.new_basic_block();
            self.in_basic_block(alt_block_id, |lowerer| {
                lowerer.lower_block(alt, Bind::Discard, instantiations)?;
                lowerer.push_terminator(Terminator::Jump { to: join_block_id });
                Ok(())
            })?;
            alt_block_id
        } else {
            join_block_id
        };

        self.push_terminator(Terminator::Branch {
            cond: cond_ir.0,
            conseq: conseq_block_id,
            alt: else_id,
        });

        self.set_current_block(join_block_id);

        Ok((Value::Void, Ty::Void))
    }

    /// Lower binary operators. Most binary operators are converted to method calls
    /// earlier in the pipeline, but `||` and `&&` need short-circuit evaluation.
    fn lower_binary(
        &mut self,
        expr: &Expr,
        lhs: &Expr,
        op: TokenKind,
        rhs: &Expr,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        match op {
            TokenKind::PipePipe => self.lower_or(expr, lhs, rhs, bind, instantiations),
            TokenKind::AmpAmp => self.lower_and(expr, lhs, rhs, bind, instantiations),
            _ => Ok((Value::Void, Ty::Void)), // Other operators converted to calls earlier
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs, instantiations))]
    fn lower_or(
        &mut self,
        expr: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let lhs_block_id = self.get_current_block();
        let rhs_block_id = self.new_basic_block();
        let rhs_register = self.next_register();
        let join_block_id = self.new_basic_block();

        let (lhs_val, lhs_ty) = self.lower_expr(lhs, Bind::Fresh, instantiations)?;
        assert_eq!(lhs_ty, Ty::Bool);

        self.push_terminator(Terminator::Branch {
            cond: lhs_val,
            conseq: join_block_id,
            alt: rhs_block_id,
        });

        self.in_basic_block(rhs_block_id, |lowerer| {
            lowerer.lower_expr(rhs, Bind::Assigned(rhs_register), instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(())
        })?;

        let ret = self.ret(bind);
        self.set_current_block(join_block_id);
        self.push_phi(Phi {
            dest: ret,
            ty: Ty::Bool,
            sources: vec![
                PhiSource {
                    from_id: lhs_block_id,
                    value: Value::Bool(true),
                },
                PhiSource {
                    from_id: rhs_block_id,
                    value: rhs_register.into(),
                },
            ]
            .into(),
        });

        Ok((ret.into(), Ty::Bool))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs, instantiations))]
    fn lower_and(
        &mut self,
        expr: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let lhs_block_id = self.get_current_block();
        let rhs_block_id = self.new_basic_block();
        let rhs_register = self.next_register();
        let join_block_id = self.new_basic_block();

        let (lhs_val, lhs_ty) = self.lower_expr(lhs, Bind::Fresh, instantiations)?;
        assert_eq!(lhs_ty, Ty::Bool);

        self.push_terminator(Terminator::Branch {
            cond: lhs_val,
            conseq: rhs_block_id,
            alt: join_block_id,
        });

        self.in_basic_block(rhs_block_id, |lowerer| {
            lowerer.lower_expr(rhs, Bind::Assigned(rhs_register), instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(())
        })?;

        let ret = self.ret(bind);
        self.set_current_block(join_block_id);
        self.push_phi(Phi {
            dest: ret,
            ty: Ty::Bool,
            sources: vec![
                PhiSource {
                    from_id: lhs_block_id,
                    value: Value::Bool(false),
                },
                PhiSource {
                    from_id: rhs_block_id,
                    value: rhs_register.into(),
                },
            ]
            .into(),
        });

        Ok((ret.into(), Ty::Bool))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block), fields(block.id = %block.id))]
    fn lower_block(
        &mut self,
        block: &Block,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        for (i, node) in block.body.iter().enumerate() {
            // We want to skip the last one in the loop so we can handle it outside the loop and use our Bind
            if i < block.body.len() - 1 {
                self.lower_node(node, instantiations)?;
            }
        }

        let (val, ty) = if let Some(node) = block.body.last() {
            self.lower_node_with_bind(node, instantiations, bind)?
        } else {
            (Value::Void, Ty::Void)
        };

        Ok((val, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs), fields(lhs.id = %lhs.id, rhs.id = %rhs.id))]
    fn lower_assignment(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let lvalue = self.lower_lvalue(lhs, instantiations)?;
        let (value, ty) = self.lower_expr(rhs, Bind::Fresh, instantiations)?;

        self.emit_lvalue_store(lvalue, value)?;

        Ok((Value::Void, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, receiver_ty))]
    fn emit_load_lvalue(&mut self, receiver_ty: &Ty, lvalue: &LValue) -> Result<Register, IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                // Variable is already in a register
                Ok(self.get_binding(sym))
            }
            LValue::Field { base, field, ty } => {
                // Recursively load base, then extract field
                let base_val = self.emit_load_lvalue(receiver_ty, base)?;
                let dest = self.next_register();

                self.push_instr(Instruction::GetField {
                    dest,
                    record: base_val,
                    field: self.field_index(receiver_ty, field),
                    ty: ty.clone(),
                    meta: vec![].into(),
                });

                Ok(dest)
            }
        }
    }

    fn emit_lvalue_store(&mut self, lvalue: LValue, value: Value) -> Result<(), IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                self.set_binding(&sym, value.as_register()?);
                Ok(())
            }
            LValue::Field {
                box base,
                field,
                ty: receiver_ty,
            } => {
                let base_val = self.emit_load_lvalue(&receiver_ty, &base)?;
                let dest = self.next_register();
                self.push_instr(Instruction::SetField {
                    dest,
                    record: base_val,
                    field: self.field_index(&receiver_ty, &field),
                    val: value,
                    ty: receiver_ty,
                    meta: vec![].into(),
                });

                self.emit_lvalue_store(base, dest.into())?;

                Ok(())
            }
        }
    }

    fn lower_lvalue(
        &mut self,
        expr: &Expr,
        instantiations: &Substitutions,
    ) -> Result<LValue, IRError> {
        match &expr.kind {
            ExprKind::Variable(name) => {
                Ok(LValue::Variable(name.symbol().expect("name not resolved")))
            }
            ExprKind::Member(Some(box receiver), label, _span) => {
                let receiver_lvalue = self.lower_lvalue(receiver, instantiations)?;
                let (receiver_ty, mut new_instantiations) =
                    self.specialized_ty(receiver).expect("didn't get base ty");
                new_instantiations.extend(instantiations.clone());

                let receiver_ty = substitute(receiver_ty, &new_instantiations);

                Ok(LValue::Field {
                    base: receiver_lvalue.into(),
                    ty: receiver_ty.clone(),
                    field: label.clone(),
                })
            }
            _ => Err(IRError::InvalidAssignmentTarget(format!("{expr:?}"))),
        }
    }

    // #[instrument(level = tracing::Level::TRACE, skip(self, pattern), fields(pattern.id = %pattern.id))]
    fn lower_pattern(&mut self, pattern: &Pattern) -> Result<Bind, IRError> {
        match &pattern.kind {
            PatternKind::Bind(name) => {
                let symbol = name.symbol().expect("name not resolved");
                let value = if self.asts[self.current_ast_id]
                    .phase
                    .is_captured
                    .contains(&symbol)
                {
                    let ty = self
                        .ty_from_symbol(&symbol)
                        .expect("did not get ty for sym");
                    let heap_addr = self.next_register();
                    self.push_instr(Instruction::Alloc {
                        dest: heap_addr,
                        ty,
                        count: 1.into(),
                    });
                    self.insert_binding(symbol, Binding::Pointer(heap_addr.into()));
                    Bind::Indirect(heap_addr, symbol)
                } else {
                    let val = self.next_register();

                    self.insert_binding(symbol, val.into());
                    Bind::Assigned(val)
                };

                Ok(value)
            }
            #[allow(clippy::todo)]
            PatternKind::LiteralInt(_) => todo!(),
            #[allow(clippy::todo)]
            PatternKind::LiteralFloat(_) => todo!(),
            #[allow(clippy::todo)]
            PatternKind::LiteralTrue => todo!(),
            #[allow(clippy::todo)]
            PatternKind::LiteralFalse => todo!(),
            #[allow(clippy::todo)]
            PatternKind::Tuple(..) => todo!(),
            PatternKind::Wildcard => Ok(Bind::Discard),
            #[allow(clippy::todo)]
            PatternKind::Variant { .. } => todo!(),
            #[allow(clippy::todo)]
            PatternKind::Record { .. } => todo!(),
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr), fields(expr.id = %expr.id))]
    fn lower_expr(
        &mut self,
        expr: &Expr,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (value, ty) = match &expr.kind {
            ExprKind::Func(func) => self.lower_func(func, bind, instantiations),
            ExprKind::LiteralArray(exprs) => self.lower_array(expr, exprs, bind, instantiations),
            ExprKind::LiteralInt(val) => {
                let ret = self.ret(bind);

                self.push_instr(Instruction::Constant {
                    dest: ret,
                    val: Value::Int(str::parse(val).map_err(|_| {
                        IRError::CouldNotParse(format!("Could not get int value from {val}"))
                    })?),
                    ty: Ty::Int,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok((ret.into(), Ty::Int))
            }
            ExprKind::LiteralFloat(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::Constant {
                    dest: ret,
                    val: Value::Float(str::parse(val).map_err(|_| {
                        IRError::CouldNotParse(format!("Could not get float value from {val}"))
                    })?),
                    ty: Ty::Float,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok((ret.into(), Ty::Float))
            }
            ExprKind::LiteralTrue => {
                if let Bind::Assigned(reg) = bind {
                    self.push_instr(Instruction::Constant {
                        dest: reg,
                        ty: Ty::Bool,
                        val: Value::Bool(true),
                        meta: vec![InstructionMeta::Source(expr.id)].into(),
                    });
                    Ok((reg.into(), Ty::Bool))
                } else {
                    Ok((Value::Bool(true), Ty::Bool))
                }
            }
            ExprKind::LiteralFalse => {
                if let Bind::Assigned(reg) = bind {
                    self.push_instr(Instruction::Constant {
                        dest: reg,
                        ty: Ty::Bool,
                        val: Value::Bool(false),
                        meta: vec![InstructionMeta::Source(expr.id)].into(),
                    });
                    Ok((reg.into(), Ty::Bool))
                } else {
                    Ok((Value::Bool(false), Ty::Bool))
                }
            }
            ExprKind::LiteralString(string) => {
                self.lower_string(expr, string, bind, instantiations)
            }
            ExprKind::Unary(..) => Ok((Value::Void, Ty::Void)), // Converted to calls earlier
            ExprKind::Binary(box lhs, op, box rhs) => {
                self.lower_binary(expr, lhs, op.clone(), rhs, bind, instantiations)
            }
            ExprKind::Tuple(items) => self.lower_tuple(expr.id, items, bind, instantiations),
            #[allow(clippy::todo)]
            ExprKind::Block(..) => todo!(),

            ExprKind::Call {
                callee:
                    box Expr {
                        kind:
                            ExprKind::Member(
                                Some(box Expr {
                                    kind:
                                        ExprKind::Constructor(
                                            name @ Name::Resolved(Symbol::Enum(..), ..),
                                        ),
                                    ..
                                }),
                                label,
                                ..,
                            ),
                        ..
                    },
                args,
                ..
            } => self.lower_enum_constructor(expr.id, name, label, args, bind, instantiations),

            ExprKind::Call {
                box callee, args, ..
            } => self.lower_call(expr, callee, args, bind, instantiations),

            ExprKind::Member(
                Some(box Expr {
                    kind: ExprKind::Constructor(name @ Name::Resolved(Symbol::Enum(..), ..)),
                    ..
                }),
                label,
                ..,
            ) => self.lower_enum_constructor(expr.id, name, label, &[], bind, instantiations),
            ExprKind::Member(member, label, ..) => {
                self.lower_member(expr.id, member, label, bind, instantiations)
            }

            ExprKind::Variable(name) => self.lower_variable(name, expr, instantiations),
            ExprKind::Constructor(name) => self.lower_constructor(name, expr, bind, instantiations),
            ExprKind::If(cond, conseq, alt) => {
                self.lower_if_expr(cond, conseq, alt, bind, instantiations)
            }
            ExprKind::Match(box scrutinee, arms) => {
                self.lower_match(scrutinee, arms, bind, instantiations)
            }
            ExprKind::RecordLiteral { fields, .. } => {
                self.lower_record_literal(expr, fields, bind, instantiations)
            }
            #[allow(clippy::todo)]
            ExprKind::RowVariable(..) => todo!(),
            ExprKind::As(lhs, ..) => self.lower_expr(lhs, bind, instantiations),
            ExprKind::InlineIR(instr) => self.lower_inline_ir(instr, bind, instantiations),
            _ => unreachable!("cannot lower expr: {expr:?}"),
        }?;

        // Quick check to make sure types are right
        #[cfg(feature = "verify_ir")]
        if let Ok(expected_ty) = self.ty_from_id(&expr.id) {
            assert_eq!(
                ty,
                expected_ty,
                "type mismatch {:?}",
                formatter::format_node(&expr.into(), &self.asts[expr.id.0.0 as usize].meta)
            );
        }

        Ok((value, ty))
    }

    #[allow(clippy::todo)]
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_inline_ir(
        &mut self,
        instr: &InlineIRInstruction,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let binds: Vec<_> = instr
            .binds
            .iter()
            .map(|b| self.lower_expr(b, Bind::Fresh, instantiations).map(|b| b.0))
            .try_collect()?;
        match &instr.kind {
            InlineIRInstructionKind::Constant { dest, ty, val } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id);
                let val = self.parsed_value(val, &binds);
                self.push_instr(Instruction::Constant {
                    dest,
                    ty: ty.clone(),
                    val,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Cmp {
                dest,
                lhs,
                rhs,
                ty,
                op,
            } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id);
                let lhs = self.parsed_value(lhs, &binds);
                let rhs = self.parsed_value(rhs, &binds);
                self.push_instr(Instruction::Cmp {
                    dest,
                    ty: ty.clone(),
                    lhs,
                    rhs,
                    op: op.clone().into(),
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Add { dest, ty, a, b }
            | InlineIRInstructionKind::Sub { dest, ty, a, b }
            | InlineIRInstructionKind::Mul { dest, ty, a, b }
            | InlineIRInstructionKind::Div { dest, ty, a, b } => {
                let ty = self.parsed_ty(ty, instr.id);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let a = self.parsed_value(a, &binds);
                let b = self.parsed_value(b, &binds);

                match &instr.kind {
                    InlineIRInstructionKind::Add { .. } => self.push_instr(Instruction::Add {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    InlineIRInstructionKind::Sub { .. } => self.push_instr(Instruction::Sub {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    InlineIRInstructionKind::Mul { .. } => self.push_instr(Instruction::Mul {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    InlineIRInstructionKind::Div { .. } => self.push_instr(Instruction::Div {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    _ => unreachable!(),
                }

                Ok((dest.into(), ty))
            }

            InlineIRInstructionKind::Ref { dest, ty, val } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id);
                let val = self.parsed_value(val, &binds);
                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val,
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Call {
                dest,
                ty,
                callee,
                args,
            } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id);
                let callee = self.parsed_value(callee, &binds);
                let args = args
                    .iter()
                    .map(|a| self.parsed_value(a, &binds))
                    .collect_vec()
                    .into();
                self.push_instr(Instruction::Call {
                    dest,
                    ty: ty.clone(),
                    callee,
                    args,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Record { dest, ty, record } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id);
                let record = record
                    .iter()
                    .map(|a| self.parsed_value(a, &binds))
                    .collect_vec()
                    .into();
                self.push_instr(Instruction::Record {
                    dest,
                    ty: ty.clone(),
                    record,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::GetField {
                dest,
                ty,
                record,
                field,
            } => {
                let ty = self.parsed_ty(ty, instr.id);
                let record = self.parsed_register(record, Register::DROP);
                let Value::Int(pos) = self.parsed_value(field, &binds) else {
                    unreachable!("field must be an int");
                };
                let field = Label::Positional(pos as usize);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record,
                    field,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::SetField {
                dest,
                val,
                ty,
                record,
                field,
            } => {
                let ty = self.parsed_ty(ty, instr.id);
                let val = self.parsed_value(val, &binds);
                let record = self.parsed_register(record, Register::DROP);
                let Value::Int(pos) = self.parsed_value(field, &binds) else {
                    unreachable!("field must be an int");
                };
                let field = Label::Positional(pos as usize);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::SetField {
                    dest,
                    val,
                    ty: ty.clone(),
                    record,
                    field: field.clone(),
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::_Print { val } => {
                let val = self.parsed_value(val, &binds);
                self.push_instr(Instruction::_Print { val });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Alloc { dest, ty, count } => {
                let ty = self.parsed_ty(ty, instr.id);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let count = self.parsed_value(count, &binds);
                self.push_instr(Instruction::Alloc {
                    dest,
                    ty: ty.clone(),
                    count,
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Free { addr } => {
                let addr = self.parsed_value(addr, &binds);
                self.push_instr(Instruction::Free { addr });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Load { dest, ty, addr } => {
                let ty = self.parsed_ty(ty, instr.id);
                let addr = self.parsed_value(addr, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::Load {
                    dest,
                    ty: ty.clone(),
                    addr,
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Store { value, ty, addr } => {
                let ty = self.parsed_ty(ty, instr.id);
                let value = self.parsed_value(value, &binds);
                let addr = self.parsed_value(addr, &binds);
                self.push_instr(Instruction::Store {
                    value,
                    ty: ty.clone(),
                    addr,
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Move { from, ty, to } => {
                let ty = self.parsed_ty(ty, instr.id);
                let from = self.parsed_value(from, &binds);
                let to = self.parsed_value(to, &binds);
                self.push_instr(Instruction::Move {
                    ty: ty.clone(),
                    from,
                    to,
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Copy {
                ty,
                from,
                to,
                length,
            } => {
                let ty = self.parsed_ty(ty, instr.id);
                let from = self.parsed_value(from, &binds);
                let to = self.parsed_value(to, &binds);
                let length = self.parsed_value(length, &binds);
                self.push_instr(Instruction::Copy {
                    ty: ty.clone(),
                    from,
                    to,
                    length,
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Gep {
                dest,
                ty,
                addr,
                offset_index,
            } => {
                let ty = self.parsed_ty(ty, instr.id);
                let addr = self.parsed_value(addr, &binds);
                let offset_index = self.parsed_value(offset_index, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::Gep {
                    dest,
                    ty: ty.clone(),
                    addr,
                    offset_index,
                });
                Ok((dest.into(), ty))
            }
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, items))]
    fn lower_array(
        &mut self,
        expr: &Expr,
        items: &[Expr],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let item_irs: Vec<(Value, Ty)> = items
            .iter()
            .map(|item| self.lower_expr(item, Bind::Fresh, instantiations))
            .try_collect()?;

        let (item_irs, item_tys): (Vec<Value>, Vec<Ty>) = item_irs.into_iter().unzip();
        let item_ty = if let Some(item) = items.first() {
            self.ty_from_id(&item.id)?
        } else {
            Ty::Void
        };

        let record_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: record_reg,
            ty: Ty::Tuple(item_tys.clone()), // This is sort of a hack, it's really a record but it's a pain to wrap a row and this still lowers to IrTy::Record
            record: item_irs.into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        let alloc_reg = self.next_register();
        self.push_instr(Instruction::Alloc {
            dest: alloc_reg,
            ty: Ty::Tuple(item_tys.clone()),
            count: Value::Int(1),
        });

        self.push_instr(Instruction::Store {
            value: record_reg.into(),
            ty: Ty::Tuple(item_tys),
            addr: alloc_reg.into(),
        });

        let dest = self.ret(bind);
        self.push_instr(Instruction::Nominal {
            dest,
            sym: Symbol::Array,
            ty: Ty::Array(item_ty.clone()),
            record: vec![
                alloc_reg.into(),
                Value::Int(items.len() as i64),
                Value::Int(items.len() as i64),
            ]
            .into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        Ok((dest.into(), Ty::Array(item_ty)))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, items))]
    fn lower_tuple(
        &mut self,
        id: NodeID,
        items: &[Expr],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let item_irs: Vec<(Value, Ty)> = items
            .iter()
            .map(|expr| self.lower_expr(expr, Bind::Fresh, instantiations))
            .try_collect()?;

        let (item_irs, item_tys): (Vec<Value>, Vec<Ty>) = item_irs.into_iter().unzip();
        let ty = Ty::Tuple(item_tys);
        let dest = self.ret(bind);
        self.push_instr(Instruction::Record {
            dest,
            ty: ty.clone(),
            record: item_irs.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_string(
        &mut self,
        expr: &Expr,
        string: &String,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ret = self.ret(bind);
        let bytes = string.bytes().collect_vec();
        let bytes_len = bytes.len() as i64;
        let ptr = self.static_memory.write(Value::RawBuffer(bytes));

        self.push_instr(Instruction::Nominal {
            dest: ret,
            sym: Symbol::String,
            ty: Ty::String(),
            record: vec![
                Value::RawPtr(Addr(ptr)),
                Value::Int(bytes_len),
                Value::Int(bytes_len),
            ]
            .into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        Ok((ret.into(), Ty::String()))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let result_type = {
            let first_arm_expr_id = arms[0].body.id;
            self.ty_from_id(&first_arm_expr_id)?
        };

        let result_register = self.ret(bind);

        let (scrutinee_value, _scrutinee_type) =
            self.lower_expr(scrutinee, Bind::Fresh, instantiations)?;
        let scrutinee_register = scrutinee_value.as_register()?;

        let join_block_id = self.new_basic_block();

        let mut arm_block_ids = Vec::with_capacity(arms.len());
        let mut arm_result_registers = Vec::with_capacity(arms.len());

        for arm in arms {
            let arm_block_id = self.new_basic_block();
            arm_block_ids.push(arm_block_id);

            self.in_basic_block(arm_block_id, |lowerer| {
                let (arm_value, _arm_type) =
                    lowerer.lower_block(&arm.body, Bind::Fresh, instantiations)?;
                let arm_register = arm_value.as_register()?;
                arm_result_registers.push(arm_register);

                lowerer.push_terminator(Terminator::Jump { to: join_block_id });
                Ok(())
            })?;
        }

        // 3. Build the dispatch chain from the block that computed the scrutinee.
        self.build_match_dispatch(scrutinee, scrutinee_register.into(), arms, &arm_block_ids)?;

        // 4. Join block φ (if match produces a value).
        self.set_current_block(join_block_id);

        self.push_phi(Phi {
            dest: result_register,
            ty: result_type.clone(),
            sources: arm_block_ids
                .into_iter()
                .zip(arm_result_registers.into_iter())
                .map(|a| a.into())
                .collect::<Vec<PhiSource>>()
                .into(),
        });

        Ok((Value::Reg(result_register.0), result_type))
    }

    fn build_match_dispatch(
        &mut self,
        scrutinee_expr: &Expr,
        scrutinee_value: Value,
        arms: &[MatchArm],
        arm_block_ids: &[BasicBlockId],
    ) -> Result<(), IRError> {
        assert_eq!(
            arms.len(),
            arm_block_ids.len(),
            "arms and arm blocks must match"
        );

        // Type of scrutinee; used for the Cmp instruction.
        let scrutinee_type = self.ty_from_id(&scrutinee_expr.id)?;

        // Start dispatch from the block where the scrutinee was just computed.
        let current_function = self
            .current_function_stack
            .last()
            .expect("did not get current function");
        let current_block_index = *current_function
            .current_block_idx
            .last()
            .expect("did not get current block index");
        let mut current_test_block_id = current_function.blocks[current_block_index].id;

        for arm_index in 0..arms.len() {
            let arm = &arms[arm_index];
            let arm_block_id = arm_block_ids[arm_index];

            // If the pattern is Bind or Wildcard, this is a catch-all from here on.
            match &arm.pattern.kind {
                PatternKind::Bind(..) | PatternKind::Wildcard => {
                    self.set_current_block(current_test_block_id);
                    self.push_terminator(Terminator::Jump { to: arm_block_id });
                    return Ok(());
                }
                _ => {}
            }

            // Last arm: treat it as default (type checker should have enforced
            // exhaustiveness or complained earlier).
            if arm_index == arms.len() - 1 {
                self.set_current_block(current_test_block_id);
                self.push_terminator(Terminator::Jump { to: arm_block_id });
                break;
            }

            // For non-last arms, we emit: Cmp then Branch.
            self.set_current_block(current_test_block_id);

            let (pattern_value, _pattern_type) = self.lower_pattern_literal_value(&arm.pattern)?;

            let condition_register = self.next_register();
            self.push_instr(Instruction::Cmp {
                dest: condition_register,
                lhs: scrutinee_value.clone(),
                rhs: pattern_value,
                ty: scrutinee_type.clone(),
                op: CmpOperator::Equals,
                meta: vec![InstructionMeta::Source(arm.pattern.id)].into(),
            });

            let next_test_block_id = self.new_basic_block();

            self.push_terminator(Terminator::Branch {
                cond: Value::Reg(condition_register.0),
                conseq: arm_block_id,
                alt: next_test_block_id,
            });

            // Next iteration will emit into the fallthrough test block.
            current_test_block_id = next_test_block_id;
        }

        Ok(())
    }

    fn lower_pattern_literal_value(&mut self, pattern: &Pattern) -> Result<(Value, Ty), IRError> {
        match &pattern.kind {
            PatternKind::LiteralInt(text) => {
                let parsed = text.parse::<i64>().map_err(|error| {
                    IRError::InvalidAssignmentTarget(format!(
                        "invalid integer literal in match pattern: {text} ({error})"
                    ))
                })?;
                Ok((Value::Int(parsed), Ty::Int))
            }

            PatternKind::LiteralFloat(text) => {
                let parsed = text.parse::<f64>().map_err(|error| {
                    IRError::InvalidAssignmentTarget(format!(
                        "invalid float literal in match pattern: {text} ({error})"
                    ))
                })?;
                Ok((Value::Float(parsed), Ty::Float))
            }

            PatternKind::LiteralTrue => Ok((Value::Bool(true), Ty::Bool)),
            PatternKind::LiteralFalse => Ok((Value::Bool(false), Ty::Bool)),

            PatternKind::Bind(..) | PatternKind::Wildcard => {
                // These are handled earlier in build_match_dispatch as defaults.
                unreachable!("Bind and Wildcard should not reach lower_pattern_literal_value")
            }

            // Everything else will need a more sophisticated scheme:
            // - Variant: compare enum tag, then destructure fields in the arm
            // - Tuple / Record / Struct: recursive structural matching
            // For now, make it explicit that these are not lowered here.
            other => Err(IRError::InvalidAssignmentTarget(format!(
                "pattern kind not yet supported in match dispatch lowering: {other:?}"
            ))),
        }
    }

    fn lower_record_literal(
        &mut self,
        expr: &Expr,
        fields: &[RecordField],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let mut field_vals = vec![];
        let mut field_row = Row::Empty(TypeDefKind::Struct);
        for field in fields.iter() {
            let (val, ty) = self.lower_expr(&field.value, Bind::Fresh, instantiations)?;
            field_vals.push(val);
            field_row = Row::Extend {
                row: field_row.into(),
                label: field.label.name_str().into(),
                ty,
            };
        }

        let dest = self.ret(bind);

        // Check if this record literal is typed as a nominal struct
        if let Ok(Ty::Nominal { symbol, .. }) = self.ty_from_id(&expr.id) {
            let ty = Ty::Record(Some(symbol), field_row.into());
            self.push_instr(Instruction::Nominal {
                dest,
                sym: symbol,
                ty: ty.clone(),
                record: field_vals.into(),
                meta: vec![InstructionMeta::Source(expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        }

        let ty = Ty::Record(None, field_row.into());
        self.push_instr(Instruction::Record {
            dest,
            ty: ty.clone(),
            record: field_vals.into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_constructor(
        &mut self,
        name: &Name,
        expr: &Expr,
        bind: Bind,
        old_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let constructor_sym = *self
            .types
            .catalog
            .initializers
            .get(&name.symbol().expect("name not resolved"))
            .expect("did not get init")
            .get(&Label::Named("init".into()))
            .expect("did not get init");

        let init_entry = self
            .types
            .get_symbol(&constructor_sym)
            .cloned()
            .expect("did not get init entry");
        let (ty, mut instantiations) = self.specialize(&init_entry, expr.id)?;
        instantiations.ty.extend(old_instantiations.ty.clone());
        instantiations.row.extend(old_instantiations.row.clone());

        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty: ty.clone(),
            val: Value::Func(constructor_sym),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_enum_constructor(
        &mut self,
        id: NodeID,
        name: &Name,
        variant_name: &Label,
        values: &[CallArg],
        bind: Bind,
        old_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let enum_symbol = name.symbol().expect("name not resolved");
        let constructor_sym = *self
            .types
            .catalog
            .variants
            .get(&enum_symbol)
            .unwrap_or_else(|| panic!("did not get variants for {enum_symbol:?}"))
            .get(variant_name)
            .unwrap_or_else(|| panic!("didn't get {:?}", name));

        let tag = self
            .types
            .catalog
            .variants
            .get(&enum_symbol)
            .unwrap_or_else(|| panic!("did not get variants for {enum_symbol:?}"))
            .get_index_of(variant_name)
            .unwrap_or_else(|| panic!("did not get tag for {enum_symbol:?} {variant_name:?}"));

        let enum_entry = self
            .types
            .get_symbol(&enum_symbol)
            .unwrap_or_else(|| panic!("did not get enum entry {enum_symbol:?}"))
            .clone();
        let (_, _ty_instantiations) = self.specialize(&enum_entry, id)?;
        let init_entry = self
            .types
            .get_symbol(&constructor_sym)
            .cloned()
            .expect("did not get enum constructor entry");
        let (_, mut instantiations) = self.specialize(&init_entry, id)?;
        instantiations.extend(old_instantiations.clone());

        let mut args: Vec<Value> = Default::default();
        let mut args_tys: Vec<Ty> = vec![Ty::Int];
        for value in values.iter() {
            let (val, ty) = self.lower_expr(&value.value, Bind::Fresh, &instantiations)?;
            args.push(val);
            args_tys.push(ty);
        }

        // Set the tag as the first entry
        args.insert(0, Value::Int(tag as i64));

        let row =
            args_tys
                .iter()
                .enumerate()
                .fold(Row::Empty(TypeDefKind::Enum), |acc, (i, ty)| Row::Extend {
                    row: acc.into(),
                    label: Label::Positional(i),
                    ty: ty.clone(),
                });

        let ty = Ty::Record(Some(enum_symbol), row.into());
        let dest = self.ret(bind);
        self.push_instr(Instruction::Nominal {
            sym: enum_symbol,
            dest,
            ty: ty.clone(),
            record: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, receiver))]
    #[allow(clippy::todo)]
    fn lower_member(
        &mut self,
        id: NodeID,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        if let Some(box receiver) = &receiver {
            let reg = self.next_register();
            let member_bind = Bind::Assigned(reg);
            let (receiver_val, _) = self.lower_expr(receiver, member_bind, instantiations)?;
            let ty = self.ty_from_id(&id)?;
            let dest = self.ret(bind);

            let (receiver_ty, _) = self.specialized_ty(receiver)?;

            if let Ty::Nominal { symbol, .. } = &receiver_ty
                && let Some(methods) = self.types.catalog.instance_methods.get(symbol)
                && let Some(method) = methods.get(label).cloned()
            {
                tracing::debug!("lowering method: {label} {method:?}");
                self.check_import(&method);

                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val: Value::Func(method),
                });
            } else if let Some(witness) = self.witness_for(&id, label).copied()
                && matches!(witness, Symbol::InstanceMethod(..))
            {
                tracing::debug!("lowering req {label} {witness:?}");
                self.check_import(&witness);
                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val: Value::Func(witness),
                });
            } else {
                let label = self.field_index(&receiver_ty, label);
                tracing::debug!("lowering field {label}");
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record: receiver_val.as_register()?,
                    field: label,
                    meta: vec![InstructionMeta::Source(id)].into(),
                });
            };

            Ok((dest.into(), ty))
        } else {
            todo!("gotta handle unqualified lookups")
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_variable(
        &mut self,
        name: &Name,
        expr: &Expr,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (ty, instantiations) = self.specialized_ty(expr)?;
        let monomorphized_ty = substitute(ty.clone(), &instantiations);

        let original_name_sym = name.symbol().expect("did not get symbol");

        // If we currently have a binding for this symbol, prefer that over just passing names around
        if self
            .current_func_mut()
            .bindings
            .contains_key(&original_name_sym)
        {
            return Ok((self.get_binding(&original_name_sym).into(), ty));
        }

        let ret = if matches!(monomorphized_ty, Ty::Func(..)) {
            // It's a func reference so we pass the name
            // let monomorphized_name = self
            //     .monomorphize_name(name.clone(), &instantiations)
            //     .symbol()
            //     .expect("did not get symbol");
            // Value::Func(monomorphized_name)

            let monomorphized_name = self
                .monomorphize_name(name.clone(), &instantiations)
                .symbol()
                .expect("did not get symbol");

            // Check if this function has captures
            if let Some(captures) = self.asts[self.current_ast_id]
                .phase
                .captures
                .get(&name.symbol().expect("did not get symbol"))
                .cloned()
                && !captures.is_empty()
            {
                let env: Vec<Value> = captures
                    .iter()
                    .map(
                        |cap| match self.current_func_mut().bindings.get(&cap.symbol).cloned() {
                            Some(Binding::Pointer(addr)) => addr,
                            Some(Binding::Register(reg)) => Value::Reg(reg),
                            Some(Binding::Capture { index, ty }) => {
                                let dest = self.next_register();
                                self.push_instr(Instruction::GetField {
                                    dest,
                                    ty,
                                    record: Register(0),
                                    field: Label::Positional(index),
                                    meta: vec![].into(),
                                });
                                dest.into()
                            }
                            other => panic!("unexpected binding for capture: {other:?}"),
                        },
                    )
                    .collect();
                Value::Closure {
                    func: monomorphized_name,
                    env: env.into(),
                }
            } else {
                Value::Func(monomorphized_name)
            }
        } else {
            Value::Reg(
                self.get_binding(&name.symbol().expect("name not resolved"))
                    .0,
            )
        };

        Ok((ret, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    #[allow(clippy::too_many_arguments)]
    fn lower_constructor_call(
        &mut self,
        id: NodeID,
        name: &Name,
        callee: &Expr,
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let record_dest = self.next_register();

        // Look up the initializer and specialize it using the already-computed instantiations
        let init_sym = *self
            .types
            .catalog
            .initializers
            .get(&name.symbol().expect("name not resolved"))
            .unwrap_or_else(|| panic!("did not get initializers for {name:?}"))
            .get(&Label::Named("init".into()))
            .expect("did not get init");

        let init_entry = self
            .types
            .get_symbol(&init_sym)
            .cloned()
            .expect("did not get init entry");
        let (init_ty, concrete_tys) = self.specialize(&init_entry, callee.id)?;

        let properties = self
            .types
            .catalog
            .properties
            .get(&name.symbol().expect("name not resolved"))
            .expect("did not get properties");

        // Extract return type from the initializer function
        let mut params = init_ty.clone().uncurry_params();
        let ret = params.pop().expect("did not get init ret");

        self.push_instr(Instruction::Nominal {
            sym: name.symbol().expect("did nto get nominal sym"),
            dest: record_dest,
            ty: ret.clone(),
            record: properties
                .iter()
                .map(|_| Value::Uninit)
                .collect::<Vec<_>>()
                .into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });
        args.insert(0, record_dest.into());

        let init = self.monomorphize_name(
            Name::Resolved(init_sym, format!("{}_init", name)),
            &concrete_tys,
        );

        self.push_instr(Instruction::Call {
            dest,
            ty: ret.clone(),
            callee: Value::Func(init.symbol().expect("did not get symbol")),
            args: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ret))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, call_expr, callee, args, parent_instantiations))]
    fn lower_call(
        &mut self,
        call_expr: &Expr,
        callee: &Expr,
        args: &[CallArg],
        bind: Bind,
        parent_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let dest = self.ret(bind);

        // Handle embedded IR call
        if let ExprKind::Variable(name) = &callee.kind
            && name.symbol().expect("name not resolved") == Symbol::IR
        {
            return self.lower_embedded_ir_call(call_expr.id, args, dest, parent_instantiations);
        }

        if let ExprKind::Variable(name) = &callee.kind
            && name.symbol().expect("name not resolved") == Symbol::PRINT
        {
            let arg =
                self.lower_expr(&args[0].value, Bind::Assigned(dest), parent_instantiations)?;
            self.push_instr(Instruction::_Print { val: arg.0 });
            return Ok((Value::Void, Ty::Void));
        }

        let (_callee_ty, mut instantiations) = self
            .specialized_ty(callee)
            .expect("did not get specialized ty for callee");
        instantiations.extend(parent_instantiations.clone());

        let ty = self.ty_from_id(&call_expr.id)?;
        let mut arg_vals = vec![];
        let mut arg_tys = vec![];
        for arg in args {
            let (arg, arg_ty) = self.lower_expr(&arg.value, Bind::Fresh, &instantiations)?;
            arg_vals.push(arg);
            arg_tys.push(arg_ty)
        }

        if let ExprKind::Constructor(name) = &callee.kind {
            return self.lower_constructor_call(
                call_expr.id,
                name,
                callee,
                arg_vals,
                dest,
                &instantiations,
            );
        }

        if let ExprKind::Member(Some(box receiver), member, ..) = &callee.kind {
            return self.lower_method_call(
                call_expr,
                callee,
                receiver.clone(),
                member,
                args,
                arg_vals,
                dest,
                &instantiations,
            );
        }

        let callee_ir = self.lower_expr(callee, Bind::Fresh, &instantiations)?.0;

        self.push_instr(Instruction::Call {
            dest,
            ty: ty.clone(),
            callee: callee_ir,
            args: arg_vals.into(),
            meta: vec![InstructionMeta::Source(call_expr.id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(level = tracing::Level::TRACE, skip(self, call_expr, callee_expr, receiver, arg_exprs, args, instantiations ))]
    fn lower_method_call(
        &mut self,
        call_expr: &Expr,
        callee_expr: &Expr,
        mut receiver: Expr,
        label: &Label,
        arg_exprs: &[CallArg],
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_id(&call_expr.id)?;

        // Capture protocol ID before we replace receiver (for witness specialization)
        let protocol_id = match &receiver.kind {
            ExprKind::Constructor(Name::Resolved(Symbol::Protocol(id), _)) => Some(*id),
            _ => None,
        };

        // Is this an instance method call on a constructor? If so we don't need
        // to prepend a self arg because it's passed explicitly (like Foo.bar(fizz) where
        // fizz == self)
        if let ExprKind::Constructor(_name) = &receiver.kind {
            receiver = arg_exprs[0].value.clone();
        } else {
            let (receiver_ir, _) = self.lower_expr(&receiver, Bind::Fresh, instantiations)?;
            args.insert(0, receiver_ir);
        }

        if let Some(method_sym) = self.lookup_instance_method(&receiver, label)? {
            self.check_import(&method_sym);
            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: Value::Func(method_sym),
                args: args.into(),
                meta: vec![InstructionMeta::Source(call_expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        };

        if let Some(witness) = self.witness_for(&callee_expr.id, label).copied() {
            self.check_import(&witness);
            // Try to specialize for conformance if this is a protocol method call
            let specialized = 'specialize: {
                let Some(..) = protocol_id else {
                    tracing::trace!("no protocol_id");
                    break 'specialize None;
                };
                let Ok(receiver_ty) = self.ty_from_id(&receiver.id) else {
                    tracing::trace!("couldn't get receiver ty");
                    break 'specialize None;
                };

                let conforming_id = match &receiver_ty {
                    Ty::Primitive(sym) => *sym,
                    Ty::Nominal { symbol, .. } => *symbol,
                    _ => {
                        tracing::trace!("receiver ty not primitive/nominal: {receiver_ty:?}");
                        break 'specialize None;
                    }
                };

                // Build witness substitutions from ALL conformances for this type
                // (needed because protocols can extend other protocols, e.g. Comparable: Equatable)
                let mut subs = Substitutions::default();

                // Collect all conformances for this type from local and modules
                let all_conformances: Vec<_> = self
                    .types
                    .catalog
                    .conformances
                    .values()
                    .filter(|c| c.conforming_id == conforming_id)
                    .cloned()
                    .chain(
                        self.config
                            .modules
                            .modules
                            .values()
                            .flat_map(|m| m.types.catalog.conformances.values())
                            .filter(|c| c.conforming_id == conforming_id)
                            .cloned(),
                    )
                    .collect();

                for conformance in &all_conformances {
                    for (method_label, impl_symbol) in &conformance.witnesses {
                        let conf_protocol = conformance.protocol_id;
                        // Check local method requirements
                        if let Some(req_methods) = self
                            .types
                            .catalog
                            .method_requirements
                            .get(&Symbol::Protocol(conf_protocol))
                            && let Some(req_symbol) = req_methods.get(method_label)
                        {
                            subs.witnesses.insert(*req_symbol, *impl_symbol);
                            self.check_import(impl_symbol);
                        }
                        // Check module method requirements
                        for module in self.config.modules.modules.values() {
                            if let Some(req_methods) = module
                                .types
                                .catalog
                                .method_requirements
                                .get(&Symbol::Protocol(conf_protocol))
                                && let Some(req_symbol) = req_methods.get(method_label)
                            {
                                subs.witnesses.insert(*req_symbol, *impl_symbol);
                                self.check_import(impl_symbol);
                            }
                        }
                    }
                }

                tracing::trace!("witness subs: {:?}", subs.witnesses);
                if subs.witnesses.is_empty() {
                    break 'specialize None;
                }

                let name = Name::Resolved(witness, label.to_string());
                let specialized_name = self.monomorphize_name(name, &subs);
                tracing::trace!("specialized to: {specialized_name:?}");
                Some(specialized_name)
            };

            let callee = specialized.unwrap_or_else(|| Name::Resolved(witness, label.to_string()));

            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: Value::Func(callee.symbol().expect("did not get symbol")),
                args: args.into(),
                meta: vec![InstructionMeta::Source(call_expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        }

        Err(IRError::TypeNotFound(format!(
            "No witness found for {:?} in {:?} ({:?}).",
            label,
            receiver,
            self.ty_from_id(&receiver.id)
        )))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func.name = %func.name))]
    fn lower_func(
        &mut self,
        func: &Func,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_symbol(&func.name.symbol().expect("name not resolved"))?;

        let (mut param_tys, mut ret_ty) = uncurry_function(ty);

        // Do we have captures? If so this is a closure
        let capture_env = if let Some(captures) = self.asts[self.current_ast_id]
            .phase
            .captures
            .get(&func.name.symbol().expect("didn't get sym"))
            .cloned()
            && !captures.is_empty()
        {
            let mut env_fields = vec![];
            for capture in captures.clone() {
                let ty = self
                    .ty_from_symbol(&capture.symbol)
                    .expect("didn't get capture ty")
                    .clone();

                let val = match self
                    .current_func_mut()
                    .bindings
                    .get(&capture.symbol)
                    .cloned()
                {
                    Some(Binding::Pointer(val)) => val,
                    Some(Binding::Capture { index, .. }) => {
                        // Captured from outer closure's env - emit getfield
                        let dest = self.next_register();
                        self.push_instr(Instruction::GetField {
                            dest,
                            ty: Ty::RawPtr,
                            record: 0.into(), // env is always %0
                            field: Label::Positional(index),
                            meta: vec![].into(),
                        });
                        Value::Reg(dest.0)
                    }
                    other => unreachable!("unexpected binding for capture: {other:?}"),
                };

                env_fields.push((capture.symbol, ty.clone(), val));
            }

            Some(env_fields)
        } else {
            None
        };

        let _s = tracing::trace_span!("pushing new current function");
        self.current_function_stack.push(CurrentFunction::default());

        let mut params = vec![];

        if let Some(env_fields) = capture_env.clone() {
            for (i, (binding, ty, ..)) in env_fields.iter().enumerate() {
                self.insert_binding(
                    *binding,
                    Binding::Capture {
                        index: i,
                        ty: ty.clone(),
                    },
                );
            }

            // Allocate env as %0
            let env_reg = self.next_register();
            params.push(Value::Reg(env_reg.0));
            param_tys.insert(
                0,
                Ty::Record(
                    None,
                    env_fields
                        .iter()
                        .enumerate()
                        .fold(Row::Empty(TypeDefKind::Struct), |row, (i, _)| Row::Extend {
                            row: row.into(),
                            label: Label::Positional(i),
                            ty: Ty::RawPtr,
                        })
                        .into(),
                ),
            );
        }

        for param in func.params.iter() {
            let register = self.next_register();
            params.push(Value::Reg(register.0));
            self.insert_binding(
                param.name.symbol().expect("name not resolved"),
                register.into(),
            );
        }

        let mut ret = Value::Void;
        for node in func.body.body.iter() {
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
        }

        if ret == Value::Poison {
            self.push_terminator(Terminator::Unreachable);
        } else {
            self.push_terminator(Terminator::Ret {
                val: ret,
                ty: ret_ty.clone(),
            });
        }

        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");
        drop(_s);

        let func_ty = curry_ty(param_tys.iter(), ret_ty);
        self.functions.insert(
            func.name.symbol().expect("name not resolved"),
            PolyFunction {
                name: func.name.clone(),
                params,
                blocks: current_function.blocks,
                ty: func_ty.clone(),
                register_count: (current_function.registers.next) as usize,
            },
        );

        let func_sym = func.name.symbol().expect("did not get symbol");
        let func_val = if let Some(env) = capture_env {
            Value::Closure {
                func: func_sym,
                env: env.into_iter().map(|e| e.2.clone()).collect_vec().into(),
            }
        } else {
            Value::Func(func_sym)
        };

        if bind != Bind::Discard {
            let dest = self.ret(bind);
            self.push_instr(Instruction::Ref {
                dest,
                ty: func_ty.clone(),
                val: func_val.clone(),
            });
        }

        Ok((func_val, func_ty))
    }

    fn lower_embedded_ir_call(
        &mut self,
        id: NodeID,
        args: &[CallArg],
        dest: Register,
        parent_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ExprKind::LiteralString(string) = &args[0].value.kind else {
            unreachable!()
        };

        let mut string = string.clone();

        // Replace $? with destination register
        if string.contains("$?") {
            string = string.replace("$?", &format!("%{}", dest.0));
        }

        // Lower additional arguments and substitute $1, $2, $3, etc.
        for (i, arg) in args.iter().skip(1).enumerate() {
            let placeholder = format!("${}", i + 1);
            if string.contains(&placeholder) {
                let (val, _ty) = self.lower_expr(&arg.value, Bind::Fresh, parent_instantiations)?;
                string = string.replace(&placeholder, &val.to_string());
            }
        }

        self.push_instr(parse_instruction::<IrTy>(&string).into());

        let ty = self.ty_from_id(&id)?;

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_instr(&mut self, instruction: Instruction<Ty>) {
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let current_block_idx = current_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");
        current_function.blocks[*current_block_idx]
            .instructions
            .push(instruction);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_phi(&mut self, phi: Phi<Ty>) {
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let current_block_idx = current_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");
        current_function.blocks[*current_block_idx].phis.push(phi);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn new_basic_block(&mut self) -> BasicBlockId {
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let id = BasicBlockId(current_function.blocks.len() as u32);
        let new_block = BasicBlock {
            id,
            phis: Default::default(),
            instructions: Default::default(),
            terminator: Terminator::Unreachable,
        };
        current_function.blocks.push(new_block);
        id
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn get_current_block(&mut self) -> BasicBlockId {
        BasicBlockId(
            self.current_function_stack
                .last_mut()
                .expect("didn't get current func")
                .current_block_idx
                .last()
                .copied()
                .expect("didnt get current block id") as u32,
        )
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn set_current_block(&mut self, id: BasicBlockId) {
        self.current_function_stack
            .last_mut()
            .expect("didn't get current func")
            .current_block_idx
            .push(id.0 as usize);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, f))]
    fn in_basic_block<T>(
        &mut self,
        id: BasicBlockId,
        f: impl FnOnce(&mut Lowerer<'a>) -> Result<T, IRError>,
    ) -> Result<T, IRError> {
        self.current_function_stack
            .last_mut()
            .expect("didn't get current func")
            .current_block_idx
            .push(id.0 as usize);
        let ret = f(self);
        self.current_function_stack
            .last_mut()
            .expect("didn't get current func")
            .current_block_idx
            .pop();
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let current_block_idx = current_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");

        let block = &mut current_function.blocks[*current_block_idx];
        // Don't override an existing terminator (e.g., from an early return)
        if block.terminator != Terminator::Unreachable {
            return;
        }
        block.terminator = terminator;
    }

    fn insert_binding(&mut self, symbol: Symbol, binding: Binding<Ty>) {
        self.current_func_mut().bindings.insert(symbol, binding);
    }

    fn get_binding(&mut self, symbol: &Symbol) -> Register {
        let binding = self
            .current_func_mut()
            .bindings
            .get(symbol)
            .cloned()
            .unwrap_or_else(|| panic!("did not get binding for {symbol:?}"));
        let ty = self
            .types
            .get_symbol(symbol)
            .unwrap_or_else(|| panic!("did not get ty for {symbol:?}"))
            .as_mono_ty()
            .clone();

        match binding {
            Binding::Register(reg) => Register(reg),
            Binding::Capture { index, ty } => {
                let ptr = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest: ptr,
                    ty: Ty::RawPtr,
                    record: 0.into(),
                    field: Label::Positional(index),
                    meta: vec![].into(),
                });
                let dest = self.next_register();
                self.push_instr(Instruction::Load {
                    dest,
                    ty,
                    addr: ptr.into(),
                });
                dest
            }
            Binding::Pointer(addr) => {
                let dest = self.next_register();
                self.push_instr(Instruction::Load { dest, ty, addr });
                dest
            }
        }
    }

    fn set_binding(&mut self, symbol: &Symbol, value_register: Register) {
        let ty = self
            .types
            .get_symbol(symbol)
            .expect("did not get ty for {symbol:?}")
            .as_mono_ty()
            .clone();

        let binding = self
            .current_func_mut()
            .bindings
            .get(symbol)
            .cloned()
            .expect("did not get binding");

        match binding {
            Binding::Register(..) => {
                self.current_func_mut()
                    .bindings
                    .insert(*symbol, value_register.into());
            }
            Binding::Capture { index, ty } => {
                let dest = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: Ty::RawPtr,
                    record: Register(0),
                    field: Label::Positional(index),
                    meta: vec![].into(),
                });

                self.push_instr(Instruction::Store {
                    value: value_register.into(),
                    ty,
                    addr: dest.into(),
                });
            }
            Binding::Pointer(addr) => {
                self.push_instr(Instruction::Store {
                    value: value_register.into(),
                    ty,
                    addr: addr.clone(),
                });
            }
        }
    }

    fn current_func_mut(&mut self) -> &mut CurrentFunction {
        self.current_function_stack
            .last_mut()
            .expect("didn't get current function")
    }

    fn next_register(&mut self) -> Register {
        let register = self.current_func_mut().registers.next();
        tracing::trace!("allocated register: {register}");
        register
    }

    fn ret(&mut self, bind: Bind) -> Register {
        match bind {
            Bind::Assigned(value) => value,
            Bind::Fresh => self.next_register(),
            Bind::Discard => Register::DROP,
            Bind::Indirect(reg, sym) => {
                let ty = self.ty_from_symbol(&sym).expect("did not get ty for bind");
                let value = self.next_register();
                self.push_instr(Instruction::Store {
                    value: value.into(),
                    ty,
                    addr: reg.into(),
                });
                value
            }
        }
    }

    /// Check to see if this symbol calls any symbols we don't have
    fn check_import(&mut self, symbol: &Symbol) {
        if self.config.module_id == ModuleId::Core {
            // No imports can happen from core.
            return;
        }

        let module_id = match symbol {
            Symbol::InstanceMethod(InstanceMethodId { module_id, .. }) => Some(*module_id),
            Symbol::StaticMethod(StaticMethodId { module_id, .. }) => Some(*module_id),
            Symbol::Initializer(InitializerId { module_id, .. }) => Some(*module_id),
            Symbol::Global(GlobalId { module_id, .. }) => Some(*module_id),
            Symbol::Synthesized(SynthesizedId { module_id, .. }) => Some(*module_id),
            _ => None,
        };

        let Some(module_id) = module_id else {
            return;
        };

        let func = if module_id == self.config.module_id {
            let Some(func) = self.functions.get(symbol) else {
                return;
            };

            func
        } else {
            let module = self
                .config
                .modules
                .modules
                .get(&module_id)
                .expect("didn't get module for import");

            tracing::debug!("importing {symbol:?} from {module_id}");

            // TODO: This won't work with external methods yet, only core works.
            let Some(method_func) = module.program.polyfunctions.get(symbol) else {
                return;
            };
            self.functions.insert(*symbol, method_func.clone());
            method_func
        };

        // Recursively import any functions this function calls
        let callees: Vec<Symbol> = func
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instr| {
                if let Instruction::Call {
                    callee:
                        Value::Func(sym)
                        | Value::Ref(Reference::Func(sym))
                        | Value::Ref(Reference::Closure(sym, ..)),
                    ..
                } = instr
                {
                    Some(*sym)
                } else {
                    None
                }
            })
            .collect();

        for callee_sym in callees {
            // Already imported, avoid infinite recursion
            if self.functions.contains_key(&callee_sym) {
                continue;
            }
            self.check_import(&callee_sym);
        }
    }

    fn monomorphize_name(&mut self, name: Name, instantiations: &Substitutions) -> Name {
        if instantiations.ty.is_empty() && instantiations.witnesses.is_empty() {
            return name;
        }

        let new_symbol = self.symbols.next_synthesized(self.config.module_id);
        self.asts[self.current_ast_id]
            .phase
            .symbols_to_string
            .insert(new_symbol.into(), name.name_str());
        let ty_parts: Vec<String> = instantiations.ty.values().map(|v| format!("{v}")).collect();
        let witness_parts: Vec<String> = instantiations
            .witnesses
            .values()
            .map(|v| format!("{v}"))
            .collect();
        let all_parts: Vec<String> = ty_parts.into_iter().chain(witness_parts).collect();
        let new_name_str = format!("{}[{}]", name, all_parts.join(", "));

        let new_name = Name::Resolved(new_symbol.into(), new_name_str);

        tracing::trace!("monomorphized {name:?} -> {new_name:?}");

        self.specializations
            .entry(name.symbol().expect("name not resolved"))
            .or_default()
            .push(Specialization {
                name: new_name.clone(),
                substitutions: instantiations.clone(),
            });

        new_name
    }

    fn parsed_ty(&mut self, ty: &TypeAnnotation, id: NodeID) -> Ty {
        let entry = self
            .types
            .types_by_symbol
            .get(&ty.symbol().expect("did not get ty symbol"))
            .cloned()
            .expect("did not get entry");
        let (ty, _) = self
            .specialize(&entry, id)
            .expect("unable to specialize ty");
        ty
    }

    fn parsed_register(
        &self,
        reg: &crate::node_kinds::inline_ir_instruction::Register,
        dest: Register,
    ) -> Register {
        if reg.0 == "?" {
            dest
        } else {
            Register(reg.0.parse().expect("did not get register"))
        }
    }

    fn parsed_value(
        &self,
        value: &crate::node_kinds::inline_ir_instruction::Value,
        binds: &[Value],
    ) -> Value {
        match value {
            crate::node_kinds::inline_ir_instruction::Value::Reg(v) => Value::Reg(*v),
            crate::node_kinds::inline_ir_instruction::Value::Int(v) => Value::Int(*v),
            crate::node_kinds::inline_ir_instruction::Value::Float(v) => Value::Float(*v),
            crate::node_kinds::inline_ir_instruction::Value::Bool(v) => Value::Bool(*v),
            crate::node_kinds::inline_ir_instruction::Value::Void => Value::Void,
            crate::node_kinds::inline_ir_instruction::Value::Uninit => Value::Uninit,
            crate::node_kinds::inline_ir_instruction::Value::Poison => Value::Poison,
            crate::node_kinds::inline_ir_instruction::Value::Record(symbol, values) => {
                Value::Record(
                    *symbol,
                    values.iter().map(|v| self.parsed_value(v, binds)).collect(),
                )
            }
            crate::node_kinds::inline_ir_instruction::Value::RawPtr(v) => Value::RawPtr(Addr(*v)),
            crate::node_kinds::inline_ir_instruction::Value::RawBuffer(items) => {
                Value::RawBuffer(items.to_vec())
            }
            crate::node_kinds::inline_ir_instruction::Value::Bind(i) => binds[*i].clone(),
        }
    }

    fn lookup_instance_method(
        &mut self,
        expr: &Expr,
        label: &Label,
    ) -> Result<Option<Symbol>, IRError> {
        let symbol = match &expr.kind {
            ExprKind::LiteralInt(_) => Symbol::Int,
            ExprKind::LiteralFloat(_) => Symbol::Float,
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => Symbol::Bool,
            _ => {
                let Ty::Nominal { symbol, .. } = self.specialized_ty(expr)?.0 else {
                    return Ok(None);
                };

                symbol
            }
        };

        if let Some(methods) = self.types.catalog.instance_methods.get(&symbol)
            && let Some(method) = methods.get(label)
        {
            return Ok(Some(*method));
        }

        Ok(None)
    }

    fn specialized_ty(&mut self, expr: &Expr) -> Result<(Ty, Substitutions), IRError> {
        let name = match &expr.kind {
            ExprKind::Variable(name) => name,
            ExprKind::Func(func) => &func.name,
            ExprKind::Constructor(name) => name,
            ExprKind::Member(Some(receiver), label, ..) => {
                let Ty::Constructor { name, .. } = self.ty_from_id(&receiver.id)? else {
                    return Ok((self.ty_from_id(&expr.id)?, Default::default()));
                };

                let Some((member, _)) = self
                    .types
                    .catalog
                    .lookup_member(&name.symbol().expect("didn't get sym"), label)
                else {
                    return Ok((self.ty_from_id(&expr.id)?, Default::default()));
                };

                &Name::Resolved(member, label.to_string())
            }
            _ => {
                tracing::trace!("expr has no substitutions: {expr:?}");
                return Ok((self.ty_from_id(&expr.id)?, Default::default()));
            }
        };

        let symbol = name.symbol().expect("name not resolved");
        let entry = self
            .types
            .get_symbol(&symbol)
            .cloned()
            .ok_or(IRError::TypeNotFound(format!(
                "no type found for {symbol:?}"
            )))?;

        let (ty, substitutions) = self.specialize(&entry, expr.id)?;
        _ = self.monomorphize_name(name.clone(), &substitutions);

        Ok((ty, substitutions))
    }

    #[instrument(skip(self, entry))]
    fn specialize(
        &mut self,
        entry: &TypeEntry,
        id: NodeID,
    ) -> Result<(Ty, Substitutions), IRError> {
        match entry {
            TypeEntry::Mono(ty) => Ok((ty.clone(), Default::default())),
            TypeEntry::Poly(scheme) => {
                let mut substitutions = Substitutions::default();
                for forall in scheme.foralls.iter() {
                    match forall {
                        ForAll::Ty(param) => {
                            let ty = self
                                .types
                                .catalog
                                .instantiations
                                .ty
                                .get(&(id, *param))
                                .cloned()
                                .unwrap_or(Ty::Param(*param));

                            if Ty::Param(*param) != ty {
                                substitutions.ty.insert(*param, ty);
                            }
                        }

                        ForAll::Row(param) => {
                            let row = self
                                .types
                                .catalog
                                .instantiations
                                .row
                                .get(&(id, *param))
                                .cloned()
                                .unwrap_or(Row::Param(*param));

                            substitutions.row.insert(*param, row);
                        }
                    };
                }

                let ty = substitute(scheme.ty.clone(), &substitutions);

                Ok((ty, substitutions))
            }
        }
    }

    #[instrument(skip(self), ret)]
    fn witness_for(&self, node_id: &NodeID, label: &Label) -> Option<&Symbol> {
        if let Some(MemberWitness::Concrete(witness)) =
            self.types.catalog.member_witnesses.get(node_id)
        {
            return Some(witness);
        }

        if let Some(MemberWitness::Requirement(witness, _ty)) =
            self.types.catalog.member_witnesses.get(node_id)
        {
            return Some(witness);
        }

        for module in self.config.modules.modules.values() {
            if let Some(MemberWitness::Concrete(witness)) =
                module.types.catalog.member_witnesses.get(node_id)
            {
                return Some(witness);
            }

            if let Some(MemberWitness::Requirement(witness, _ty)) =
                module.types.catalog.member_witnesses.get(node_id)
            {
                return Some(witness);
            }
        }

        None
    }

    fn field_index(&self, receiver_ty: &Ty, label: &Label) -> Label {
        match receiver_ty {
            Ty::Record(_, row) if let Some(idx) = row.close().get_index_of(label) => {
                Label::Positional(idx)
            }
            Ty::Nominal { symbol, .. }
                if let Some(idx) = self
                    .types
                    .catalog
                    .nominals
                    .get(symbol)
                    .expect("didn't find nominal")
                    .properties
                    .get_index_of(label) =>
            {
                Label::Positional(idx)
            }
            _ => panic!("unable to determine field index of {receiver_ty}.{label}"),
        }
    }

    fn ty_from_id(&self, id: &NodeID) -> Result<Ty, IRError> {
        match self.types.get(id) {
            Some(TypeEntry::Mono(ty)) => Ok(ty.clone()),
            Some(TypeEntry::Poly(scheme)) => Ok(scheme.ty.clone()),
            None => Err(IRError::TypeNotFound(format!("{id:?}"))),
        }
    }

    fn ty_from_symbol(&self, symbol: &Symbol) -> Result<Ty, IRError> {
        match self.types.get_symbol(symbol) {
            Some(TypeEntry::Mono(ty)) => Ok(ty.clone()),
            Some(TypeEntry::Poly(scheme)) => Ok(scheme.ty.clone()),
            None => {
                if matches!(
                    symbol,
                    Symbol::Synthesized(SynthesizedId {
                        module_id: ModuleId::Current,
                        local_id: 0
                    })
                ) {
                    Ok(Ty::Func(Ty::Void.into(), Ty::Void.into()))
                } else {
                    Err(IRError::TypeNotFound(format!("{symbol}")))
                }
            }
        }
    }
}

fn substitute(ty: Ty, substitutions: &Substitutions) -> Ty {
    match ty {
        Ty::Primitive(..) => ty,
        Ty::Param(type_param_id) => substitutions
            .ty
            .get(&type_param_id)
            .unwrap_or_else(|| {
                tracing::trace!("didn't find id {type_param_id:?} in {substitutions:?}");
                &ty
            })
            .clone(),
        Ty::Constructor {
            name,
            params,
            box ret,
        } => Ty::Constructor {
            name,
            params: params
                .into_iter()
                .map(|p| substitute(p, substitutions))
                .collect(),
            ret: substitute(ret, substitutions).into(),
        },
        Ty::Func(box param, box ret) => Ty::Func(
            substitute(param, substitutions).into(),
            substitute(ret, substitutions).into(),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .into_iter()
                .map(|i| substitute(i, substitutions))
                .collect(),
        ),
        Ty::Record(sym, box row) => Ty::Record(sym, substitute_row(row, substitutions).into()),
        Ty::Nominal { symbol, type_args } => Ty::Nominal {
            symbol,
            type_args: type_args
                .into_iter()
                .map(|a| substitute(a, substitutions))
                .collect(),
        },
    }
}

fn substitute_row(row: Row, substitutions: &Substitutions) -> Row {
    match row {
        Row::Empty(..) => row,
        Row::Param(id) => substitutions.row.get(&id).unwrap_or(&row).clone(),
        Row::Extend { box row, label, ty } => Row::Extend {
            row: substitute_row(row, substitutions).into(),
            label,
            ty: substitute(ty, substitutions),
        },
    }
}

fn is_main_func(node: &Node) -> bool {
    if let Node::Decl(Decl {
        kind:
            DeclKind::Let {
                rhs:
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

pub fn curry_ty<'a, I: IntoIterator<Item = &'a Ty>>(params: I, ret: Ty) -> Ty {
    let mut params = params.into_iter().collect::<Vec<_>>();
    if params.is_empty() {
        params.push(&Ty::Void);
    }
    params
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p.clone()), Box::new(acc)))
}
