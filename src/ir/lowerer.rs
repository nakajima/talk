use crate::compiling::module::{ModuleEnvironment, ModuleId};
use crate::formatter;
use crate::ir::basic_block::{Phi, PhiSource};
use crate::ir::instruction::CmpOperator;
use crate::ir::ir_ty::IrTy;
use crate::ir::monomorphizer::uncurry_function;
use crate::ir::parse_instruction;
use crate::label::Label;
use crate::name_resolution::symbol::{InstanceMethodId, Symbols};
use crate::node_kinds::match_arm::MatchArm;
use crate::node_kinds::parameter::Parameter;
use crate::node_kinds::record_field::RecordField;
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
use rustc_hash::FxHashMap;
use tracing::instrument;

enum LValue<F> {
    Field {
        base: Box<LValue<F>>,
        field: F,
        ty: Ty,
    },
    Variable(Symbol),
}

#[derive(Debug)]
pub(super) struct CurrentFunction {
    current_block_idx: Vec<usize>,
    blocks: Vec<BasicBlock<Ty>>,
    pub registers: RegisterAllocator,
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
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Bind {
    Assigned(Register),
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
}

impl Substitutions {
    pub fn extend(&mut self, other: Substitutions) {
        self.ty.extend(other.ty);
        self.row.extend(other.row);
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

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer<'a> {
    pub(super) asts: &'a mut IndexMap<Source, AST<NameResolved>>,
    pub(super) types: &'a mut Types,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,

    symbols: &'a mut Symbols,
    bindings: FxHashMap<Symbol, Register>,
    modules: &'a ModuleEnvironment,
    pub(super) specializations: IndexMap<Symbol, Vec<Specialization>>,
}

impl<'a> Lowerer<'a> {
    pub fn new(
        asts: &'a mut IndexMap<Source, AST<NameResolved>>,
        types: &'a mut Types,
        symbols: &'a mut Symbols,
        modules: &'a ModuleEnvironment,
    ) -> Self {
        Self {
            asts,
            types,
            functions: Default::default(),
            current_function_stack: Default::default(),
            bindings: Default::default(),
            symbols,
            specializations: Default::default(),
            modules,
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.asts.is_empty() {
            return Ok(Program::default());
        }

        // Do we have a main func?
        let mut asts = std::mem::take(self.asts);
        let has_main_func = asts.iter_mut().flat_map(|a| &a.1.roots).any(is_main_func);
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
        }

        self.current_function_stack.push(CurrentFunction::default());

        for ast in asts.values_mut() {
            for root in ast.roots.iter() {
                self.lower_node(root, &Default::default())?;
            }
        }

        _ = std::mem::replace(self.asts, asts);

        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
            polyfunctions: monomorphizer.functions,
        })
    }

    fn lower_node(
        &mut self,
        node: &Node,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        match node {
            Node::Decl(decl) => self.lower_decl(decl, instantiations),
            Node::Stmt(stmt) => self.lower_stmt(stmt, instantiations),
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
                self.lower_expr(value, bind, instantiations)?;
            }
            DeclKind::Struct { body, .. } => {
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
            DeclKind::Associated { .. } => todo!(),
            DeclKind::Func(..) => todo!(),
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
            DeclKind::FuncSignature(..) => todo!(),
            DeclKind::MethodRequirement(..) => todo!(),
            DeclKind::TypeAlias(..) => todo!(),
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
        let func_ty = match self.types.get_symbol(&name.symbol()).unwrap() {
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
                self.types.get_symbol(&name.symbol()).unwrap(),
                func_ty,
                formatter.format(&[Node::Decl(decl.clone())], 80)
            );
        };

        self.current_function_stack.push(CurrentFunction::default());

        let mut param_values = vec![];
        for param in params.iter() {
            let register = self.next_register();
            param_values.push(Value::Reg(register.0));
            self.bindings.insert(param.name.symbol(), register);
        }

        let mut ret = Value::Void;
        for node in body.body.iter() {
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
        }
        self.push_terminator(Terminator::Ret {
            val: ret.clone(),
            ty: ret_ty.clone(),
        });

        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");

        self.functions.insert(
            name.symbol(),
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
    ) -> Result<(Value, Ty), IRError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.lower_expr(expr, Bind::Fresh, instantiations),
            StmtKind::If(cond, conseq, alt) => {
                self.lower_if_stmt(cond, conseq, alt, instantiations)
            }
            StmtKind::Return(_expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs, instantiations),
            StmtKind::Loop(_expr, _block) => todo!(),
        }
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

    #[instrument(level = tracing::Level::TRACE, skip(self, block), fields(block.id = %block.id))]
    fn lower_block(
        &mut self,
        block: &Block,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ret = self.ret(bind);

        for node in &block.body {
            self.lower_node(node, instantiations)?;
        }

        let ty = self.ty_from_id(&block.id)?;

        Ok((ret.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs), fields(lhs.id = %lhs.id, rhs.id = %rhs.id))]
    fn lower_assignment(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let lvalue = self.lower_lvalue(lhs)?;
        let (value, ty) = self.lower_expr(rhs, Bind::Fresh, instantiations)?;

        self.emit_lvalue_store(lvalue, value)?;

        Ok((Value::Void, ty))
    }

    fn emit_load_lvalue(
        &mut self,
        receiver_ty: &Ty,
        lvalue: &LValue<Label>,
    ) -> Result<Register, IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                // Variable is already in a register
                Ok(*self.bindings.get(sym).unwrap())
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

    fn emit_lvalue_store(&mut self, lvalue: LValue<Label>, value: Value) -> Result<(), IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                // Simple rebind
                let reg = value.as_register()?;
                self.bindings.insert(sym, reg);
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

    fn lower_lvalue(&mut self, expr: &Expr) -> Result<LValue<Label>, IRError> {
        match &expr.kind {
            ExprKind::Variable(name) => Ok(LValue::Variable(name.symbol())),
            ExprKind::Member(Some(box receiver), label, _span) => {
                let receiver_lvalue = self.lower_lvalue(receiver)?;
                let (receiver_ty, ..) = self.specialized_ty(receiver).expect("didn't get base ty");

                Ok(LValue::Field {
                    base: receiver_lvalue.into(),
                    ty: receiver_ty.clone(),
                    field: label.clone(),
                })
            }
            _ => Err(IRError::InvalidAssignmentTarget(format!("{expr:?}"))),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, pattern), fields(pattern.id = %pattern.id))]
    fn lower_pattern(&mut self, pattern: &Pattern) -> Result<Bind, IRError> {
        match &pattern.kind {
            PatternKind::Bind(name) => {
                let value = self.next_register();
                let symbol = name.symbol();
                self.bindings.insert(symbol, value);
                Ok(Bind::Assigned(value))
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

    #[instrument(level = tracing::Level::TRACE, skip(self, expr), fields(expr.id = %expr.id))]
    fn lower_expr(
        &mut self,
        expr: &Expr,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        match &expr.kind {
            ExprKind::Func(func) => self.lower_func(func, bind, instantiations),
            ExprKind::LiteralArray(_exprs) => todo!(),
            ExprKind::LiteralInt(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::Constant {
                    dest: ret,
                    val: Value::Int(str::parse(val).unwrap()),
                    ty: Ty::Int,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok((ret.into(), Ty::Int))
            }
            ExprKind::LiteralFloat(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::Constant {
                    dest: ret,
                    val: Value::Float(str::parse(val).unwrap()),
                    ty: Ty::Float,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok((ret.into(), Ty::Float))
            }
            ExprKind::LiteralTrue => Ok((Value::Bool(true), Ty::Bool)),
            ExprKind::LiteralFalse => Ok((Value::Bool(false), Ty::Bool)),
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(..) => todo!(),
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
            ExprKind::If(..) => todo!(),
            ExprKind::Match(box scrutinee, arms) => {
                self.lower_match(scrutinee, arms, bind, instantiations)
            }
            ExprKind::RecordLiteral { fields, .. } => {
                self.lower_record_literal(expr, fields, bind, instantiations)
            }
            ExprKind::RowVariable(..) => todo!(),
            ExprKind::As(lhs, ..) => self.lower_expr(lhs, bind, instantiations),
            _ => unreachable!("cannot lower expr: {expr:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        // Type of the whole match expression (all arm bodies are this type).
        // If you have a dedicated match expr node id, you can use that instead.
        let result_type = {
            let first_arm_expr_id = arms[0].body.id;
            self.ty_from_id(&first_arm_expr_id)?
        };

        // This is the "result variable" of the match expression.
        // If in statement position, this may just be DROP and never used.
        let result_register = self.ret(bind);

        // 1. Lower scrutinee.
        let (scrutinee_value, _scrutinee_type) =
            self.lower_expr(scrutinee, Bind::Fresh, instantiations)?;
        let scrutinee_register = scrutinee_value.as_register()?;

        // 2. One block per arm + a join block.
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
        let current_function = self.current_function_stack.last().unwrap();
        let current_block_index = *current_function.current_block_idx.last().unwrap();
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

        let ty = Ty::Record(field_row.into());
        let dest = self.ret(bind);
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
            .get(&name.symbol())
            .unwrap()
            .get(&Label::Named("init".into()))
            .unwrap();

        let init_entry = self.types.get_symbol(&constructor_sym).cloned().unwrap();
        let (ty, mut instantiations) = self.specialize(&init_entry, expr.id)?;
        instantiations.ty.extend(old_instantiations.ty.clone());
        instantiations.row.extend(old_instantiations.row.clone());

        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty: ty.clone(),
            val: Value::Func(Name::Resolved(constructor_sym, format!("{}_init", name))),
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
        let enum_symbol = name.symbol();
        let constructor_sym = *self
            .types
            .catalog
            .variants
            .get(&enum_symbol)
            .unwrap()
            .get(variant_name)
            .unwrap_or_else(|| panic!("didn't get {:?}", name));

        let tag = self
            .types
            .catalog
            .variants
            .get(&enum_symbol)
            .unwrap()
            .get_index_of(variant_name)
            .unwrap();

        let enum_entry = self.types.get_symbol(&enum_symbol).unwrap().clone();
        let (_, _ty_instantiations) = self.specialize(&enum_entry, id)?;
        let init_entry = self.types.get_symbol(&constructor_sym).cloned().unwrap();
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

        let ty = Ty::Record(row.into());
        let dest = self.ret(bind);
        self.push_instr(Instruction::Record {
            dest,
            ty: ty.clone(),
            record: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, receiver))]
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
                    val: Value::Func(Name::Resolved(method, label.to_string())),
                });
            } else if let Some(witness) = self.witness_for(&id, label).copied()
                && matches!(witness, Symbol::InstanceMethod(..))
            {
                tracing::debug!("lowering req {label} {witness:?}");
                println!("ok wise guuy {:?}", self.types.catalog.instantiations.ty);

                self.check_import(&witness);
                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val: Value::Func(Name::Resolved(witness, label.to_string())),
                });
            } else {
                println!("lower_member: Not a method, generating GetField");
                let label = self.field_index(&receiver_ty, label);
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

        let ret = if matches!(monomorphized_ty, Ty::Func(..)) {
            // It's a func reference so we pass the name
            let monomorphized_name = self.monomorphize_name(name.clone(), &instantiations);
            Value::Func(monomorphized_name)
        } else {
            self.bindings.get(&name.symbol()).unwrap().into()
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
            .get(&name.symbol())
            .unwrap()
            .get(&Label::Named("init".into()))
            .unwrap();

        let init_entry = self.types.get_symbol(&init_sym).cloned().unwrap();
        let (init_ty, concrete_tys) = self.specialize(&init_entry, callee.id)?;

        let properties = self.types.catalog.properties.get(&name.symbol()).unwrap();

        // Extract return type from the initializer function
        let mut params = init_ty.clone().uncurry_params();
        let ret = params.pop().unwrap();

        self.push_instr(Instruction::Record {
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
            callee: Value::Func(init),
            args: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ret))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
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
            && name.symbol() == Symbol::IR
        {
            return self.lower_embedded_ir_call(call_expr.id, args, dest);
        }

        let (_callee_ty, mut instantiations) = self.specialized_ty(callee).unwrap();
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
                receiver,
                member,
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
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_method_call(
        &mut self,
        call_expr: &Expr,
        callee_expr: &Expr,
        receiver: &Expr,
        label: &Label,
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_id(&call_expr.id)?;
        let (receiver_ir, _) = self.lower_expr(receiver, Bind::Fresh, instantiations)?;
        args.insert(0, receiver_ir);

        if let Some(method_sym) = self.lookup_instance_method(receiver, label)? {
            self.check_import(&method_sym);
            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: Value::Func(Name::Resolved(method_sym, label.to_string())),
                args: args.into(),
                meta: vec![InstructionMeta::Source(call_expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        };

        if let Some(witness) = self.witness_for(&callee_expr.id, label).copied() {
            println!("Got a witness! {witness:?}");
            self.check_import(&witness);
            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: Value::Func(Name::Resolved(witness, label.to_string())),
                args: args.into(),
                meta: vec![InstructionMeta::Source(call_expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        }

        Err(IRError::TypeNotFound(format!(
            "No witness found for {:?} in {:?}.",
            label, receiver
        )))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func.name = %func.name))]
    fn lower_func(
        &mut self,
        func: &Func,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_symbol(&func.name.symbol())?;

        let Ty::Func(param_tys, box mut ret_ty) = ty else {
            panic!("didn't get func ty for {:?}: {ty:?}", func.name);
        };

        let _s = tracing::trace_span!("pushing new current function");
        self.current_function_stack.push(CurrentFunction::default());

        let mut params = vec![];
        for param in func.params.iter() {
            let register = self.next_register();
            params.push(Value::Reg(register.0));
            self.bindings.insert(param.name.symbol(), register);
        }

        let mut ret = Value::Void;
        for node in func.body.body.iter() {
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
        }

        self.push_terminator(Terminator::Ret {
            val: ret,
            ty: ret_ty.clone(),
        });

        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");
        drop(_s);
        self.functions.insert(
            func.name.symbol(),
            PolyFunction {
                name: func.name.clone(),
                params,
                blocks: current_function.blocks,
                ty: Ty::Func(param_tys.clone(), ret_ty.clone().into()),
                register_count: (current_function.registers.next) as usize,
            },
        );

        let func = Value::Func(func.name.clone());
        if bind != Bind::Discard {
            let dest = self.ret(bind);
            self.push_instr(Instruction::Ref {
                dest,
                ty: Ty::Func(param_tys.clone(), ret_ty.clone().into()),
                val: func.clone(),
            });
        }
        Ok((func, Ty::Func(param_tys, ret_ty.into())))
    }

    fn lower_embedded_ir_call(
        &mut self,
        id: NodeID,
        args: &[CallArg],
        dest: Register,
    ) -> Result<(Value, Ty), IRError> {
        let ExprKind::LiteralString(string) = &args[0].value.kind else {
            unreachable!()
        };

        let mut string = string.clone();

        if string.contains("$?") {
            string = string.replace("$?", &format!("%{}", dest.0));
        }

        self.push_instr(parse_instruction::<IrTy>(&string).into());

        let ty = self.ty_from_id(&id).unwrap();

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_instr(&mut self, instruction: Instruction<Ty>) {
        let current_function = self.current_function_stack.last_mut().unwrap();
        let current_block_idx = current_function.current_block_idx.last().unwrap();
        current_function.blocks[*current_block_idx]
            .instructions
            .push(instruction);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_phi(&mut self, phi: Phi<Ty>) {
        let current_function = self.current_function_stack.last_mut().unwrap();
        let current_block_idx = current_function.current_block_idx.last().unwrap();
        current_function.blocks[*current_block_idx].phis.push(phi);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn new_basic_block(&mut self) -> BasicBlockId {
        let current_function = self.current_function_stack.last_mut().unwrap();
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
    fn set_current_block(&mut self, id: BasicBlockId) {
        self.current_function_stack
            .last_mut()
            .unwrap()
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
            .unwrap()
            .current_block_idx
            .push(id.0 as usize);
        let ret = f(self);
        self.current_function_stack
            .last_mut()
            .unwrap()
            .current_block_idx
            .pop();
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let current_function = self.current_function_stack.last_mut().unwrap();
        let current_block_idx = current_function.current_block_idx.last().unwrap();
        current_function.blocks[*current_block_idx].terminator = terminator;
    }

    fn next_register(&mut self) -> Register {
        let current_function = self.current_function_stack.last_mut().unwrap();
        let register = current_function.registers.next();
        tracing::trace!("allocated register: {register}");
        register
    }

    fn ret(&mut self, bind: Bind) -> Register {
        match bind {
            Bind::Assigned(value) => value,
            Bind::Fresh => self.next_register(),
            Bind::Discard => Register::DROP,
        }
    }

    /// Check to see if this symbol comes from an external module, if so we need to import the code into our program.
    fn check_import(&mut self, symbol: &Symbol) {
        if let Symbol::InstanceMethod(InstanceMethodId {
            module_id: module_id @ (ModuleId::Core | ModuleId::Builtin | ModuleId::External(..)),
            ..
        }) = symbol
        {
            let module = self.modules.modules.get(module_id).unwrap();
            tracing::debug!("importing {symbol:?} from {module_id}");
            // TODO: This won't work with external methods yet, only core works.
            let method_func = module.program.polyfunctions.get(symbol).unwrap();
            self.functions.insert(*symbol, method_func.clone());
        }
    }

    fn monomorphize_name(&mut self, name: Name, instantiations: &Substitutions) -> Name {
        if instantiations.ty.is_empty() {
            return name;
        }

        let new_symbol = self.symbols.next_synthesized(ModuleId::Current);
        let new_name_str = format!(
            "{}[{}]",
            name,
            instantiations
                .ty
                .values()
                .map(|v| format!("{v}"))
                .collect::<Vec<_>>()
                .join(", ")
        );

        let new_name = Name::Resolved(new_symbol.into(), new_name_str);

        self.specializations
            .entry(name.symbol())
            .or_default()
            .push(Specialization {
                name: new_name.clone(),
                substitutions: instantiations.clone(),
            });

        new_name
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
            _ => {
                tracing::trace!("expr has no substitutions: {expr:?}");
                println!(
                    "expr has no substitutions: {expr:?}, {:?}",
                    self.ty_from_id(&expr.id)
                );
                return Ok((self.ty_from_id(&expr.id)?, Default::default()));
            }
        };

        let symbol = name.symbol();

        let entry = self
            .types
            .get_symbol(&symbol)
            .cloned()
            .ok_or(IRError::TypeNotFound(format!(
                "no type found for {symbol:?}"
            )))
            .unwrap();

        let (ty, substitutions) = self.specialize(&entry, expr.id)?;
        _ = self.monomorphize_name(name.clone(), &substitutions);

        Ok((ty, substitutions))
    }

    #[instrument(skip(self))]
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
        if let Some(MemberWitness::Concrete(witness) | MemberWitness::Requirement(witness)) =
            self.types.catalog.member_witnesses.get(node_id)
        {
            return Some(witness);
        }

        for module in self.modules.modules.values() {
            if let Some(MemberWitness::Concrete(witness) | MemberWitness::Requirement(witness)) =
                module.types.catalog.member_witnesses.get(node_id)
            {
                return Some(witness);
            }
        }

        None
    }

    fn field_index(&self, receiver_ty: &Ty, label: &Label) -> Label {
        if let Ty::Record(row) | Ty::Nominal { row, .. } = receiver_ty
            && let Some(idx) = row.close().get_index_of(label)
        {
            Label::Positional(idx)
        } else {
            label.clone()
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
        Ty::Record(box row) => Ty::Record(substitute_row(row, substitutions).into()),
        Ty::Nominal { symbol, box row } => Ty::Nominal {
            symbol,
            row: substitute_row(row, substitutions).into(),
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
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p.clone()), Box::new(acc)))
}
