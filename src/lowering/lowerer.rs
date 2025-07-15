use std::{collections::HashMap, ops::AddAssign, str::FromStr};

use crate::{
    Lowered, SourceFile, SymbolID, SymbolInfo, SymbolKind, SymbolTable, Typed,
    analysis::{
        cfg::ControlFlowGraph, function_analysis::definite_initialization::DefiniteInitizationPass,
        function_analysis_pass::FunctionAnalysisPass,
    },
    compiling::{compilation_session::SharedCompilationSession, driver::DriverConfig},
    constraint::Constraint,
    diagnostic::Diagnostic,
    environment::Environment,
    expr::ExprMeta,
    lowering::{
        instr::{Callee, Instr},
        ir_error::IRError,
        ir_function::IRFunction,
        ir_module::{IRConstantData, IRModule},
        ir_type::IRType,
        ir_value::IRValue,
        parsing::parser::ParserError,
        phi_predecessors::PhiPredecessors,
        register::Register,
    },
    name::ResolvedName,
    parser::ExprID,
    source_file,
    token::Token,
    token_kind::TokenKind,
    ty::Ty,
    type_checker::Scheme,
    type_defs::{TypeDef, protocol_def::Conformance, struct_def::StructDef},
    type_var_id::{TypeVarID, TypeVarKind},
    typed_expr::{Expr, Pattern, TypedExpr},
};

#[derive(Debug, Clone, PartialEq)]
pub enum RefKind {
    Func(String),
}

impl FromStr for RefKind {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The string representation of a RefKind::Func is just the function name,
        // which starts with '@'.
        if s.starts_with('@') {
            Ok(RefKind::Func(s.to_string()))
        } else {
            Err(ParserError::UnexpectedToken(
                vec![],
                crate::lowering::parsing::lexer::Tokind::Identifier(s.to_string()),
            ))
        }
    }
}

impl std::fmt::Display for RefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // f.write_str("ref ")?;
        match self {
            Self::Func(name) => f.write_str(name)?,
        };
        Ok(())
    }
}

impl Ty {
    pub(super) fn to_ir(&self, lowerer: &Lowerer) -> IRType {
        match self {
            Ty::SelfType => IRType::Void,
            Ty::Pointer => IRType::POINTER,
            Ty::Init(_sym, params) => IRType::Func(
                params.iter().map(|t| t.to_ir(lowerer)).collect(),
                IRType::Void.into(),
            ),
            Ty::Byte => IRType::Byte,
            Ty::Void => IRType::Void,
            Ty::Int => IRType::Int,
            Ty::Bool => IRType::Bool,
            Ty::Float => IRType::Float,
            Ty::Func(items, ty, _generics) => IRType::Func(
                items.iter().map(|t| t.to_ir(lowerer)).collect(),
                Box::new(ty.to_ir(lowerer)),
            ),
            Ty::TypeVar(type_var_id) => IRType::TypeVar(format!("T{}", type_var_id.id)),
            Ty::Enum(symbol_id, generics) => IRType::Enum(
                *symbol_id,
                generics.iter().map(|i| i.to_ir(lowerer)).collect(),
            ),
            Ty::EnumVariant(enum_id, items) => {
                // let enum_def = lowerer.env.lookup_enum(enum_id).unwrap();
                IRType::Enum(*enum_id, items.iter().map(|t| t.to_ir(lowerer)).collect())
            }
            Ty::Closure { func, .. } => func.to_ir(lowerer),
            Ty::Tuple(items) => IRType::Struct(
                SymbolID::TUPLE,
                items.iter().map(|i| i.to_ir(lowerer)).collect(),
                vec![],
            ),
            Ty::Array(el) => IRType::TypedBuffer {
                element: el.to_ir(lowerer).into(),
            },
            Ty::Struct(symbol_id, generics) => {
                let Some(TypeDef::Struct(struct_def)) = lowerer.env.lookup_type(symbol_id) else {
                    tracing::error!("Unable to determine definition of struct: {symbol_id:?}");
                    return IRType::Void;
                };

                IRType::Struct(
                    *symbol_id,
                    struct_def
                        .properties
                        .iter()
                        .map(|p| p.ty.to_ir(lowerer))
                        .collect(),
                    generics.iter().map(|g| g.to_ir(lowerer)).collect(),
                )
            }
            Ty::Protocol(_, _) => IRType::Void,
        }
    }
}

pub enum IRPattern {
    Bind,
    Wildcard,
    EnumVariant { tag: u32, bindings: Vec<IRType> },
    IntLiteral(i64),
    FloatLiteral(f64),
    LiteralBool(bool),
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub struct BasicBlockID(pub u32);

impl BasicBlockID {
    pub const ENTRY: BasicBlockID = BasicBlockID(0);
}

impl AddAssign<u32> for BasicBlockID {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs
    }
}

impl FromStr for BasicBlockID {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "entry" {
            Ok(BasicBlockID(0))
        } else {
            Ok(BasicBlockID(str::parse(&s[1..]).unwrap_or(u32::MAX)))
        }
    }
}

impl std::fmt::Display for BasicBlockID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CurrentBasicBlock {
    pub id: BasicBlockID,
    pub instructions: Vec<InstructionWithExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub id: BasicBlockID,
    pub instructions: Vec<Instr>,
}

impl BasicBlock {
    fn _push_instr(&mut self, instr: Instr) {
        self.instructions.push(instr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedRegister {
    pub ty: IRType,
    pub register: Register,
}

impl TypedRegister {
    pub fn new(ty: IRType, register: Register) -> Self {
        Self { ty, register }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RegisterList(pub Vec<TypedRegister>);

impl RegisterList {
    pub const EMPTY: RegisterList = RegisterList(vec![]);
}

impl std::fmt::Display for RegisterList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, reg) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{} {}", reg.ty, reg.register)?;
        }
        Ok(())
    }
}
impl FromStr for TypedRegister {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let mut parts = s.split_whitespace();

        let Some(ty_str) = parts.next() else {
            return Err(IRError::ParseError(
                "Could not get register type".to_string(),
            ));
        };

        let Some(reg_str) = parts.next() else {
            return Err(IRError::ParseError(
                "Could not get typed register".to_string(),
            ));
        };

        Ok(TypedRegister {
            ty: IRType::from_str(ty_str).map_err(|e| IRError::ParseError(format!("{e:?}")))?,
            register: str::parse(reg_str).map_err(|e| IRError::ParseError(format!("{e:?}")))?,
        })
    }
}

// Replace the old implementation with this one.
impl FromStr for RegisterList {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The input 's' is the content *between* the parentheses, e.g., "%1, %2" or "".
        let s = s.trim();
        if s.is_empty() {
            // Correctly handle the case of zero arguments.
            return Ok(RegisterList(vec![]));
        }

        // For non-empty arguments, split by comma and parse each part.
        s.split(',')
            .map(|part| part.trim().parse::<TypedRegister>())
            .collect::<Result<Vec<TypedRegister>, _>>()
            .map(RegisterList)
            .map_err(|e| IRError::ParseError(format!("{e:?}")))
    }
}

#[derive(Debug, Clone)]
pub enum SymbolValue {
    Register(Register),
    Capture(usize, IRType),
    Struct(StructDef),
    FuncRef(String),
}

impl From<Register> for SymbolValue {
    fn from(value: Register) -> Self {
        Self::Register(value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InstructionWithExpr {
    pub instr: Instr,
    pub expr_id: Option<ExprID>,
}

#[derive(Debug)]
struct CurrentFunction {
    current_block_idx: usize,
    next_block_id: BasicBlockID,
    blocks: Vec<CurrentBasicBlock>,
    env_ty: Option<IRType>,
    pub registers: RegisterAllocator,
    pub symbol_registers: HashMap<SymbolID, SymbolValue>,
}

impl CurrentFunction {
    fn new(env_ty: Option<IRType>) -> Self {
        Self {
            next_block_id: BasicBlockID(0),
            current_block_idx: 0,
            blocks: Default::default(),
            env_ty,
            registers: RegisterAllocator::new(),
            symbol_registers: Default::default(),
        }
    }

    fn next_block_id(&mut self) -> BasicBlockID {
        let id = self.next_block_id;
        self.next_block_id += 1;
        id
    }

    fn add_block(&mut self, block: CurrentBasicBlock) {
        self.blocks.push(block);
    }

    fn current_block_mut(&mut self) -> &mut CurrentBasicBlock {
        &mut self.blocks[self.current_block_idx]
    }

    fn set_current_block(&mut self, id: BasicBlockID) -> Result<(), IRError> {
        let Some(index) = self.blocks.iter().position(|blk| blk.id == id) else {
            return Err(IRError::Unknown(format!(
                "Current function has no block with id {id}"
            )));
        };

        self.current_block_idx = index;

        Ok(())
    }

    fn register_symbol(&mut self, symbol_id: SymbolID, register: SymbolValue) {
        tracing::trace!("register symbol {:?}: {:?}", symbol_id, register,);
        self.symbol_registers.insert(symbol_id, register);
    }

    fn _lookup_symbol(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.symbol_registers.get(symbol_id)
    }

    fn export(
        self,
        ty: IRType,
        name: String,
        env_ty: Option<IRType>,
        env_reg: Option<Register>,
        source_file: &SourceFile<source_file::Typed>,
    ) -> IRFunction {
        let mut blocks = vec![];
        let mut debug_info = DebugInfo::default();

        for block in self.blocks.into_iter() {
            let mut instr_expr_ids = HashMap::default();
            let mut instructions = vec![];
            for (i, instruction) in block.instructions.into_iter().enumerate() {
                instructions.push(instruction.instr);
                if let Some(expr_id) = instruction.expr_id {
                    let meta = source_file.meta.borrow();
                    instr_expr_ids.insert(i, meta.get(&expr_id).cloned());
                }
            }

            debug_info.insert(block.id, instr_expr_ids);

            blocks.push(BasicBlock {
                id: block.id,
                instructions,
            });
        }

        tracing::trace!("EXPORING FUNC: {} {:?}", name, self.registers);

        IRFunction {
            ty,
            name,
            blocks,
            env_ty,
            env_reg,
            size: self.registers.next_id,
            debug_info,
        }
    }
}

pub type DebugInfo = HashMap<BasicBlockID, HashMap<usize, Option<ExprMeta>>>;

#[derive(Debug, Clone, PartialEq)]
struct RegisterAllocator {
    next_id: i32,
}

impl RegisterAllocator {
    fn new() -> Self {
        tracing::trace!("new register allocator");
        Self { next_id: 0 }
    }

    fn allocate(&mut self) -> Register {
        let id = self.next_id;
        self.next_id += 1;
        Register(id)
    }
}

pub struct Lowerer<'a> {
    pub(super) source_file: SourceFile<Typed>,
    current_functions: Vec<CurrentFunction>,
    lowered_functions: Vec<IRFunction>,
    symbol_table: &'a mut SymbolTable,
    loop_exits: Vec<BasicBlockID>,
    globals: HashMap<SymbolID, SymbolValue>,
    current_expr_ids: Vec<ExprID>,
    pub env: &'a mut Environment,
    session: SharedCompilationSession,
    constants: Vec<IRConstantData>,
}

impl<'a> Lowerer<'a> {
    pub fn new(
        source_file: SourceFile<Typed>,
        symbol_table: &'a mut SymbolTable,
        env: &'a mut Environment,
        session: SharedCompilationSession,
    ) -> Self {
        Self {
            source_file,
            current_functions: vec![],
            lowered_functions: Default::default(),
            symbol_table,
            globals: HashMap::new(),
            loop_exits: vec![],
            current_expr_ids: vec![],
            env,
            session,
            constants: Default::default(),
        }
    }

    pub fn lower(
        mut self,
        module: &mut IRModule,
        driver_config: &DriverConfig,
    ) -> SourceFile<Lowered> {
        let roots = self.source_file.phase_data.roots.clone();

        if driver_config.executable {
            let (expr_id, did_create) =
                find_or_create_main(&mut self.source_file, self.symbol_table, self.env);

            // If we created the main function, we need to set it up
            if did_create {
                // Make sure we have a current function
                self.current_functions.push(CurrentFunction::new(None));

                // Make sure it has a basic block
                let entry = self.new_basic_block();
                self.set_current_block(entry);
            }

            self.lower_function(&expr_id);

            // If we created the main function, we moved all the typed roots into its body
            // so we don't need to lower them again.
            if !did_create {
                for root in roots.iter() {
                    if let Expr::Func { .. } = &root.expr {
                        self.lower_function(root);
                    }
                }
            }
        } else {
            self.current_functions.push(CurrentFunction::new(None));
            let id = self.new_basic_block();
            self.set_current_block(id);

            for root in roots.iter() {
                self.lower_expr(root);
            }
        }

        for function in self.lowered_functions {
            module.functions.push(function)
        }

        module.constants = self.constants;

        self.source_file.to_lowered()
    }

    pub fn lower_expr(&mut self, typed_expr: &TypedExpr) -> Option<Register> {
        self.current_expr_ids.push(typed_expr.id);

        let res = match &typed_expr.expr {
            Expr::LiteralInt(_)
            | Expr::LiteralFloat(_)
            | Expr::LiteralFalse
            | Expr::LiteralTrue => self.lower_literal(typed_expr),
            Expr::Binary(_, _, _) => self.lower_binary_op(typed_expr),
            Expr::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs),
            Expr::Variable(name) => self.lower_variable(typed_expr, name),
            Expr::If(_, _, _) => self.lower_if(typed_expr),
            Expr::Block(_) => self.lower_block(typed_expr),
            Expr::Call { callee, args, .. } => {
                self.lower_call(callee, &typed_expr.ty.to_ir(self), args)
            }
            Expr::Func { .. } => self.lower_function(typed_expr),
            Expr::Return(rhs) => self.lower_return(typed_expr, rhs),
            Expr::EnumDecl { .. } => None,
            Expr::Member(Some(box receiver), name) => {
                self.lower_member(&Some(receiver), typed_expr, name, false)
            }
            Expr::Member(None, name) => self.lower_member(&None, typed_expr, name, false),
            Expr::Match(scrutinee, arms) => self.lower_match(scrutinee, arms, &typed_expr.ty),
            Expr::CallArg { value, .. } => self.lower_expr(value),
            Expr::Struct {
                name: ResolvedName(struct_id, _),
                body,
                ..
            } => self.lower_struct(typed_expr, *struct_id, body),
            Expr::Extend {
                name: ResolvedName(type_id, _),
                body,
                ..
            } => self.lower_extend(*type_id, body),
            Expr::Init(symbol_id, func_id) => self.lower_init(symbol_id, func_id).or_else(|| {
                self.push_err(format!("No symbol for ID {func_id:?}").as_str(), func_id.id);

                None
            }),
            Expr::TypeRepr { .. } => None, // these are just for the type system
            Expr::LiteralArray(items) => self.lower_array(typed_expr, items),
            Expr::Loop(cond, body) => self.lower_loop(cond, body),
            Expr::Break => {
                let Some(current_loop_exit) = self.loop_exits.last() else {
                    self.add_diagnostic(Diagnostic::lowering(
                        self.source_file.path.clone(),
                        typed_expr.id,
                        IRError::Unknown("trying to break while not in a loop".into()),
                    ));

                    return None;
                };

                self.push_instr(Instr::Jump(*current_loop_exit));
                None
            }
            Expr::ProtocolDecl {
                name,
                body:
                    box TypedExpr {
                        expr: Expr::Block(items),
                        ..
                    },
                ..
            } => self.lower_protocol(name, items),
            Expr::Tuple(items) => self.lower_tuple(typed_expr, items),
            Expr::LiteralString(string) => self.lower_string(typed_expr, string.to_string()),
            expr => {
                self.add_diagnostic(Diagnostic::lowering(
                    self.source_file.path.clone(),
                    typed_expr.id,
                    IRError::Unknown(format!("Cannot lower {expr:?}")),
                ));

                None
            }
        };

        self.current_expr_ids.pop();

        res
    }

    fn lower_protocol(&mut self, name: &ResolvedName, items: &[TypedExpr]) -> Option<Register> {
        for body_expr in items {
            if let Expr::Func { .. } = &body_expr.expr {
                self.lower_method(body_expr, name)?;
            }

            if let TypedExpr {
                expr:
                    Expr::FuncSignature {
                        name: func_name, ..
                    },
                ty,
                ..
            } = &body_expr
            {
                self.lower_method_stub(ty, name, func_name)?;
            }
        }

        None
    }

    fn lower_tuple(&mut self, typed_expr: &TypedExpr, items: &[TypedExpr]) -> Option<Register> {
        let mut member_registers = vec![];
        let mut member_types = vec![];

        for item in items {
            if let Some(reg) = self.lower_expr(item) {
                let ir_type = item.ty.to_ir(self);
                member_registers.push(TypedRegister::new(ir_type.clone(), reg));
                member_types.push(ir_type);
            } else {
                self.push_err("Could not lower tuple element", item.id);
                return None;
            }
        }

        // we represent tuples as structs for now
        let dest = self.allocate_register();
        self.push_instr(Instr::MakeStruct {
            dest,
            ty: typed_expr.ty.to_ir(self),
            values: RegisterList(member_registers),
        });

        Some(dest)
    }

    fn lower_loop(&mut self, cond: &Option<Box<TypedExpr>>, body: &TypedExpr) -> Option<Register> {
        let current_block = self.current_block_mut()?.id;
        let loop_entry = self.new_basic_block();
        let loop_exit = self.new_basic_block();
        let loop_cond = if let Some(cond) = cond {
            let loop_cond = self.new_basic_block();
            self.set_current_block(loop_cond);
            let Some(cond_reg) = self.lower_expr(cond) else {
                self.add_diagnostic(Diagnostic::lowering(
                    self.source_file.path.clone(),
                    cond.id,
                    IRError::Unknown(format!("Cannot lower loop condition {cond:?}")),
                ));
                return None;
            };

            self.push_instr(Instr::Branch {
                cond: cond_reg,
                true_target: loop_entry,
                false_target: loop_exit,
            });

            Some(loop_cond)
        } else {
            None
        };

        self.loop_exits.push(loop_exit);

        let jump_target = loop_cond.unwrap_or(loop_entry);
        self.set_current_block(current_block);
        self.push_instr(Instr::Jump(jump_target));
        self.set_current_block(loop_entry);
        self.lower_expr(body);
        self.push_instr(Instr::Jump(jump_target));

        self.loop_exits.pop();
        self.set_current_block(loop_exit);

        None
    }

    fn lower_string(&mut self, _expr_id: &TypedExpr, string: String) -> Option<Register> {
        // Allocate the storage
        let chars_bytes = string.as_bytes();
        let static_addr = self.push_constant(IRConstantData::RawBuffer(chars_bytes.to_vec()));

        let string_struct_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: string_struct_reg,
            ty: IRType::string(),
            count: None,
        });

        let length_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: length_reg,
            base: string_struct_reg,
            ty: IRType::string(),
            index: IRValue::ImmediateInt(0),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: IRValue::ImmediateInt(chars_bytes.len() as i64),
            location: length_reg,
        });

        let capacity_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: capacity_reg,
            base: string_struct_reg,
            ty: IRType::string(),
            index: IRValue::ImmediateInt(1),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: IRValue::ImmediateInt(chars_bytes.len() as i64),
            location: capacity_reg,
        });

        let storage_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: storage_reg,
            base: string_struct_reg,
            ty: IRType::string(),
            index: IRValue::ImmediateInt(2),
        });
        let static_ptr_reg = self.allocate_register();
        self.push_instr(Instr::Const {
            dest: static_ptr_reg,
            ty: IRType::RawBuffer,
            val: IRValue::ImmediateInt(static_addr as i64),
        });
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: static_ptr_reg.into(),
            location: storage_reg,
        });

        Some(string_struct_reg)
    }

    fn lower_array(&mut self, typed_expr: &TypedExpr, items: &[TypedExpr]) -> Option<Register> {
        let Ty::Struct(_sym, els) = &typed_expr.ty else {
            self.push_err("Invalid array type", typed_expr.id);
            return None;
        };

        let ty = els.last()?.to_ir(self);

        // Allocate the array
        let array_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: array_reg,
            ty: IRType::array(ty.clone()),
            count: None,
        });

        // Set the array's count
        let count_reg = self.allocate_register();
        self.push_instr(Instr::ConstantInt(count_reg, items.len() as i64));
        let count_ptr_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: count_ptr_reg,
            base: array_reg,
            ty: IRType::array(ty.clone()),
            index: IRValue::ImmediateInt(0),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: count_reg.into(),
            location: count_ptr_reg,
        });

        // Set the array's capacity
        let capacity_reg = self.allocate_register();
        self.push_instr(Instr::ConstantInt(capacity_reg, items.len() as i64));
        let capacity_ptr_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: capacity_ptr_reg,
            base: array_reg,
            ty: IRType::array(ty.clone()),
            index: IRValue::ImmediateInt(1),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: capacity_reg.into(),
            location: capacity_ptr_reg,
        });

        // Alloc the array's storage
        let storage_ptr_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: storage_ptr_reg,
            base: array_reg,
            ty: IRType::array(ty.clone()),
            index: IRValue::ImmediateInt(2),
        });
        let storage_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: storage_reg,
            ty: IRType::Int,
            count: Some(IRValue::Register(count_reg)),
        });
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: storage_reg.into(),
            location: storage_ptr_reg,
        });

        if items.is_empty() {
            let loaded = self.allocate_register();
            self.push_instr(Instr::Load {
                dest: loaded,
                ty: IRType::array(ty.clone()),
                addr: array_reg,
            });
            return Some(loaded);
        }

        for (i, item) in items.iter().enumerate() {
            let lowered_item = self.lower_expr(item)?;
            let item_reg = self.allocate_register();
            let item_ty = item.ty.to_ir(self);
            self.push_instr(Instr::GetElementPointer {
                dest: item_reg,
                base: storage_reg,
                ty: IRType::TypedBuffer {
                    element: item_ty.clone().into(),
                },
                index: IRValue::ImmediateInt(i as i64),
            });
            self.push_instr(Instr::Store {
                ty: item_ty,
                val: lowered_item.into(),
                location: item_reg,
            });
        }

        Some(array_reg)
    }

    fn lower_struct(
        &mut self,
        typed_expr: &TypedExpr,
        struct_id: SymbolID,
        body: &TypedExpr,
    ) -> Option<Register> {
        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(&struct_id).cloned() else {
            self.add_diagnostic(Diagnostic::lowering(
                self.source_file.path.clone(),
                typed_expr.id,
                IRError::Unknown(format!(
                    "Could not resolve struct for symbol: {struct_id:?}"
                )),
            ));
            return None;
        };

        for initializer in &struct_def.initializers {
            let Some(typed_initializer) = self.source_file.typed_expr(initializer.expr_id).cloned()
            else {
                tracing::error!("didn't get initializer");
                return None;
            };

            self.lower_expr(&typed_initializer);

            // TODO this is awkward
            if let Some(init_func) = self.lowered_functions.last() {
                let cfg = ControlFlowGraph::new(init_func);
                let pass = DefiniteInitizationPass::new(struct_def.clone());
                match pass.run(init_func, &cfg) {
                    Ok(_) => (),
                    Err(e) => {
                        self.add_diagnostic(Diagnostic::lowering(
                            self.source_file.path.clone(),
                            initializer.expr_id,
                            e,
                        ));
                    }
                }
            }
        }

        let Expr::Block(member_exprs) = &body.expr else {
            self.add_diagnostic(Diagnostic::lowering(
                self.source_file.path.clone(),
                body.id,
                IRError::Unknown("Did not get struct body".into()),
            ));
            return None;
        };

        for member in member_exprs.clone() {
            match &member.expr {
                Expr::Func {
                    name: Some(name), ..
                } => {
                    self.lower_method(&member, name);
                }
                Expr::Init(..) | Expr::Property { .. } => {
                    // These are handled by the StructDef or the first loop; ignore them here.
                    continue;
                }
                _ => {
                    tracing::warn!("unhandled struct member: {:?}", member.expr);
                    continue;
                }
            }
        }

        self.register_global(&struct_id, SymbolValue::Struct(struct_def));

        None
    }

    fn lower_extend(&mut self, type_id: SymbolID, body: &TypedExpr) -> Option<Register> {
        let Some(type_def) = self.env.lookup_type(&type_id).cloned() else {
            self.add_diagnostic(Diagnostic::lowering(
                self.source_file.path.clone(),
                body.id,
                IRError::Unknown(format!("Could not resolve type for symbol: {type_id:?}")),
            ));
            return None;
        };

        tracing::trace!("Lowering extension for {type_def:?}");

        let Expr::Block(member_exprs) = &body.expr else {
            self.add_diagnostic(Diagnostic::lowering(
                self.source_file.path.clone(),
                body.id,
                IRError::Unknown("Did not get extension body".into()),
            ));
            return None;
        };

        for member in member_exprs.clone() {
            match &member.expr {
                Expr::Func {
                    name: Some(name), ..
                } => {
                    self.lower_method(&member, name);
                }
                Expr::Init(..) | Expr::Property { .. } => {
                    // These are handled by the type defs; ignore them here.
                    continue;
                }
                _ => {
                    tracing::warn!("unhandled struct member: {:?}", member.expr);
                    continue;
                }
            }
        }

        None
    }

    fn setup_self_context(
        &mut self,
        symbol_id: &SymbolID,
        typed_func: &TypedExpr,
    ) -> Option<(IRType, TypeDef, TypedExpr, Register, Option<IRValue>)> {
        let Some(type_def) = self.env.lookup_type(symbol_id).cloned() else {
            tracing::error!("Cannot setup self context for {symbol_id:?}");
            return None;
        };

        let Expr::Func { params, body, .. } = &typed_func.expr else {
            tracing::error!("Typed expr not a func: {typed_func:?}");
            return None;
        };

        self.current_functions.push(CurrentFunction::new(Some(
            type_def.ty().to_ir(self).clone(),
        )));
        let block_id = self.new_basic_block();
        self.set_current_block(block_id);

        // Define our env
        let env = self.allocate_register();
        self.current_func_mut()?
            .register_symbol(*symbol_id, SymbolValue::Register(env));

        for param in params {
            let Expr::Parameter(resolved_name, _) = &param.expr else {
                self.push_err("Did not get parameter", param.id);
                return None;
            };

            let register = self.allocate_register();
            self.current_func_mut()?
                .register_symbol(resolved_name.0, SymbolValue::Register(register));
        }

        let ret = self.lower_block(body);

        Some((
            type_def.ty().to_ir(self),
            type_def,
            typed_func.clone(),
            env,
            ret.map(IRValue::Register),
        ))
    }

    fn lower_init(&mut self, symbol_id: &SymbolID, func_id: &TypedExpr) -> Option<Register> {
        let (ty, type_def, typed_func, env, _) = self.setup_self_context(symbol_id, func_id)?;

        let loaded_reg = self.allocate_register();
        self.push_instr(Instr::Load {
            dest: loaded_reg,
            ty: ty.clone(),
            addr: env,
        });

        self.push_instr(Instr::Ret(ty.clone(), Some(loaded_reg.into())));

        let Ty::Func(params, _ret, generics) = typed_func.ty else {
            return None;
        };

        // Override func type for init to always return the struct
        let init_func_ty = Ty::Func(params, Ty::Pointer.into(), generics);

        let name_str = type_def.name();
        let current_function = self.current_functions.pop()?;

        let func = current_function.export(
            init_func_ty.to_ir(self),
            ResolvedName(*symbol_id, format!("{name_str}_init")).mangled(&init_func_ty),
            Some(type_def.ty().to_ir(self)),
            Some(env),
            &self.source_file,
        );

        self.lowered_functions.push(func.clone());

        Some(env)
    }

    fn lower_method(&mut self, func_id: &TypedExpr, name: &ResolvedName) -> Option<Register> {
        let (_ty, type_def, typed_func, env, ret) = self.setup_self_context(&name.0, func_id)?;

        let (Ty::Func(_, ret_ty, _)
        | Ty::Closure {
            func: box Ty::Func(_, ret_ty, _),
            ..
        }) = &typed_func.ty
        else {
            self.push_err(
                &format!("Could not get return type for method: {typed_func:?}"),
                func_id.id,
            );
            return None;
        };

        self.push_instr(Instr::Ret(ret_ty.to_ir(self), ret));

        let current_function = self.current_functions.pop()?;
        let func = current_function.export(
            typed_func.ty.to_ir(self),
            ResolvedName(name.0, format!("{}_{}", type_def.name(), name.1)).mangled(&typed_func.ty),
            Some(type_def.ty().to_ir(self)),
            Some(env),
            &self.source_file,
        );

        self.lowered_functions.push(func.clone());

        None
    }

    fn lower_method_stub(
        &mut self,
        ty: &Ty,
        protocol_name: &ResolvedName,
        name: &ResolvedName,
    ) -> Option<Register> {
        let Ty::Func(mut params, ret, generics) = ty.clone() else {
            unreachable!()
        };

        let type_var = Ty::TypeVar(TypeVarID::new(0, TypeVarKind::SelfVar(name.0)));

        // Insert the self env param
        params.insert(0, type_var.clone());

        let stub_function = IRFunction {
            ty: Ty::Func(params, ret, generics).to_ir(self),
            name: format!("@_{}_{}_{}", protocol_name.0.0, protocol_name.1, name.1),
            blocks: vec![],
            env_ty: Some(type_var.to_ir(self)),
            env_reg: None,
            size: 0,
            debug_info: Default::default(),
        };

        self.lowered_functions.push(stub_function);

        None
    }

    fn lower_function(&mut self, typed_expr: &TypedExpr) -> Option<Register> {
        let Expr::Func {
            ref name,
            ref params,
            ref body,
            ref captures,
            ref generics,
            ..
        } = typed_expr.expr
        else {
            self.push_err("Did not get typed expr", typed_expr.id);
            return None;
        };

        let name = self.resolve_name(name.clone());
        let generics: Vec<IRType> = generics.iter().map(|t| t.ty.to_ir(self)).collect();

        // If the only capture is the func itself, we don't need to allocate a closure

        let ret = if captures.is_empty() {
            let fn_ptr = self.allocate_register();
            self.push_instr(Instr::Ref(
                fn_ptr,
                typed_expr.ty.to_ir(self),
                RefKind::Func(name.mangled(&typed_expr.ty)),
            ));

            self.current_functions.push(CurrentFunction::new(None));
            let id = self.new_basic_block();
            self.set_current_block(id);

            Some(fn_ptr)
        } else {
            let closure_ptr = self.allocate_register();
            self.push_instr(Instr::Alloc {
                dest: closure_ptr,
                count: None,
                ty: IRType::closure(),
            });

            self.current_func_mut()?
                .register_symbol(name.symbol_id(), SymbolValue::Register(closure_ptr));

            let (capture_types, capture_registers) = if let Ty::Closure {
                captures: capture_types,
                ..
            } = &typed_expr.ty
            {
                let self_symbol = name.0;

                // Define an environment object for our captures. If there aren't any captures we don't care,
                // we're going to do it anyway. Maybe we can optimize it out later? I don't know if we'll have time.
                let mut capture_registers = vec![];
                let mut captured_ir_types = vec![];
                for (i, capture) in captures.iter().enumerate() {
                    let Some(SymbolValue::Register(register)) = self.lookup_register(capture)
                    else {
                        self.push_err(
                            "don't know how to handle captured captures yet",
                            typed_expr.id,
                        );
                        return None;
                    };
                    capture_registers.push(*register);

                    if *capture == self_symbol {
                        captured_ir_types.push(IRType::POINTER);
                    } else {
                        let capture_ty = self
                            .env
                            .lookup_symbol(&capture_types[i])
                            .cloned()
                            .unwrap_or_else(|_| {
                                // This is gnarly
                                let sym = capture_types[i];
                                let Some(info) = self.symbol_table.get(&sym) else {
                                    return Scheme::new(Ty::Void, vec![], vec![]);
                                };
                                let Some(typed_expr) = self.source_file.typed_expr(info.expr_id)
                                else {
                                    return Scheme::new(Ty::Void, vec![], vec![]);
                                };

                                Scheme::new(typed_expr.ty.clone(), vec![], vec![])
                            })
                            .ty();
                        captured_ir_types.push(capture_ty.to_ir(self));
                    }
                }

                (captured_ir_types, capture_registers)
            } else {
                (vec![], vec![])
            };

            let environment_type = IRType::Struct(SymbolID::ENV, capture_types.clone(), vec![]);

            self.fill_closure(
                closure_ptr,
                RefKind::Func(name.mangled(&typed_expr.ty)),
                typed_expr.ty.to_ir(self),
                capture_types.clone(),
                capture_registers,
                generics,
            );

            self.current_functions
                .push(CurrentFunction::new(Some(environment_type)));
            let id = self.new_basic_block();
            self.set_current_block(id);

            // Now that we're in the block, register the captures
            for (i, capture) in captures.iter().enumerate() {
                self.current_func_mut()?
                    .register_symbol(*capture, SymbolValue::Capture(i, capture_types[i].clone()));
            }

            Some(closure_ptr)
        };

        tracing::trace!("lowering {name:?}");

        let Expr::Block(body_exprs) = &body.expr else {
            self.push_err("Did not get body", body.id);
            return None;
        };

        let env_reg = if captures.is_empty() {
            None
        } else {
            Some(self.allocate_register()) // Set aside our env register
        };

        for param in params {
            let Expr::Parameter(name, _) = &param.expr else {
                self.push_err("didn't get parameter", param.id);
                return None;
            };

            let register = self.current_func_mut()?.registers.allocate();
            self.current_func_mut()?
                .register_symbol(name.symbol_id(), SymbolValue::Register(register));
        }

        for (i, body_expr) in body_exprs.iter().enumerate() {
            let ret = if let Some(reg) = self.lower_expr(body_expr) {
                (body_expr.ty.to_ir(self), Some(reg.into()))
            } else {
                (IRType::Void, None)
            };

            if i == body_exprs.len() - 1 {
                let ty = if matches!(ret.0, IRType::Func(_, _)) {
                    // we don't pass around functions, we pass around pointers (closures)
                    IRType::POINTER
                } else {
                    ret.0
                };

                self.push_instr(Instr::Ret(ty, ret.1));
            }
        }

        let current_function = self.current_functions.pop()?;
        let env_ty = current_function.env_ty.clone();
        let func = current_function.export(
            typed_expr.ty.to_ir(self),
            name.mangled(&typed_expr.ty),
            env_ty,
            env_reg,
            &self.source_file,
        );

        self.lowered_functions.push(func.clone());

        ret
    }

    fn lower_match(
        &mut self,
        scrutinee: &TypedExpr,
        arms: &[TypedExpr],
        ty: &Ty,
    ) -> Option<Register> {
        let scrutinee_reg = self.lower_expr(scrutinee)?;
        let merge_block_id = self.new_basic_block();

        // Pre-allocate all the blocks where we will check the condition for each arm.
        let arm_cond_blocks: Vec<_> = (0..arms.len()).map(|_| self.new_basic_block()).collect();

        // Jump to the first condition
        self.push_instr(Instr::Jump(arm_cond_blocks[0]));

        let fail_block_id = self.new_basic_block();
        self.set_current_block(fail_block_id);
        self.push_instr(Instr::Unreachable);

        let mut predecessors = vec![];
        for (i, arm) in arms.iter().enumerate() {
            predecessors.push(self.lower_match_arm(
                arm,
                &scrutinee_reg,
                merge_block_id,
                arm_cond_blocks[i],
                arm_cond_blocks.get(i + 1).cloned().unwrap_or(fail_block_id),
            ));
        }

        self.set_current_block(merge_block_id);

        let phi_reg = self.allocate_register();
        self.push_instr(Instr::Phi(
            phi_reg,
            ty.to_ir(self),
            PhiPredecessors(predecessors),
        ));

        Some(phi_reg)
    }

    fn lower_match_arm(
        &mut self,
        typed_arm: &TypedExpr,
        scrutinee: &Register,
        merge_block_id: BasicBlockID,
        cond_block_id: BasicBlockID,
        else_block_id: BasicBlockID,
    ) -> (Register, BasicBlockID) {
        let Expr::MatchArm(pattern_id, body_id) = &typed_arm.expr else {
            self.push_err("Did not get match arm", typed_arm.id);
            return (Register(0), BasicBlockID(u32::MAX));
        };

        let then_block_id = self.new_basic_block();

        self.lower_pattern_and_bind(
            pattern_id,
            scrutinee,
            cond_block_id,
            then_block_id,
            else_block_id,
        );
        self.set_current_block(then_block_id);
        let Some(body_ret_reg) = self.lower_expr(body_id) else {
            tracing::error!("Did not get body return: {:?}", body_id);
            return (Register(0), BasicBlockID(u32::MAX));
        };

        // After evaluating body, jump to the merge
        self.push_instr(Instr::Jump(merge_block_id));

        (body_ret_reg, then_block_id)
    }

    fn lower_pattern_and_bind(
        &mut self,
        pattern_typed_expr: &TypedExpr,
        scrutinee_reg: &Register,
        cond_block_id: BasicBlockID,
        then_block_id: BasicBlockID,
        else_block_id: BasicBlockID,
    ) -> Option<()> {
        let Expr::ParsedPattern(pattern) = &pattern_typed_expr.expr else {
            return None;
        };

        self.set_current_block(cond_block_id);
        match pattern {
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                let (enum_id, enum_generics) = {
                    let mut id = None;
                    let mut generics = None;

                    if let Ty::Enum(enum_id, params) = &pattern_typed_expr.ty {
                        id = Some(enum_id);
                        generics = Some(params);
                    }

                    if let Ty::EnumVariant(enum_id, params) = &pattern_typed_expr.ty {
                        id = Some(enum_id);
                        generics = Some(params);
                    }

                    (id, generics)
                };

                let (Some(enum_id), Some(enum_generics)) = (enum_id, enum_generics) else {
                    self.push_err("Could not determine enum generics", pattern_typed_expr.id);
                    return None;
                };

                let Some(TypeDef::Enum(type_def)) = self.env.lookup_type(enum_id).cloned() else {
                    self.push_err("Could not determine enum", pattern_typed_expr.id);
                    return None;
                };

                /* ... find variant by name in type_def ... */
                let Some((tag, variant_def)) = type_def.tag_with_variant_for(variant_name) else {
                    self.push_err("message", pattern_typed_expr.id);
                    return None;
                };

                // 2. Get the tag of the scrutinee.
                let tag_reg = self.allocate_register();
                self.push_instr(Instr::GetEnumTag(tag_reg, *scrutinee_reg));

                let expected_tag_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(expected_tag_reg, tag as i64));
                let tags_match_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    tags_match_reg,
                    IRType::Int,
                    tag_reg,
                    expected_tag_reg,
                ));

                self.push_instr(Instr::Branch {
                    cond: tags_match_reg,
                    true_target: then_block_id,
                    false_target: else_block_id,
                });

                self.set_current_block(then_block_id);

                for (i, field_pattern) in fields.iter().enumerate() {
                    if let Expr::ParsedPattern(Pattern::Bind(ResolvedName(symbol_id, _))) =
                        &field_pattern.expr
                    {
                        let value_reg = self.allocate_register();

                        // We need to figure out the type of the value. This feels clumsy.
                        let Ty::EnumVariant(_, values) = variant_def.ty.clone() else {
                            unreachable!();
                        };
                        let ty = match values[i].clone() {
                            Ty::TypeVar(var) => {
                                let Some(generic_pos) = type_def
                                    .type_parameters
                                    .iter()
                                    .position(|t| t.type_var == var)
                                // t == var.0)
                                else {
                                    self.push_err(
                                        format!("unable to determine enum generic: {var:?}")
                                            .as_str(),
                                        field_pattern.id,
                                    );

                                    return None;
                                };

                                enum_generics[generic_pos].clone()
                            }
                            other => other,
                        };

                        self.push_instr(Instr::GetEnumValue(
                            value_reg,
                            ty.to_ir(self),
                            *scrutinee_reg,
                            tag,
                            i as u16,
                        ));
                        self.current_func_mut()?
                            .register_symbol(*symbol_id, SymbolValue::Register(value_reg));
                    }
                    // Handle nested patterns recursively here.
                }
            }
            Pattern::LiteralInt(val) => {
                let literal_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(literal_reg, val.parse().unwrap_or(0)));
                let is_eq_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    is_eq_reg,
                    IRType::Int,
                    *scrutinee_reg,
                    literal_reg,
                ));

                self.push_instr(Instr::Branch {
                    cond: is_eq_reg,
                    true_target: then_block_id,
                    false_target: else_block_id,
                });
            }
            Pattern::LiteralFloat(_) => (),
            Pattern::LiteralTrue => (),
            Pattern::LiteralFalse => (),
            Pattern::Bind(_name) => (),
            Pattern::Wildcard => (),
        }

        Some(())
    }

    fn _lower_pattern(&mut self, pattern_typed_expr: &TypedExpr) -> Option<Register> {
        let Expr::ParsedPattern(pattern) = &pattern_typed_expr.expr else {
            self.push_err(
                "Didn't get pattern for match arm: {pattern_typed_expr:?}",
                pattern_typed_expr.id,
            );
            return None;
        };

        match pattern {
            Pattern::Bind(_) => None,
            Pattern::LiteralInt(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(reg, str::parse(val).ok()?));
                Some(reg)
            }
            Pattern::LiteralFloat(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantFloat(reg, str::parse(val).ok()?));
                Some(reg)
            }
            Pattern::LiteralTrue => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, true));
                Some(reg)
            }
            Pattern::LiteralFalse => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, false));
                Some(reg)
            }
            Pattern::Wildcard => None,
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Ty::Enum(enum_id, _) = pattern_typed_expr.ty else {
                    self.push_err(
                        format!("didn't get pattern type: {:?}", pattern_typed_expr.ty).as_str(),
                        pattern_typed_expr.id,
                    );
                    return None;
                };
                let Some(TypeDef::Enum(type_def)) = self.env.lookup_type(&enum_id).cloned() else {
                    self.push_err(
                        format!("didn't get type def for {enum_id:?}").as_str(),
                        pattern_typed_expr.id,
                    );
                    return None;
                };

                let (tag, variant) = type_def.variants.iter().enumerate().find_map(|(i, v)| {
                    if &v.name == variant_name {
                        Some((i, v))
                    } else {
                        None
                    }
                })?;

                let dest = self.allocate_register();
                let Ty::EnumVariant(_, values) = &variant.ty else {
                    self.push_err("did not get enum variant values", pattern_typed_expr.id);
                    return Some(dest);
                };
                let args = RegisterList(
                    fields
                        .iter()
                        .zip(values)
                        .filter_map(|(f, ty)| {
                            Some(TypedRegister {
                                ty: ty.to_ir(self),
                                register: self._lower_pattern(f)?,
                            })
                        })
                        .collect(),
                );
                self.push_instr(Instr::TagVariant(
                    dest,
                    pattern_typed_expr.ty.to_ir(self),
                    tag as u16,
                    args,
                ));

                Some(dest)
            } // _ => todo!("{:?}", pattern),
        }
    }

    fn lower_member(
        &mut self,
        receiver: &Option<&TypedExpr>,
        typed_expr: &TypedExpr,
        name: &str,
        is_lvalue: bool,
    ) -> Option<Register> {
        if let Ty::Enum(sym, _generics) = &typed_expr.ty {
            return self.lower_enum_construction(typed_expr, *sym, name, &typed_expr.ty, &[]);
        }

        if let Ty::EnumVariant(sym, _generics) = &typed_expr.ty {
            return self.lower_enum_construction(typed_expr, *sym, name, &typed_expr.ty, &[]);
        }

        let Some(receiver) = receiver else {
            unreachable!("we should have a receiver since it's not an enum");
        };

        let Some(receiver_reg) = self.lower_expr(receiver) else {
            self.push_err(
                &format!(
                    "did not get receiver register: {:?}, typed_expr: {typed_expr:?}",
                    receiver.id
                ),
                receiver.id,
            );
            return None;
        };

        match &receiver.ty {
            Ty::Struct(struct_id, _) => {
                let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(struct_id).cloned()
                else {
                    unreachable!("didn't get struct def");
                };

                if let Some(index) = struct_def.properties.iter().position(|p| p.name == name) {
                    let member_reg = self.allocate_register();

                    self.push_instr(Instr::GetElementPointer {
                        dest: member_reg,
                        base: receiver_reg,
                        ty: receiver.ty.to_ir(self).clone(),
                        index: IRValue::ImmediateInt(index as i64),
                    });

                    if is_lvalue {
                        return Some(member_reg);
                    } else {
                        let member_loaded_reg = self.allocate_register();
                        self.push_instr(Instr::Load {
                            dest: member_loaded_reg,
                            addr: member_reg,
                            ty: typed_expr.ty.to_ir(self),
                        });

                        return Some(member_loaded_reg);
                    }
                }

                if let Some(method) = struct_def.methods.iter().find(|m| m.name == name) {
                    let func = self.allocate_register();
                    let name = ResolvedName(*struct_id, format!("{}_{name}", struct_def.name_str))
                        .mangled(&method.ty);
                    self.push_instr(Instr::Ref(
                        func,
                        typed_expr.ty.to_ir(self),
                        RefKind::Func(name),
                    ));
                    return Some(func);
                }

                None
            }
            _ => {
                self.push_err(format!("Member not lowered {name}").as_str(), typed_expr.id);
                None
            }
        }
    }

    fn lower_enum_construction(
        &mut self,
        typed_expr: &TypedExpr,
        enum_id: SymbolID,
        variant_name: &str,
        ty: &Ty,
        args: &[TypedRegister],
    ) -> Option<Register> {
        let Some(TypeDef::Enum(type_def)) = self.env.lookup_type(&enum_id).cloned() else {
            self.push_err(
                format!("didn't get type def for {enum_id:?}").as_str(),
                typed_expr.id,
            );
            return None;
        };

        let mut tag: Option<u16> = None;

        for (i, var) in type_def.variants.iter().enumerate() {
            if var.name != variant_name {
                continue;
            }

            tag = Some(i as u16);
        }

        let Some(tag) = tag else {
            self.push_err("did not find variant for tag", typed_expr.id);
            return None;
        };

        let dest = self.allocate_register();
        self.push_instr(Instr::TagVariant(
            dest,
            ty.to_ir(self),
            tag,
            RegisterList(args.to_vec()),
        ));

        Some(dest)
    }

    fn lower_return(
        &mut self,
        typed_expr: &TypedExpr,
        rhs: &Option<Box<TypedExpr>>,
    ) -> Option<Register> {
        if let Some(rhs) = rhs {
            let register = self.lower_expr(rhs)?;
            let ir_type = typed_expr.ty.to_ir(self);
            self.push_instr(Instr::Ret(ir_type, Some(register.into())));
            Some(register)
        } else {
            self.push_instr(Instr::Ret(IRType::Void, None));
            None
        }
    }

    fn lower_literal(&mut self, typed_expr: &TypedExpr) -> Option<Register> {
        let register = self.allocate_register();
        match &typed_expr.expr {
            Expr::LiteralInt(val) => {
                self.push_instr(Instr::ConstantInt(register, str::parse(val).ok()?));
                Some(register)
            }
            Expr::LiteralFloat(val) => {
                self.push_instr(Instr::ConstantFloat(register, str::parse(val).ok()?));
                Some(register)
            }
            Expr::LiteralFalse => {
                self.push_instr(Instr::ConstantBool(register, false));
                Some(register)
            }
            Expr::LiteralTrue => {
                self.push_instr(Instr::ConstantBool(register, true));
                Some(register)
            }
            _ => None,
        }
    }

    fn lower_binary_op(&mut self, typed_expr: &TypedExpr) -> Option<Register> {
        let Expr::Binary(lhs, op, rhs) = &typed_expr.expr else {
            self.push_err("did get binary expr", typed_expr.id);
            return None;
        };

        let operand_ty = lhs.ty.clone();

        let operand_1 = self.lower_expr(lhs)?;
        let operand_2 = self.lower_expr(rhs)?;
        let return_reg = self.allocate_register();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Minus => Instr::Sub(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Star => Instr::Mul(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Slash => Instr::Div(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            BangEquals => Instr::Ne(return_reg, operand_ty.to_ir(self), operand_1, operand_2),
            EqualsEquals => Instr::Eq(return_reg, operand_ty.to_ir(self), operand_1, operand_2),

            Less => Instr::LessThan(return_reg, operand_ty.to_ir(self), operand_1, operand_2),
            LessEquals => {
                Instr::LessThanEq(return_reg, operand_ty.to_ir(self), operand_1, operand_2)
            }
            Greater => Instr::GreaterThan(return_reg, operand_ty.to_ir(self), operand_1, operand_2),
            GreaterEquals => {
                Instr::GreaterThanEq(return_reg, operand_ty.to_ir(self), operand_1, operand_2)
            }
            _ => {
                self.push_err(
                    format!("Cannot lower binary operation: {op:?}").as_str(),
                    typed_expr.id,
                );
                return None;
            }
        };

        self.push_instr(instr);

        Some(return_reg)
    }

    fn lower_assignment(
        &mut self,
        typed_lhs: &TypedExpr,
        typed_rhs: &TypedExpr,
    ) -> Option<Register> {
        let rhs = self.lower_expr(typed_rhs)?;

        match &typed_lhs.expr {
            Expr::Let(ResolvedName(symbol_id, _), _) => {
                self.current_func_mut()?
                    .register_symbol(*symbol_id, rhs.into());
                Some(rhs)
            }
            Expr::Variable(ResolvedName(symbol, _)) => {
                let value = self.lookup_register(symbol)?.clone();

                match value {
                    SymbolValue::Register(reg) => {
                        self.push_instr(Instr::StoreLocal(reg, typed_rhs.ty.to_ir(self), rhs));
                        None
                    }
                    SymbolValue::Capture(idx, ty) => {
                        let capture_ptr = self.allocate_register();
                        let env_ty = self.current_func()?.env_ty.clone();
                        self.push_instr(Instr::GetElementPointer {
                            dest: capture_ptr,
                            base: Register(0),
                            ty: env_ty?,
                            index: IRValue::ImmediateInt(idx as i64),
                        });
                        self.push_instr(Instr::Store {
                            ty: ty.clone(),
                            val: rhs.into(),
                            location: capture_ptr,
                        });

                        Some(rhs)
                    }
                    SymbolValue::Struct(struct_def) => {
                        unreachable!("Cannot assign to struct: {:?}", struct_def)
                    }
                    SymbolValue::FuncRef(name) => {
                        unreachable!("Cannot assign to func: {:?}", name)
                    }
                }
            }
            Expr::Member(Some(box receiver), name) => {
                if let Some(dest) = self.lower_member(&Some(receiver), typed_lhs, name, true) {
                    self.push_instr(Instr::Store {
                        ty: typed_lhs.ty.to_ir(self),
                        val: rhs.into(),
                        location: dest,
                    });
                    Some(rhs)
                } else {
                    None
                }
            }
            _ => {
                self.push_err(
                    format!("don't know how to lower: {typed_lhs:?}").as_str(),
                    typed_lhs.id,
                );
                None
            }
        }
    }

    fn lower_block(&mut self, typed_expr: &TypedExpr) -> Option<Register> {
        let Expr::Block(exprs) = &typed_expr.expr else {
            unreachable!()
        };

        if exprs.is_empty() {
            return None;
        }

        for (i, id) in exprs.iter().enumerate() {
            let reg = self.lower_expr(id);
            if i == exprs.len() - 1 {
                return reg;
            }
        }

        None
    }

    fn lower_variable(&mut self, typed_expr: &TypedExpr, name: &ResolvedName) -> Option<Register> {
        let ResolvedName(symbol_id, _) = name;
        let value = self.lookup_register(symbol_id)?;
        match value.clone() {
            SymbolValue::Register(reg) => Some(reg),
            SymbolValue::Capture(idx, ty) => {
                let env_ptr = self.allocate_register();
                self.push_instr(Instr::GetElementPointer {
                    dest: env_ptr,
                    base: Register(0),
                    ty: IRType::closure(),
                    index: IRValue::ImmediateInt(idx as i64),
                });

                let reg = self.allocate_register();
                self.push_instr(Instr::Load {
                    dest: reg,
                    ty: ty.clone(),
                    addr: env_ptr,
                });

                Some(reg)
            }
            _ => {
                self.push_err(
                    format!("unable to lower: {value:?}").as_str(),
                    typed_expr.id,
                );
                None
            }
        }
    }

    fn lower_if(&mut self, typed_expr: &TypedExpr) -> Option<Register> {
        let Expr::If(cond, conseq, alt) = &typed_expr.expr else {
            unreachable!()
        };

        let cond_reg = self.lower_expr(cond)?;
        let then_id = self.new_basic_block();

        let mut else_reg: Option<Register> = None;
        let else_id: Option<BasicBlockID> = if alt.is_some() {
            Some(self.new_basic_block())
        } else {
            None
        };
        let merge_id = self.new_basic_block(); // All paths merge here

        self.push_instr(Instr::Branch {
            cond: cond_reg,
            true_target: then_id,
            false_target: else_id.unwrap_or(merge_id),
        });

        self.set_current_block(then_id);
        let then_reg = self.lower_expr(conseq);
        self.push_instr(Instr::Jump(merge_id));

        if let Some(alt) = alt {
            self.set_current_block(else_id?);
            else_reg = self.lower_expr(alt);
            self.push_instr(Instr::Jump(merge_id));
        }

        self.current_func_mut()?.set_current_block(merge_id).ok()?;

        let phi_dest_reg = self.allocate_register();
        let ir_type = typed_expr.ty.to_ir(self);
        let mut predecessors = vec![];

        if let Some(then_reg) = then_reg {
            predecessors.push((then_reg, then_id));
        };

        if let Some(else_reg) = else_reg
            && let Some(else_id) = else_id
        {
            predecessors.push((else_reg, else_id));
        }

        if predecessors.len() <= 1 {
            None
        } else {
            self.push_instr(Instr::Phi(
                phi_dest_reg,
                ir_type,
                PhiPredecessors(predecessors),
            ));

            Some(phi_dest_reg)
        }
    }

    fn lower_call(
        &mut self,
        callee_typed_expr: &TypedExpr,
        ret_ty: &IRType,
        args: &[TypedExpr],
    ) -> Option<Register> {
        let ty = &callee_typed_expr.ty;
        let (Ty::Func(params, _, _)
        | Ty::Closure {
            func: box Ty::Func(params, _, _),
            ..
        }
        | Ty::Init(_, params)) = &callee_typed_expr.ty
        else {
            tracing::error!("didn't get callable: {callee_typed_expr:?}");
            return None;
        };

        // Handle builtins
        if let Expr::Variable(ResolvedName(symbol, _)) = &callee_typed_expr.expr
            && crate::builtins::is_builtin_func(symbol)
        {
            return match super::builtins::lower_builtin(symbol, callee_typed_expr, args, self) {
                Ok(res) => return res,
                Err(e) => {
                    self.push_err(e.message().as_str(), callee_typed_expr.id);
                    None
                }
            };
        }

        let mut arg_registers = vec![];
        for (i, arg) in args.iter().enumerate() {
            if let Some(arg_reg) = self.lower_expr(arg) {
                arg_registers.push(TypedRegister {
                    ty: params[i].to_ir(self),
                    register: arg_reg,
                });
            } else {
                self.push_err(
                    "Argument expression did not produce a value for call",
                    arg.id,
                );
                continue;
            }
        }

        // Handle enum variant construction
        if let Ty::Enum(enum_id, _) = &ty {
            let Expr::Member(_, variant_name) = &callee_typed_expr.expr else {
                self.push_err("didn't get member expr for enum call", callee_typed_expr.id);
                return None;
            };

            return self.lower_enum_construction(
                callee_typed_expr,
                *enum_id,
                variant_name,
                ty,
                &arg_registers,
            );
        }

        // Handle enum variant construction
        if let Ty::EnumVariant(enum_id, _) = &ty {
            let Expr::Member(_, variant_name) = &callee_typed_expr.expr else {
                self.push_err("didn't get member expr for enum call", callee_typed_expr.id);
                return None;
            };

            return self.lower_enum_construction(
                callee_typed_expr,
                *enum_id,
                variant_name,
                ty,
                &arg_registers,
            );
        }

        // Handle struct construction
        if let Ty::Init(struct_id, params) = &callee_typed_expr.ty {
            return self.lower_init_call(struct_id, ty, arg_registers, params);
        }

        // Handle method calls
        if let Expr::Member(receiver, name) = &callee_typed_expr.expr {
            return self.lower_method_call(
                callee_typed_expr,
                receiver,
                ret_ty,
                name,
                arg_registers,
            );
        }

        // Check to see if we can call this function directly (because its SymbolKind is FuncDef). If it is,
        // we can just call by name. Otherwise if it's something like SymbolKind::Local, we'll have to load
        // the callee from the register.
        if let Expr::Variable(name) = &callee_typed_expr.expr
            && let Some(name_info) = self.symbol_table.get(&name.symbol_id())
            && name_info.kind == SymbolKind::FuncDef
        {
            // Determine the underlying function type, whether it's a direct function or a closure.
            let (func_ty, is_closure) = match &callee_typed_expr.ty {
                Ty::Closure { func, .. } => (func.as_ref(), true),
                ty @ Ty::Func(..) => (ty, false),
                _ => {
                    self.push_err(
                        "Callee variable is not a function or closure",
                        callee_typed_expr.id,
                    );
                    return None;
                }
            };

            let callee_name = name.mangled(func_ty);

            if !is_closure {
                // We can skip all the closure environment ceremony
                let dest_reg = self.allocate_register();

                self.push_instr(Instr::Call {
                    dest_reg,
                    ty: ty.to_ir(self),
                    callee: Callee::Name(callee_name),
                    args: RegisterList(arg_registers),
                });

                return Some(dest_reg);
            }

            // First, get the register holding the pointer to the closure object itself.
            let Some(callee_reg) = self.lower_expr(callee_typed_expr) else {
                self.push_err(
                    &format!(
                        "Could not lower function variable to get its closure object: {callee_typed_expr:?}",
                    ),
                    callee_typed_expr.id,
                );
                return None;
            };

            // Now, load the environment pointer from the closure object.
            // The environment is the second element (index 1).
            let env_ptr = self.allocate_register();
            // let env_reg = self.allocate_register();
            self.push_instr(Instr::GetElementPointer {
                dest: env_ptr,
                base: callee_reg,
                ty: IRType::closure(),
                index: IRValue::ImmediateInt(1),
            });

            // Prepend the environment register to the argument list.
            arg_registers.insert(
                0,
                TypedRegister {
                    ty: IRType::POINTER,
                    register: env_ptr,
                },
            );

            // Finally, emit the direct call-by-name instruction.
            let dest_reg = self.allocate_register();
            self.push_instr(Instr::Call {
                dest_reg,
                ty: ty.to_ir(self),
                callee: Callee::Name(callee_name),
                args: RegisterList(arg_registers),
            });
            Some(dest_reg)
        } else {
            // Fallback for indirect calls (e.g., `(if c then f else g)()` ).
            // Here, the callee is not a static name, so we must use the original call-by-reference.
            let Some(callee_reg) = self.lower_expr(callee_typed_expr) else {
                self.push_err(
                    &format!("did not get callee: {callee_typed_expr:?}"),
                    callee_typed_expr.id,
                );
                return None;
            };

            let func_ptr = self.allocate_register();
            let func_reg = self.allocate_register();
            self.push_instr(Instr::GetElementPointer {
                dest: func_ptr,
                base: callee_reg,
                ty: IRType::closure(),
                index: IRValue::ImmediateInt(0),
            });
            self.push_instr(Instr::Load {
                dest: func_reg,
                ty: callee_typed_expr.ty.to_ir(self),
                addr: func_ptr,
            });

            let env_ptr = self.allocate_register();
            let env_reg = self.allocate_register();

            self.push_instr(Instr::GetElementPointer {
                dest: env_ptr,
                base: callee_reg,
                ty: IRType::closure(),
                index: IRValue::ImmediateInt(1),
            });
            self.push_instr(Instr::Load {
                dest: env_reg,
                ty: IRType::POINTER,
                addr: env_ptr,
            });

            arg_registers.insert(
                0,
                TypedRegister {
                    ty: IRType::POINTER,
                    register: env_reg,
                },
            );

            let dest_reg = self.allocate_register();
            let ir_type = ty.to_ir(self);
            self.push_instr(Instr::Call {
                ty: ir_type,
                dest_reg,
                callee: func_reg.into(),
                args: RegisterList(arg_registers),
            });

            Some(dest_reg)
        }
    }

    fn lower_init_call(
        &mut self,
        struct_id: &SymbolID,
        ty: &Ty,
        mut arg_registers: Vec<TypedRegister>,
        params: &[Ty],
    ) -> Option<Register> {
        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(struct_id).cloned() else {
            unreachable!()
        };

        let struct_ty = ty.to_ir(self);

        let struct_instance_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: struct_instance_reg,
            ty: struct_ty.clone(),
            count: None,
        });

        // Add the instance address as the first arg
        arg_registers.insert(
            0,
            TypedRegister {
                ty: IRType::POINTER,
                register: struct_instance_reg,
            },
        );

        let init_func_ty = Ty::Func(
            params.to_vec(),
            Box::new(ty.clone()),
            vec![], // No generics on init
        );
        let init_func_name = ResolvedName(*struct_id, format!("{}_init", struct_def.name_str))
            .mangled(&init_func_ty);

        // 3. Call the initializer function
        let initialized_struct_reg = self.allocate_register();
        self.push_instr(Instr::Call {
            dest_reg: initialized_struct_reg,
            ty: struct_ty,
            callee: Callee::Name(init_func_name),
            args: RegisterList(arg_registers),
        });

        Some(struct_instance_reg)
    }

    fn lower_method_call(
        &mut self,
        callee_typed_expr: &TypedExpr,
        receiver_ty: &Option<Box<TypedExpr>>,
        ret_ty: &IRType,
        name: &str,
        mut arg_registers: Vec<TypedRegister>,
    ) -> Option<Register> {
        let Some(receiver_ty) = receiver_ty else {
            tracing::error!("no receiver for member expr");
            return None;
        };

        let Some(receiver) = self.lower_expr(receiver_ty) else {
            tracing::error!("could not lower member receiver: {callee_typed_expr:?}");
            return None;
        };

        let type_var_id = if let IRType::TypeVar(type_var) = &receiver_ty.ty.to_ir(self) {
            Some(type_var.clone())
        } else {
            None
        };

        arg_registers.insert(
            0,
            TypedRegister {
                ty: IRType::Pointer { hint: type_var_id },
                register: receiver,
            },
        );

        let callee_name = match &receiver_ty.ty {
            Ty::Struct(struct_id, _) => {
                let struct_def = self.env.lookup_struct(struct_id)?;
                let method = struct_def.methods.iter().find(|m| m.name == name)?;
                Some(format!(
                    "@_{}_{}_{}",
                    struct_id.0, struct_def.name_str, method.name
                ))
            }
            Ty::Enum(enum_id, _) => {
                let def = self.env.lookup_enum(enum_id)?;
                let method = def.methods.iter().find(|m| m.name == name)?;
                Some(format!("@_{}_{}_{}", enum_id.0, def.name_str, method.name))
            }
            Ty::TypeVar(_type_var)
                if let conformances = self
                    .env
                    .constraints()
                    .iter()
                    .filter_map(|c| {
                        if let Constraint::ConformsTo { conformance, .. } = c {
                            Some(conformance)
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<&Conformance>>()
                    && !conformances.is_empty() =>
            {
                let mut result = None;
                for conformance in &conformances {
                    let protocol_def = self.env.lookup_protocol(&conformance.protocol_id)?;
                    if let Some(method) = protocol_def.methods.iter().find(|m| m.name == name) {
                        result = Some(format!(
                            "@_{}_{}_{}",
                            protocol_def.symbol_id.0, protocol_def.name_str, method.name
                        ));

                        break;
                    } else if let Some(method) = protocol_def
                        .method_requirements
                        .iter()
                        .find(|m| m.name == name)
                    {
                        result = Some(format!(
                            "@_{}_{}_{}",
                            protocol_def.symbol_id.0, protocol_def.name_str, method.name
                        ));

                        break;
                    }
                }

                result
            }
            _ => None,
        };

        let Some(callee_name) = callee_name else {
            self.push_err(
                &format!("Could not determine callee. Receiver: {receiver_ty:?}"),
                receiver_ty.id,
            );
            return None;
        };

        let result_reg = self.allocate_register();
        self.push_instr(Instr::Call {
            dest_reg: result_reg,
            ty: ret_ty.clone(),
            callee: Callee::Name(callee_name),
            args: RegisterList(arg_registers),
        });

        Some(result_reg)
    }

    /// Fills a pre-allocated closure with the given function reference and captures.
    ///
    /// This assumes `closure_ptr` has already been allocated with Instr::Alloc.
    fn fill_closure(
        &mut self,
        closure_ptr: Register,
        func_ref: RefKind,
        func_type: IRType,
        capture_types: Vec<IRType>,
        capture_registers: Vec<Register>,
        generics: Vec<IRType>,
    ) {
        // Create the environment struct
        let environment_register = self.allocate_register();
        let environment_type = IRType::Struct(SymbolID(0), capture_types.clone(), generics);
        self.push_instr(Instr::MakeStruct {
            dest: environment_register,
            ty: environment_type.clone(),
            values: RegisterList(
                capture_types
                    .into_iter()
                    .zip(capture_registers)
                    .map(|(ty, register)| TypedRegister { ty, register })
                    .collect(),
            ),
        });

        // Allocate space for the environment
        let env_dest_ptr = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: env_dest_ptr,
            count: None,
            ty: environment_type.clone(),
        });

        // Store the environment
        self.push_instr(Instr::Store {
            ty: environment_type,
            val: environment_register.into(),
            location: env_dest_ptr,
        });

        // Get reference to the function
        let func_ref_reg = self.allocate_register();
        self.push_instr(Instr::Ref(func_ref_reg, func_type, func_ref));

        // Get pointers to the closure fields
        let env_ptr = self.allocate_register();
        let fn_ptr = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: env_ptr,
            base: closure_ptr,
            ty: IRType::closure(),
            index: IRValue::ImmediateInt(1),
        });
        self.push_instr(Instr::GetElementPointer {
            dest: fn_ptr,
            base: closure_ptr,
            ty: IRType::closure(),
            index: IRValue::ImmediateInt(0),
        });

        // Store the environment and function pointers
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: env_dest_ptr.into(),
            location: env_ptr,
        });
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: func_ref_reg.into(),
            location: fn_ptr,
        });
    }

    fn push_constant(&mut self, constant: IRConstantData) -> usize {
        let cur = self.constants.len();
        self.constants.push(constant);
        cur
    }

    pub(super) fn push_instr(&mut self, instr: Instr) {
        let expr_id = self.current_expr_ids.last().copied();
        #[allow(clippy::unwrap_used)]
        self.current_block_mut()
            .unwrap()
            .instructions
            .push(InstructionWithExpr { instr, expr_id });
    }

    pub(super) fn allocate_register(&mut self) -> Register {
        #[allow(clippy::unwrap_used)]
        self.current_func_mut().unwrap().registers.allocate()
    }

    fn lookup_register(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.lookup_symbol(symbol_id)
    }

    fn lookup_symbol(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        if let Some(val) = self
            .current_functions
            .last()
            .and_then(|f| f._lookup_symbol(symbol_id))
        {
            return Some(val);
        }

        self.globals.get(symbol_id)
    }

    fn register_global(&mut self, symbol_id: &SymbolID, value: SymbolValue) {
        self.globals.insert(*symbol_id, value);
    }

    fn current_func_mut(&mut self) -> Option<&mut CurrentFunction> {
        self.current_functions.last_mut()
    }

    fn current_func(&mut self) -> Option<&CurrentFunction> {
        self.current_functions.last()
    }

    fn current_block_mut(&mut self) -> Option<&mut CurrentBasicBlock> {
        Some(self.current_func_mut()?.current_block_mut())
    }

    fn set_current_block(&mut self, id: BasicBlockID) -> Option<()> {
        self.current_func_mut()?.set_current_block(id).ok();

        Some(())
    }

    fn new_basic_block(&mut self) -> BasicBlockID {
        #[allow(clippy::unwrap_used)]
        let id = self.current_func_mut().unwrap().next_block_id();
        let block = CurrentBasicBlock {
            id,
            instructions: Vec::new(),
        };

        #[allow(clippy::unwrap_used)]
        self.current_func_mut().unwrap().add_block(block);
        id
    }

    fn resolve_name(&mut self, name: Option<ResolvedName>) -> ResolvedName {
        match name {
            Some(name) => name,
            None => {
                let name_str = format!("fn{}", self.symbol_table.max_id() + 1);
                let symbol =
                    self.symbol_table
                        .add(&name_str, SymbolKind::CustomType, ExprID(12345), None);
                ResolvedName(symbol, name_str)
            }
        }
    }

    pub fn add_diagnostic(&self, diagnostic: Diagnostic) {
        if let Ok(mut lock) = self.session.lock() {
            lock.add_diagnostic(diagnostic);
        }
    }

    pub fn push_err(&mut self, message: &str, expr_id: ExprID) -> IRError {
        self.add_diagnostic(Diagnostic::lowering(
            self.source_file.path.clone(),
            expr_id,
            IRError::Unknown(message.to_string()),
        ));

        IRError::Unknown(message.to_string())
    }

    pub fn property_index(&self, name: &str, irtype: IRType) -> Option<usize> {
        let IRType::Struct(symbol_id, _, _) = irtype else {
            unreachable!("didn't get property index for {:?}", irtype)
        };

        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(&symbol_id) else {
            unreachable!("didn't get typedef for {:?}", irtype)
        };

        struct_def.properties.iter().position(|k| k.name == name)
    }
}

fn find_or_create_main(
    source_file: &mut SourceFile<Typed>,
    symbol_table: &mut SymbolTable,
    env: &mut Environment,
) -> (TypedExpr, bool) {
    // If we've already generated a `main` for this file, reuse it so we don't
    // continually duplicate the AST on subsequent lowering passes.
    if symbol_table.get(&SymbolID::GENERATED_MAIN).is_some()
        && let Some(existing) = source_file
            .roots()
            .iter()
            .find(|expr| expr.id == ExprID(SymbolID::GENERATED_MAIN.0))
    {
        return (existing.clone(), false);
    }

    for root in source_file.roots() {
        if let TypedExpr {
            expr:
                Expr::Func {
                    name: Some(ResolvedName(_, name)),
                    ..
                },
            ..
        } = root
            && name == "main"
        {
            return (root.clone(), false);
        }
    }

    // We didn't find a main, we have to generate one
    let body_expr = Expr::Block(source_file.roots().to_vec());
    source_file.add(
        env.next_expr_id(),
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
            identifiers: vec![],
        },
    );

    let func_expr = Expr::Func {
        name: Some(ResolvedName(SymbolID::GENERATED_MAIN, "main".into())),
        generics: vec![],
        params: vec![],
        body: Box::new(TypedExpr {
            id: ExprID(0),
            expr: body_expr,
            ty: Ty::Void,
        }),
        ret: None,
        captures: vec![],
    };

    let typed_expr = TypedExpr {
        id: ExprID(SymbolID::GENERATED_MAIN.0),
        expr: func_expr.clone(),
        ty: Ty::Func(vec![], Box::new(Ty::Void), vec![]),
    };

    source_file.roots_mut().insert(0, typed_expr.clone());

    source_file.add(
        env.next_expr_id(),
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
            identifiers: vec![],
        },
    );

    symbol_table.import(
        &SymbolID::GENERATED_MAIN,
        SymbolInfo {
            name: "@main".into(),
            kind: SymbolKind::FuncDef,
            expr_id: ExprID(SymbolID::GENERATED_MAIN.0),
            is_captured: false,
            definition: None,
        },
    );

    (typed_expr, true)
}
