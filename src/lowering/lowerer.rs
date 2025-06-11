use std::{collections::HashMap, num::ParseIntError, ops::AddAssign, str::FromStr};

use crate::{
    Lowered, SourceFile, SymbolID, SymbolInfo, SymbolKind, SymbolTable, Typed,
    environment::TypeDef,
    expr::{Expr, ExprMeta, Pattern},
    lowering::{
        instr::{FuncName, Instr},
        ir_module::IRModule,
        parser::parser::ParserError,
    },
    name::Name,
    parser::ExprID,
    symbol_table,
    token::Token,
    token_kind::TokenKind,
    type_checker::Ty,
    typed_expr::TypedExpr,
};

#[derive(Debug, Clone)]
pub enum IRError {}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Register(pub i32);
impl FromStr for Register {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let reg = Register(str::parse(&s[1..])?);
        Ok(reg)
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("%{}", self.0))?;
        Ok(())
    }
}

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
                crate::lowering::parser::lexer::Tokind::Identifier(s.to_string()),
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
    fn to_ir(&self) -> IRType {
        match self {
            Ty::Void => IRType::Void,
            Ty::Int => IRType::Int,
            Ty::Bool => IRType::Bool,
            Ty::Float => IRType::Float,
            Ty::Func(items, ty) => IRType::Func(
                items.iter().map(|t| t.to_ir()).collect(),
                Box::new(ty.to_ir()),
            ),
            Ty::TypeVar(type_var_id) => IRType::TypeVar(format!("T{}", type_var_id.0)),
            Ty::Enum(_symbol_id, generics) => {
                IRType::Enum(generics.iter().map(|i| i.to_ir()).collect())
            }
            Ty::EnumVariant(_symbol_id, _items) => todo!(),
            Ty::Closure { func, .. } => func.to_ir(),
            Ty::Tuple(_items) => todo!(),
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

#[derive(Debug, Clone, PartialEq)]
pub enum IRType {
    Void,
    Int,
    Float,
    Bool,
    Func(Vec<IRType>, Box<IRType>),
    TypeVar(String),
    Enum(Vec<IRType>),
    Struct(Vec<IRType>),
    Pointer,
}

impl IRType {
    pub const EMPTY_STRUCT: IRType = IRType::Struct(vec![]);
    pub fn closure() -> IRType {
        IRType::Struct(vec![IRType::Pointer, IRType::Pointer])
    }
}

impl FromStr for IRType {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();

        // Handle function types like "(int, float) int"
        if s.starts_with('(') {
            let Some(end_of_args) = s.rfind(')') else {
                return Err(ParserError::UnexpectedEOF);
            };

            // Split into argument part and return type part
            let (args_str, ret_str) = s.split_at(end_of_args + 1);

            // Recursively parse arguments inside the parentheses
            let args_inner = &args_str[1..args_str.len() - 1];
            let mut args = vec![];
            if !args_inner.is_empty() {
                for arg_part in args_inner.split(',') {
                    args.push(IRType::from_str(arg_part.trim())?);
                }
            }

            // Recursively parse the return type
            let ret_ty = IRType::from_str(ret_str.trim())?;
            Ok(IRType::Func(args, Box::new(ret_ty)))
        } else {
            // Handle simple, non-function types
            match s {
                "void" => Ok(IRType::Void),
                "int" => Ok(IRType::Int),
                "float" => Ok(IRType::Float),
                "bool" => Ok(IRType::Bool),
                "enum" => Ok(IRType::Enum(vec![])), // Basic enum
                _ if s.starts_with('T') => Ok(IRType::TypeVar(s.to_string())),
                _ => Err(ParserError::UnexpectedToken(
                    vec![],
                    crate::lowering::parser::lexer::Tokind::Identifier(s.to_string()),
                )),
            }
        }
    }
}

impl std::fmt::Display for IRType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Void => f.write_str("void"),
            Self::Int => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::Bool => f.write_str("bool"),
            Self::Func(args, ret) => {
                write!(
                    f,
                    "({}) {}",
                    args.iter()
                        .map(|a| format!("{}", a))
                        .collect::<Vec<String>>()
                        .join(", "),
                    ret
                )
            }
            Self::TypeVar(name) => f.write_str(name),
            Self::Enum(_generics) => f.write_str("enum"),
            Self::Struct(types) => write!(
                f,
                "struct {{{}}}",
                types
                    .iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            IRType::Pointer => write!(f, "ptr"),
        }
    }
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub struct BasicBlockID(pub u32);

impl AddAssign<u32> for BasicBlockID {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs
    }
}

impl FromStr for BasicBlockID {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "entry" {
            Ok(BasicBlockID(0))
        } else {
            Ok(BasicBlockID(str::parse(&s[1..]).unwrap()))
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
pub struct BasicBlock {
    pub id: BasicBlockID,
    pub instructions: Vec<Instr>,
}

impl BasicBlock {
    fn push_instr(&mut self, instr: Instr) {
        self.instructions.push(instr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PhiPredecessors(pub Vec<(Register, BasicBlockID)>);

impl std::fmt::Display for PhiPredecessors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (i, (reg, id)) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{id}: {reg}")?;
        }
        f.write_str("]")?;
        Ok(())
    }
}

impl FromStr for PhiPredecessors {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let inner = s
            .trim()
            .strip_prefix('[')
            .and_then(|s| s.strip_suffix(']'))
            .ok_or(ParserError::UnexpectedEOF)?;

        if inner.trim().is_empty() {
            return Ok(PhiPredecessors(vec![]));
        }

        inner
            .split(',')
            .map(|pair_str| {
                let mut parts = pair_str.trim().splitn(2, ':');

                let bb_str = parts.next().ok_or(ParserError::UnexpectedEOF)?.trim();
                let reg_str = parts.next().ok_or(ParserError::UnexpectedEOF)?.trim();

                let bb = bb_str.parse::<BasicBlockID>()?;
                let reg = reg_str.parse::<Register>().map_err(ParserError::from)?;

                Ok((reg, bb))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(PhiPredecessors)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RegisterList(pub Vec<Register>);

impl RegisterList {
    pub const EMPTY: RegisterList = RegisterList(vec![]);
}

impl From<Vec<Register>> for RegisterList {
    fn from(value: Vec<Register>) -> Self {
        Self(value)
    }
}

impl std::fmt::Display for RegisterList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, reg) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{reg}")?;
        }
        Ok(())
    }
}

// Replace the old implementation with this one.
impl FromStr for RegisterList {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The input 's' is the content *between* the parentheses, e.g., "%1, %2" or "".
        let s = s.trim();
        if s.is_empty() {
            // Correctly handle the case of zero arguments.
            return Ok(RegisterList(vec![]));
        }

        // For non-empty arguments, split by comma and parse each part.
        s.split(',')
            .map(|part| part.trim().parse::<Register>())
            .collect::<Result<Vec<Register>, _>>()
            .map(RegisterList)
            .map_err(|e| e.into())
    }
}

#[derive(Debug, Clone)]
pub enum SymbolValue {
    Register(Register),
    Capture(usize, IRType),
}

impl From<Register> for SymbolValue {
    fn from(value: Register) -> Self {
        Self::Register(value)
    }
}

struct CurrentFunction {
    current_block_idx: usize,
    next_block_id: BasicBlockID,
    blocks: Vec<BasicBlock>,
    env_reg: Register,
    env_ty: IRType,
    pub registers: RegisterAllocator,
    pub symbol_registers: HashMap<SymbolID, SymbolValue>,
}

impl CurrentFunction {
    #[track_caller]
    fn new(env_reg: Register, env_ty: IRType) -> Self {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!("new CurrentFunction from {}:{}", loc.file(), loc.line());
        }
        Self {
            next_block_id: BasicBlockID(0),
            current_block_idx: 0,
            blocks: Default::default(),
            env_reg,
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

    fn add_block(&mut self, block: BasicBlock) {
        self.blocks.push(block);
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        &mut self.blocks[self.current_block_idx]
    }

    fn set_current_block(&mut self, id: BasicBlockID) {
        let index = self.blocks.iter().position(|blk| blk.id == id).unwrap();
        self.current_block_idx = index;
    }

    #[track_caller]
    fn register_symbol(&mut self, symbol_id: SymbolID, register: SymbolValue) {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "register symbol {:?}: {:?} from {}:{}",
                symbol_id,
                register,
                loc.file(),
                loc.line()
            );
        }
        self.symbol_registers.insert(symbol_id, register);
    }

    fn lookup_symbol(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.symbol_registers.get(symbol_id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRFunction {
    pub ty: IRType,
    pub name: String,
    pub blocks: Vec<BasicBlock>,
    pub env_ty: IRType,
}

impl IRFunction {
    pub(crate) fn args(&self) -> &[IRType] {
        let IRType::Func(ref args, _) = self.ty else {
            unreachable!()
        };

        args
    }

    pub(crate) fn ret(&self) -> &IRType {
        let IRType::Func(_, ref ret) = self.ty else {
            unreachable!()
        };

        ret
    }
}

#[derive(Debug, Clone, PartialEq)]
struct RegisterAllocator {
    next_id: i32,
}

impl RegisterAllocator {
    fn new() -> Self {
        log::trace!("new register allocator");
        Self { next_id: 0 }
    }

    fn allocate(&mut self) -> Register {
        let id = self.next_id;
        self.next_id += 1;
        Register(id)
    }
}

pub struct Lowerer<'a> {
    source_file: SourceFile<Typed>,
    current_functions: Vec<CurrentFunction>,
    lowered_functions: Vec<IRFunction>,
    symbol_table: &'a mut SymbolTable,
}

impl<'a> Lowerer<'a> {
    pub fn new(source_file: SourceFile<Typed>, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            source_file,
            current_functions: vec![],
            lowered_functions: Default::default(),
            symbol_table,
        }
    }

    pub fn lower(mut self, module: &mut IRModule) -> Result<SourceFile<Lowered>, IRError> {
        let (expr_id, did_create) = find_or_create_main(&mut self.source_file, self.symbol_table);

        // If we created the main function, we need to set it up
        if did_create {
            // Make sure we have a current function
            self.current_functions
                .push(CurrentFunction::new(Register(0), IRType::Struct(vec![])));

            // Make sure it has a basic block
            let entry = self.new_basic_block();
            self.set_current_block(entry);
        }

        self.lower_function(&expr_id);

        // If we created the main function, we moved all the typed roots into its body
        // so we don't need to lower them again.
        if !did_create {
            let typed_roots = self.source_file.typed_roots().to_owned();
            for root in typed_roots {
                if let Expr::Func { .. } = &root.expr {
                    self.lower_function(&root.id);
                }
            }
        }

        for function in self.lowered_functions {
            module.functions.push(function)
        }

        Ok(self.source_file.to_lowered())
    }

    fn lower_function(&mut self, expr_id: &ExprID) -> Register {
        let typed_expr = self
            .source_file
            .typed_expr(expr_id)
            .expect("Did not get typed expr");

        let Expr::Func {
            ref name,
            ref params,
            ref body,
            ref captures,
            ..
        } = typed_expr.expr
        else {
            panic!(
                "Attempted to lower non-function: {:?}",
                self.source_file.get(expr_id)
            );
        };

        let (capture_types, capture_registers) = if let Ty::Closure {
            captures: capture_types,
            ..
        } = &typed_expr.ty
        {
            // Define an environment object for our captures. If there aren't any captures we don't care,
            // we're going to do it anyway. Maybe we can optimize it out later? I don't know if we'll have time.
            let mut capture_registers = vec![];
            for capture in captures {
                let SymbolValue::Register(register) = self
                    .lookup_register(capture)
                    .expect("could not find register for capture")
                else {
                    todo!("don't know how to handle captured captures yet")
                };
                capture_registers.push(*register);
            }

            (
                capture_types.iter().map(Ty::to_ir).collect(),
                capture_registers,
            )
        } else {
            (vec![], vec![])
        };

        let environment_register = self.allocate_register();
        let environment_type = IRType::Struct(capture_types.clone());
        // Create the env
        self.push_instr(Instr::MakeStruct {
            dest: environment_register,
            ty: environment_type.clone(),
            values: RegisterList(capture_registers),
        });

        // Alloc a spot for it
        let env_dest_ptr = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: env_dest_ptr,
            ty: environment_type.clone(),
        });

        self.push_instr(Instr::Store {
            ty: environment_type.clone(),
            val: environment_register,
            location: env_dest_ptr,
        });

        self.current_functions
            .push(CurrentFunction::new(environment_register, environment_type));

        // Now that we're in the block, register the captures
        for (i, capture) in captures.iter().enumerate() {
            self.current_func_mut()
                .register_symbol(*capture, SymbolValue::Capture(i, capture_types[i].clone()));
        }

        let name = match name {
            Some(Name::Resolved(_, _)) => name.clone().unwrap(),
            None => {
                let name_str = format!("fn{}", self.symbol_table.max_id() + 1);
                let symbol = self
                    .symbol_table
                    .add(&name_str, SymbolKind::CustomType, 12345);

                Name::Resolved(symbol, name_str)
            }
            _ => todo!(),
        };

        log::trace!("lowering {:?}", name);

        let Some(Expr::Block(body_exprs)) = self.source_file.get(body).cloned() else {
            panic!("did not get body")
        };

        let id = self.new_basic_block();
        self.set_current_block(id);

        self.allocate_register(); // Set aside our env register

        for param in params {
            let Expr::Parameter(Name::Resolved(symbol, _), _) =
                self.source_file.get(param).unwrap().clone()
            else {
                panic!("didn't get parameter")
            };

            let register = self.current_func_mut().registers.allocate();
            self.current_func_mut()
                .register_symbol(symbol, SymbolValue::Register(register));
        }

        for (i, id) in body_exprs.iter().enumerate() {
            let ret = if let Some(reg) = self.lower_expr(id) {
                let ty = self.source_file.typed_expr(id).unwrap().ty.to_ir();
                (ty, Some(reg))
            } else {
                (IRType::Void, None)
            };

            if i == body_exprs.len() - 1 {
                // we don't pass around functions, we pass around pointers (closures)
                let ty = if matches!(ret.0, IRType::Func(_, _)) {
                    IRType::Pointer
                } else {
                    ret.0
                };

                self.current_block_mut().push_instr(Instr::Ret(ty, ret.1));
            }
        }

        let func = IRFunction {
            ty: typed_expr.ty.to_ir(),
            name: name.mangled(&typed_expr.ty),
            blocks: self.current_func_mut().blocks.clone(),
            env_ty: self.current_func().env_ty.clone(),
        };
        self.lowered_functions.push(func.clone());
        self.current_functions.pop();

        let Name::Resolved(symbol, _) = name else {
            panic!("no symbol")
        };

        let func_ref_reg = self.current_func_mut().registers.allocate();

        self.current_func_mut()
            .register_symbol(symbol, SymbolValue::Register(func_ref_reg));
        self.current_block_mut().push_instr(Instr::Ref(
            func_ref_reg,
            typed_expr.ty.to_ir(),
            RefKind::Func(name.mangled(&typed_expr.ty)),
        ));

        // making the closure
        let closure_ptr = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: closure_ptr,
            ty: IRType::closure(),
        });
        let env_ptr = self.allocate_register();
        let fn_ptr = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: env_ptr,
            from: closure_ptr,
            ty: IRType::closure(),
            index: 1,
        });
        self.push_instr(Instr::GetElementPointer {
            dest: fn_ptr,
            from: closure_ptr,
            ty: IRType::closure(),
            index: 0,
        });

        self.push_instr(Instr::Store {
            ty: IRType::Pointer,
            val: env_dest_ptr,
            location: env_ptr,
        });
        self.push_instr(Instr::Store {
            ty: IRType::Pointer,
            val: func_ref_reg,
            location: fn_ptr,
        });

        closure_ptr
    }

    fn lower_expr(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap().clone();
        match typed_expr.expr {
            Expr::LiteralInt(_)
            | Expr::LiteralFloat(_)
            | Expr::LiteralFalse
            | Expr::LiteralTrue => self.lower_literal(expr_id),
            Expr::Binary(_, _, _) => self.lower_binary_op(expr_id),
            Expr::Assignment(lhs, rhs) => self.lower_assignment(&lhs, &rhs),
            Expr::Variable(name, _) => self.lower_variable(&name),
            Expr::If(_, _, _) => self.lower_if(expr_id),
            Expr::Block(_) => self.lower_block(expr_id),
            Expr::Call(callee, args) => self.lower_call(callee, args, typed_expr.ty),
            Expr::Func { .. } => Some(self.lower_function(expr_id)),
            Expr::Return(rhs) => self.lower_return(expr_id, &rhs),
            Expr::EnumDecl(_, _, _) => None,
            Expr::Member(_, name) => self.lower_member(expr_id, &name),
            Expr::Match(scrutinee, arms) => self.lower_match(&scrutinee, &arms, &typed_expr.ty),
            expr => todo!("Cannot lower {:?}", expr),
        }
    }

    fn lower_match(&mut self, scrutinee: &ExprID, arms: &[ExprID], ty: &Ty) -> Option<Register> {
        let scrutinee_reg = self.lower_expr(scrutinee).unwrap();
        let merge_block_id = self.new_basic_block();

        let mut predecessors = vec![];
        for arm in arms {
            predecessors.push(self.lower_match_arm(arm, &scrutinee_reg, merge_block_id));
        }

        self.push_instr(Instr::Unreachable);
        self.set_current_block(merge_block_id);

        let phi_reg = self.allocate_register();
        self.push_instr(Instr::Phi(
            phi_reg,
            ty.to_ir(),
            PhiPredecessors(predecessors),
        ));

        Some(phi_reg)
    }

    fn lower_match_arm(
        &mut self,
        expr_id: &ExprID,
        scrutinee: &Register,
        merge_block_id: BasicBlockID,
    ) -> (Register, BasicBlockID) {
        let typed_arm = self.source_file.typed_expr(expr_id).unwrap();
        let Expr::MatchArm(pattern_id, body_id) = typed_arm.expr else {
            panic!("Didn't get match arm: {:?}", typed_arm);
        };

        // This is the new, more powerful pattern lowering logic.
        let current_block_id = self.current_block_mut().id;
        let body_block = self.lower_pattern_and_bind(&pattern_id, scrutinee);
        self.set_current_block(body_block);

        let body_ret_reg = self.lower_expr(&body_id).unwrap();

        // After evaluating body, jump to the merge
        self.push_instr(Instr::Jump(merge_block_id));

        self.set_current_block(current_block_id);

        (body_ret_reg, body_block)
    }

    fn lower_pattern_and_bind(
        &mut self,
        pattern_id: &ExprID,
        scrutinee_reg: &Register,
    ) -> BasicBlockID {
        let pattern_typed_expr = self.source_file.typed_expr(pattern_id).unwrap();
        let Expr::Pattern(pattern) = pattern_typed_expr.expr else {
            panic!("Expected a pattern expression");
        };

        match pattern {
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                // 1. Get the tag for this variant from the enum definition.
                let Ty::Enum(enum_id, enum_generics) = &pattern_typed_expr.ty else {
                    panic!("did not get enum")
                };

                let TypeDef::Enum(type_def) = self.source_file.type_def(enum_id).cloned().unwrap();

                /* ... find variant by name in type_def ... */
                let (tag, variant_def) = type_def.tag_with_variant_for(&variant_name);

                // 2. Get the tag of the scrutinee.
                let tag_reg = self.allocate_register();
                self.push_instr(Instr::GetEnumTag(tag_reg, *scrutinee_reg));

                // 3. Compare with the expected tag.
                let expected_tag_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(expected_tag_reg, tag as i64));
                let tags_match_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    tags_match_reg,
                    IRType::Int,
                    tag_reg,
                    expected_tag_reg,
                ));

                // 4. If tags match, jump to a new block to extract values.
                let body_block = self.new_basic_block();
                self.push_instr(Instr::JumpIf(tags_match_reg, body_block));

                self.set_current_block(body_block);

                // 5. Extract values and bind them.
                for (i, field_pattern_id) in fields.iter().enumerate() {
                    if let Expr::Pattern(Pattern::Bind(Name::Resolved(symbol_id, _))) =
                        self.source_file.get(field_pattern_id).unwrap().clone()
                    {
                        let value_reg = self.allocate_register();

                        // We need to figure out the type of the value. This feels clumsy.
                        let ty = match variant_def.values[i].clone() {
                            Ty::TypeVar(var) => {
                                let Some(generic_pos) = type_def
                                    .type_parameters
                                    .iter()
                                    .filter_map(|t| {
                                        if let Ty::TypeVar(var_id) = t {
                                            Some(var_id)
                                        } else {
                                            None
                                        }
                                    })
                                    .position(|t| t == &var)
                                // t == var.0)
                                else {
                                    panic!("unable to determine enum generic: {:?}", var)
                                };

                                enum_generics[generic_pos].clone()
                            }
                            other => other,
                        };

                        self.push_instr(Instr::GetEnumValue(
                            value_reg,
                            ty.to_ir(),
                            *scrutinee_reg,
                            tag,
                            i as u16,
                        ));
                        self.current_func_mut()
                            .register_symbol(symbol_id, SymbolValue::Register(value_reg));
                    }
                    // Handle nested patterns recursively here.
                }

                body_block
            }
            Pattern::LiteralInt(val) => {
                let literal_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(literal_reg, val.parse().unwrap()));
                let is_eq_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    is_eq_reg,
                    IRType::Int,
                    *scrutinee_reg,
                    literal_reg,
                ));

                let body_block = self.new_basic_block();
                self.push_instr(Instr::JumpIf(is_eq_reg, body_block));

                body_block
            }
            Pattern::LiteralFloat(_) => todo!(),
            Pattern::LiteralTrue => todo!(),
            Pattern::LiteralFalse => todo!(),
            Pattern::Bind(_name) => todo!(),
            Pattern::Wildcard => todo!(),
        }
    }

    fn _lower_pattern(&mut self, pattern_id: &ExprID) -> Register {
        let pattern_typed_expr = self.source_file.typed_expr(pattern_id).unwrap();
        let Expr::Pattern(pattern) = pattern_typed_expr.expr else {
            panic!("Didn't get pattern for match arm: {:?}", pattern_typed_expr)
        };

        match pattern {
            Pattern::Bind(_) => todo!(),
            Pattern::LiteralInt(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(reg, str::parse(&val).unwrap()));
                reg
            }
            Pattern::LiteralFloat(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantFloat(reg, str::parse(&val).unwrap()));
                reg
            }
            Pattern::LiteralTrue => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, true));
                reg
            }
            Pattern::LiteralFalse => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, false));
                reg
            }
            Pattern::Wildcard => todo!(),
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Ty::Enum(enum_id, _) = pattern_typed_expr.ty else {
                    panic!("didn't get pattern type: {:?}", pattern_typed_expr.ty)
                };
                let Some(TypeDef::Enum(type_def)) = self.source_file.type_def(&enum_id).cloned()
                else {
                    panic!("didn't get type def for {:?}", enum_id);
                };

                let tag = type_def
                    .variants
                    .iter()
                    .position(|v| v.name == variant_name)
                    .unwrap() as u16;

                let dest = self.allocate_register();
                let args = RegisterList(fields.iter().map(|f| self._lower_pattern(f)).collect());
                self.push_instr(Instr::TagVariant(
                    dest,
                    pattern_typed_expr.ty.to_ir(),
                    tag,
                    args,
                ));

                dest
            } // _ => todo!("{:?}", pattern),
        }
    }

    fn lower_member(&mut self, expr_id: &ExprID, name: &str) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap();

        match &typed_expr.ty {
            Ty::Enum(sym, _generics) => {
                // Since we got called directly from lower_expr, this is variant that doesn't
                // have any attached values.

                self.lower_enum_construction(*sym, name, &typed_expr.ty, &[])
            }
            _ => todo!("lower_member: {:?}", typed_expr),
        }
    }

    fn lower_enum_construction(
        &mut self,
        enum_id: SymbolID,
        variant_name: &str,
        ty: &Ty,
        args: &[Register],
    ) -> Option<Register> {
        let Some(TypeDef::Enum(type_def)) = self.source_file.type_def(&enum_id).cloned() else {
            panic!("didn't get type def for {:?}", enum_id);
        };

        let mut tag: Option<u16> = None;

        for (i, var) in type_def.variants.iter().enumerate() {
            if var.name != variant_name {
                continue;
            }

            tag = Some(i as u16);
        }

        let Some(tag) = tag else {
            panic!("did not find variant for tag")
        };

        let dest = self.allocate_register();
        self.push_instr(Instr::TagVariant(
            dest,
            ty.to_ir(),
            tag,
            args.to_vec().into(),
        ));

        Some(dest)
    }

    fn lower_return(&mut self, expr_id: &ExprID, rhs: &Option<ExprID>) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap();

        if let Some(rhs) = rhs {
            let register = self.lower_expr(rhs)?;
            self.current_block_mut()
                .push_instr(Instr::Ret(typed_expr.ty.to_ir(), Some(register)));
            Some(register)
        } else {
            self.current_block_mut()
                .push_instr(Instr::Ret(IRType::Void, None));
            None
        }
    }

    fn lower_literal(&mut self, expr_id: &ExprID) -> Option<Register> {
        let register = self.allocate_register();
        match self.source_file.get(expr_id).unwrap().clone() {
            Expr::LiteralInt(val) => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantInt(register, str::parse(&val).unwrap()));
            }
            Expr::LiteralFloat(val) => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantFloat(register, str::parse(&val).unwrap()));
            }
            Expr::LiteralFalse => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantBool(register, false));
            }
            Expr::LiteralTrue => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantBool(register, true));
            }
            _ => unreachable!(),
        }

        Some(register)
    }

    fn lower_binary_op(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self
            .source_file
            .typed_expr(expr_id)
            .expect("Did not get binary typed expr");

        let Expr::Binary(lhs, op, rhs) = typed_expr.expr else {
            panic!("Did not get binary expr");
        };

        let operand_ty = self.source_file.type_for(lhs);

        let operand_1 = self.lower_expr(&lhs).unwrap();
        let operand_2 = self.lower_expr(&rhs).unwrap();
        let return_reg = self.allocate_register();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg, typed_expr.ty.to_ir(), operand_1, operand_2),
            Minus => Instr::Sub(return_reg, typed_expr.ty.to_ir(), operand_1, operand_2),
            Star => Instr::Mul(return_reg, typed_expr.ty.to_ir(), operand_1, operand_2),
            Slash => Instr::Div(return_reg, typed_expr.ty.to_ir(), operand_1, operand_2),
            BangEquals => Instr::Ne(return_reg, operand_ty.to_ir(), operand_1, operand_2),
            EqualsEquals => Instr::Eq(return_reg, operand_ty.to_ir(), operand_1, operand_2),

            Less => Instr::LessThan(return_reg, operand_ty.to_ir(), operand_1, operand_2),
            LessEquals => Instr::LessThanEq(return_reg, operand_ty.to_ir(), operand_1, operand_2),
            Greater => Instr::GreaterThan(return_reg, operand_ty.to_ir(), operand_1, operand_2),
            GreaterEquals => {
                Instr::GreaterThanEq(return_reg, operand_ty.to_ir(), operand_1, operand_2)
            }
            _ => panic!("Cannot lower binary operation: {:?}", op),
        };

        self.current_block_mut().push_instr(instr);

        Some(return_reg)
    }

    fn lower_assignment(&mut self, lhs: &ExprID, rhs: &ExprID) -> Option<Register> {
        let rhs = self
            .lower_expr(rhs)
            .expect("Did not get rhs for assignment");

        match self.source_file.get(lhs).unwrap().clone() {
            Expr::Let(Name::Resolved(symbol_id, _), _) => {
                self.current_func_mut()
                    .register_symbol(symbol_id, rhs.into());
                None
            }
            _ => todo!(),
        }
    }

    fn lower_block(&mut self, block_id: &ExprID) -> Option<Register> {
        let Expr::Block(exprs) = self.source_file.get(block_id).unwrap().clone() else {
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

    fn lower_variable(&mut self, name: &Name) -> Option<Register> {
        let Name::Resolved(symbol_id, _) = name else {
            panic!("Unresolved variable: {:?}", name)
        };

        let value = self
            .lookup_register(symbol_id)
            .expect("no value for name")
            .clone();

        match value {
            SymbolValue::Register(reg) => Some(reg.clone()),
            SymbolValue::Capture(idx, ty) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::GetElementPointer {
                    dest: reg,
                    from: Register(0),
                    ty: ty.clone(),
                    index: idx.clone(),
                });

                Some(reg)
            }
        }
    }

    fn lower_if(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap();
        let Expr::If(cond, conseq, alt) = typed_expr.expr else {
            unreachable!()
        };

        let cond_reg = self
            .lower_expr(&cond)
            .expect("Condition for if expression did not produce a value");

        let then_id = self.current_block_mut().id;

        let mut else_reg: Option<Register> = None;
        let else_id: Option<BasicBlockID> = if alt.is_some() {
            Some(self.new_basic_block())
        } else {
            None
        };
        let merge_id = self.new_basic_block(); // All paths merge here

        self.current_block_mut()
            .push_instr(Instr::JumpUnless(cond_reg, else_id.unwrap_or(merge_id)));

        let then_reg = self.lower_expr(&conseq).unwrap();
        self.current_block_mut().push_instr(Instr::Jump(merge_id));

        if let Some(alt) = alt {
            self.set_current_block(else_id.unwrap());
            else_reg = self.lower_expr(&alt);
            self.current_block_mut().push_instr(Instr::Jump(merge_id));
        }

        self.current_func_mut().set_current_block(merge_id);

        let phi_dest_reg = self.allocate_register();

        self.current_block_mut().push_instr(Instr::Phi(
            phi_dest_reg,
            typed_expr.ty.to_ir(),
            PhiPredecessors(vec![
                (then_reg, then_id),                   // Value from 'then' path came from then_bb
                (else_reg.unwrap(), else_id.unwrap()), // Value from 'else' path came from else_bb
            ]),
        ));

        Some(phi_dest_reg)
    }

    fn lower_call(&mut self, callee: ExprID, args: Vec<ExprID>, ty: Ty) -> Option<Register> {
        let mut arg_registers = vec![];
        for arg in args {
            if let Some(arg_reg) = self.lower_expr(&arg) {
                arg_registers.push(arg_reg);
            } else {
                // This would happen if an argument expression doesn't produce a value.
                // Depending on your language, this might be an error or indicate a void arg,
                // though void args are uncommon.
                panic!("Argument expression did not produce a value for call");
            }
        }

        let callee_typed_expr = self.source_file.typed_expr(&callee).unwrap();

        // Handle enum variant construction
        if let Ty::Enum(enum_id, _) = &ty {
            let Expr::Member(_, variant_name) = &callee_typed_expr.expr else {
                panic!("didn't get member expr for enum call")
            };

            return self.lower_enum_construction(*enum_id, variant_name, &ty, &arg_registers);
        }

        let callee = self.lower_expr(&callee).expect("did not get callee");

        let func_ptr = self.allocate_register();
        let func_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: func_ptr,
            from: callee,
            ty: IRType::closure(),
            index: 0,
        });
        self.push_instr(Instr::Load {
            dest: func_reg,
            ty: callee_typed_expr.ty.to_ir(),
            addr: func_ptr,
        });

        let env_ptr = self.allocate_register();
        let env_reg = self.allocate_register();

        self.push_instr(Instr::GetElementPointer {
            dest: env_ptr,
            from: callee,
            ty: IRType::closure(),
            index: 1,
        });
        self.push_instr(Instr::Load {
            dest: env_reg,
            ty: IRType::Pointer,
            addr: env_ptr,
        });

        arg_registers.insert(0, env_reg);

        let dest_reg = self.allocate_register();

        self.current_block_mut().push_instr(Instr::Call {
            ty: ty.to_ir(),
            dest_reg, // clone if Register is Copy, else it's fine
            callee: func_reg,
            args: RegisterList(arg_registers),
        });

        // 5. Return the destination register
        Some(dest_reg)
    }

    fn push_instr(&mut self, instr: Instr) {
        self.current_block_mut().push_instr(instr);
    }

    fn allocate_register(&mut self) -> Register {
        self.current_func_mut().registers.allocate()
    }

    fn lookup_register(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.current_functions
            .last()
            .unwrap()
            .lookup_symbol(symbol_id)
    }

    fn current_func_mut(&mut self) -> &mut CurrentFunction {
        self.current_functions.last_mut().unwrap()
    }

    fn current_func(&mut self) -> &CurrentFunction {
        self.current_functions.last().unwrap()
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        self.current_func_mut().current_block_mut()
    }

    fn set_current_block(&mut self, id: BasicBlockID) {
        self.current_func_mut().set_current_block(id);
    }

    fn new_basic_block(&mut self) -> BasicBlockID {
        let id = self.current_func_mut().next_block_id();
        let block = BasicBlock {
            id,
            instructions: Vec::new(),
        };

        self.current_func_mut().add_block(block);
        id
    }
}

fn find_or_create_main(
    source_file: &mut SourceFile<Typed>,
    symbol_table: &mut SymbolTable,
) -> (ExprID, bool) {
    for root in source_file.typed_roots() {
        if let TypedExpr {
            expr:
                Expr::Func {
                    name: Some(Name::Resolved(_, name)),
                    ..
                },
            ..
        } = root
        {
            if name == "main" {
                return (root.id, false);
            }
        }
    }

    // We didn't find a main, we have to generate one
    let body = Expr::Block(source_file.root_ids());

    let body_id = source_file.add(
        body,
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
        },
    );

    let func_expr = Expr::Func {
        name: Some(Name::Resolved(SymbolID::GENERATED_MAIN, "main".into())),
        generics: vec![],
        params: vec![],
        body: body_id,
        ret: None,
        captures: vec![],
    };

    source_file.set_typed_expr(
        SymbolID::GENERATED_MAIN.0,
        TypedExpr {
            id: SymbolID::GENERATED_MAIN.0,
            expr: func_expr.clone(),
            ty: Ty::Func(vec![], Box::new(Ty::Void)),
        },
    );

    source_file.add(
        func_expr.clone(),
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
        },
    );

    symbol_table.import(
        &SymbolID::GENERATED_MAIN,
        SymbolInfo {
            name: "@main".into(),
            kind: SymbolKind::Func,
            expr_id: SymbolID::GENERATED_MAIN.0,
            is_captured: false,
        },
    );

    (SymbolID::GENERATED_MAIN.0, true)
}

#[cfg(test)]
mod tests {
    use prettydiff::diff_lines;

    use crate::{
        SymbolTable, check,
        lowering::{
            ir_module::IRModule,
            ir_printer::print,
            lowerer::{
                BasicBlock, BasicBlockID, IRError, IRFunction, IRType, Instr, Lowerer,
                PhiPredecessors, RefKind, Register, RegisterList,
            },
        },
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let typed = check(input).unwrap();
        let mut symbol_table = SymbolTable::default();
        let lowerer = Lowerer::new(typed, &mut symbol_table);
        let mut module = IRModule::new();
        lowerer.lower(&mut module)?;
        Ok(module)
    }

    macro_rules! assert_lowered_functions {
        ($left:expr, $right:expr $(,)?) => {
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if !(*left_val.functions == *right_val) {
                        let right_program = IRModule {
                            functions: right_val.clone(),
                        };

                        println!("\n\n\n{:#?}\n{:#?}\n\n\n", &left_val.functions, right_val);

                        panic!(
                            "{}\n{}",
                            diff_lines("Actual", "Expected"),
                            diff_lines(print(left_val).as_ref(), print(&right_program).as_ref())
                        )
                    }
                }
            }
        };
    }

    #[test]
    fn lowers_nested_function() {
        let lowered = lower("func foo() { 123 }").unwrap();

        // Define the types we'll be using to make the test cleaner
        let foo_func_type = IRType::Func(vec![], Box::new(IRType::Int));

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: foo_func_type.clone(),
                    name: "@_5_foo".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Ret(IRType::Int, Some(Register(1)))
                        ],
                    }],
                    env_ty: IRType::EMPTY_STRUCT
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::MakeStruct {
                                dest: Register(1),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            Instr::Alloc {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Store {
                                val: Register(1),
                                location: Register(2),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Ref(
                                Register(3),
                                foo_func_type.clone(),
                                RefKind::Func("@_5_foo".into())
                            ),
                            Instr::Alloc {
                                dest: Register(4),
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(5),
                                from: Register(4),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                from: Register(4),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Ret(IRType::Pointer, Some(Register(4))),
                        ],
                    }],
                    env_ty: IRType::EMPTY_STRUCT,
                },
            ]
        )
    }

    #[test]
    fn lowers_return() {
        let lowered = lower(
            "
        func foo(x) {
            return x
            123
        }
        ",
        )
        .unwrap();

        let foo_func_type = IRType::Func(vec![IRType::Int], Box::new(IRType::Int));

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: foo_func_type.clone(),
                    name: "@_5_foo".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // The `return x` becomes a Ret instruction using the argument register.
                            // In our calling convention, the env is %0, so x is %1.
                            Instr::Ret(IRType::Int, Some(Register(1))),
                            // The `123` is dead code but is still lowered.
                            Instr::ConstantInt(Register(2), 123),
                            // The implicit return is still added
                            Instr::Ret(IRType::Int, Some(Register(2)))
                        ],
                    }],
                    env_ty: IRType::EMPTY_STRUCT,
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // This sequence is now identical to your working test case.
                            Instr::MakeStruct {
                                dest: Register(1),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            Instr::Alloc {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Store {
                                val: Register(1),
                                location: Register(2),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Ref(
                                Register(3),
                                foo_func_type.clone(),
                                RefKind::Func("@_5_foo".into())
                            ),
                            Instr::Alloc {
                                dest: Register(4),
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(5),
                                from: Register(4),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                from: Register(4),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Ret(IRType::Pointer, Some(Register(4))),
                        ],
                    }],
                    env_ty: IRType::EMPTY_STRUCT,
                },
            ]
        )
    }

    #[test]
    fn lowers_calls() {
        let lowered = lower("func foo(x) { x }\nfoo(123)").unwrap();

        let foo_func_type = IRType::Func(
            vec![IRType::TypeVar("T3".into())],
            Box::new(IRType::TypeVar("T3".into())),
        );

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: foo_func_type.clone(),
                    name: "@_5_foo".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![Instr::Ret(
                            IRType::TypeVar("T3".into()),
                            Some(Register(1))
                        )],
                    }],
                    env_ty: IRType::EMPTY_STRUCT
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // === Part 1: Create the closure for `foo` ===
                            Instr::MakeStruct {
                                dest: Register(1),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            Instr::Alloc {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Store {
                                val: Register(1),
                                location: Register(2),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Ref(
                                Register(3),
                                foo_func_type.clone(),
                                RefKind::Func("@_5_foo".into())
                            ),
                            Instr::Alloc {
                                dest: Register(4),
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(5),
                                from: Register(4),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                from: Register(4),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            // %4 now holds the pointer to the `foo` closure.

                            // === Part 2: Call the closure ===

                            // 1. Prepare the explicit argument(s).
                            Instr::ConstantInt(Register(7), 123),
                            // 2. Unpack the closure object from %4.
                            // You need to introduce a Load instruction here.
                            Instr::GetElementPointer {
                                dest: Register(8),
                                from: Register(3),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(9),
                                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                                addr: Register(8)
                            }, // Load the func_ptr
                            Instr::GetElementPointer {
                                dest: Register(10),
                                from: Register(3),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(11),
                                ty: IRType::Pointer,
                                addr: Register(10)
                            }, // Load the env_ptr
                            // 3. Make the indirect call.
                            Instr::Call {
                                dest_reg: Register(12),
                                ty: IRType::Int,
                                callee: Register(9), // The loaded function pointer
                                args: RegisterList(vec![Register(11), Register(7)]), // (env_ptr, arg)
                            },
                            // 4. Return the result of the call.
                            Instr::Ret(IRType::Int, Some(Register(12)))
                        ],
                    }],
                    env_ty: IRType::EMPTY_STRUCT,
                },
            ]
        )
    }

    #[test]
    fn lowers_func_with_params() {
        let lowered = lower("func foo(x) { x }").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: IRType::Func(
                        vec![IRType::TypeVar("T3".into())],
                        IRType::TypeVar("T3".into()).into()
                    ),
                    name: "@_5_foo".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![Instr::Ret(
                            IRType::TypeVar("T3".into()),
                            Some(Register(1))
                        )],
                    }],
                    env_ty: IRType::Struct(vec![])
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // Create the env
                            Instr::MakeStruct {
                                dest: Register(1),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            // Alloc space for it
                            Instr::Alloc {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT,
                            },
                            // Store the env
                            Instr::Store {
                                ty: IRType::EMPTY_STRUCT,
                                val: Register(1),
                                location: Register(2)
                            },
                            // Get the fn
                            Instr::Ref(
                                Register(3),
                                IRType::Func(
                                    vec![IRType::TypeVar("T3".into())],
                                    IRType::TypeVar("T3".into()).into()
                                ),
                                RefKind::Func("@_5_foo".into())
                            ),
                            // Alloc the closure
                            Instr::Alloc {
                                dest: Register(4),
                                ty: IRType::closure()
                            },
                            // Get a pointer to the env's address in the closure
                            Instr::GetElementPointer {
                                dest: Register(5),
                                from: Register(4),
                                ty: IRType::closure(),
                                index: 1
                            },
                            // Get a pointer to the fn's address in the closure
                            Instr::GetElementPointer {
                                dest: Register(6),
                                from: Register(4),
                                ty: IRType::closure(),
                                index: 0
                            },
                            // Store the env into the closure
                            Instr::Store {
                                ty: IRType::Pointer,
                                val: Register(2),
                                location: Register(5)
                            },
                            // Store the fn into the closure
                            Instr::Store {
                                ty: IRType::Pointer,
                                val: Register(3),
                                location: Register(6)
                            },
                            // Return a pointer to the closure
                            Instr::Ret(IRType::Pointer, Some(Register(4)))
                        ],
                    }],
                    env_ty: IRType::Struct(vec![])
                },
            ]
        )
    }

    #[test]
    fn lowers_int() {
        let lowered = lower("123").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Ret(IRType::Int, Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_float() {
        let lowered = lower("123.").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantFloat(Register(1), 123.),
                        Instr::Ret(IRType::Float, Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }],
        )
    }

    #[test]
    fn lowers_bools() {
        let lowered = lower("true\nfalse").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantBool(Register(1), true),
                        Instr::ConstantBool(Register(2), false),
                        Instr::Ret(IRType::Bool, Some(Register(2))),
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_add() {
        let lowered = lower("1 + 2").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 1),
                        Instr::ConstantInt(Register(2), 2),
                        Instr::Add(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_sub() {
        let lowered = lower("2 - 1").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 2),
                        Instr::ConstantInt(Register(2), 1),
                        Instr::Sub(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }],
        )
    }

    #[test]
    fn lowers_mul() {
        let lowered = lower("2 * 1").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 2),
                        Instr::ConstantInt(Register(2), 1),
                        Instr::Mul(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_div() {
        let lowered = lower("2 / 1").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 2),
                        Instr::ConstantInt(Register(2), 1),
                        Instr::Div(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_assignment() {
        let lowered = lower("let a = 123\na").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Ret(IRType::Int, Some(Register(1))),
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_if_expr_with_else() {
        let lowered = lower(
            "
            if true {
                123
            } else {
                456
            }

            789
       ",
        )
        .unwrap();

        let expected = vec![IRFunction {
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                // if block
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantBool(Register(1), true),
                        Instr::JumpUnless(Register(1), BasicBlockID(1)),
                        Instr::ConstantInt(Register(2), 123),
                        Instr::Jump(BasicBlockID(2)),
                    ],
                },
                // else block
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::ConstantInt(Register(3), 456),
                        Instr::Jump(BasicBlockID(2)),
                    ],
                },
                // converge block
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![
                        Instr::Phi(
                            Register(4),
                            IRType::Int,
                            PhiPredecessors(vec![
                                (Register(2), BasicBlockID(0)),
                                (Register(3), BasicBlockID(1)),
                            ]),
                        ),
                        Instr::ConstantInt(Register(5), 789),
                        Instr::Ret(IRType::Int, Some(Register(5))),
                    ],
                },
            ],
            env_ty: IRType::Struct(vec![]),
        }];

        assert_lowered_functions!(lowered, expected,);
    }

    #[test]
    fn lowers_basic_enum() {
        let lowered = lower(
            "enum Foo {
                case fizz, buzz
            }
            
            Foo.buzz",
        )
        .unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::TagVariant(Register(1), IRType::Enum(vec![]), 1, vec![].into()),
                        Instr::Ret(IRType::Enum(vec![]), Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_builtin_optional() {
        let lowered = lower("Optional.some(123)").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::TagVariant(
                            Register(2),
                            IRType::Enum(vec![IRType::Int]),
                            0,
                            RegisterList(vec![Register(1)])
                        ),
                        Instr::Ret(IRType::Enum(vec![IRType::Int]), Some(Register(2)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_match_ints() {
        let lowered = lower(
            "
        match 123 {
            123 -> 3.14,
            456 -> 2.71
        }
        ",
        )
        .unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // Add the scrutinee
                            Instr::ConstantInt(Register(1), 123),
                            // Add the first arm (register 1 is allocated for the return val of the match expr)
                            Instr::ConstantInt(Register(2), 123),
                            Instr::Eq(Register(3), IRType::Int, Register(1), Register(2)),
                            Instr::JumpIf(Register(3), BasicBlockID(2)),
                            // Add the second term
                            Instr::ConstantInt(Register(5), 456),
                            Instr::Eq(Register(6), IRType::Int, Register(1), Register(5)),
                            Instr::JumpIf(Register(6), BasicBlockID(3)),
                            // We should have jumped no matter what
                            Instr::Unreachable,
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(8),
                                IRType::Float,
                                PhiPredecessors(vec![
                                    (Register(4), BasicBlockID(2)),
                                    (Register(7), BasicBlockID(3))
                                ])
                            ),
                            Instr::Ret(IRType::Float, Some(Register(8)))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::ConstantFloat(Register(4), 3.14),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::ConstantFloat(Register(7), 2.71),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                ],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_match_bind() {
        let lowered = lower(
            "
        match Optional.some(123) {
            .some(x) -> x,
            .none -> 456
        }
        ",
        )
        .unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    // Block 0: Dispatch
                    BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // Scrutinee: Optional.some(123)
                            Instr::ConstantInt(Register(1), 123),
                            Instr::TagVariant(
                                Register(2),
                                IRType::Enum(vec![IRType::Int]),
                                0,
                                RegisterList(vec![Register(1)])
                            ),
                            // Check for first arm: .some(x)
                            Instr::GetEnumTag(Register(3), Register(2)),
                            Instr::ConstantInt(Register(4), 0), // Tag for .some
                            Instr::Eq(Register(5), IRType::Int, Register(3), Register(4)),
                            Instr::JumpIf(Register(5), BasicBlockID(2)),
                            // Check for second arm: .none
                            Instr::GetEnumTag(Register(7), Register(2)),
                            Instr::ConstantInt(Register(8), 1), // Tag for .none
                            Instr::Eq(Register(9), IRType::Int, Register(7), Register(8)),
                            Instr::JumpIf(Register(9), BasicBlockID(3)),
                            Instr::Unreachable,
                        ],
                    },
                    // Block 1: Merge Point
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(11),
                                IRType::Int,
                                PhiPredecessors(vec![
                                    (Register(6), BasicBlockID(2)),  // from .some arm
                                    (Register(10), BasicBlockID(3)), // from .none arm
                                ])
                            ),
                            Instr::Ret(IRType::Int, Some(Register(11))),
                        ]
                    },
                    // Block 2: Body for .some(x) -> x
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            // This is the binding: get value at index 0 and put it in register 8
                            Instr::GetEnumValue(Register(6), IRType::Int, Register(2), 0, 0),
                            Instr::Jump(BasicBlockID(1)),
                        ]
                    },
                    // Block 3: Body for .none -> 456
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::ConstantInt(Register(10), 456),
                            Instr::Jump(BasicBlockID(1)),
                        ]
                    },
                ],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    #[test]
    fn lowers_enum_match() {
        let lowered = lower(
            "
        enum Foo {
            case fizz, buzz
        }
        match Foo.buzz {
            .fizz -> 123,
            .buzz -> 456
        }
        ",
        )
        .unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // Add the scrutinee
                            Instr::TagVariant(Register(1), IRType::Enum(vec![]), 1, vec![].into()),
                            // Figure out what the scrutinee's tag is
                            Instr::GetEnumTag(Register(2), Register(1)),
                            // Put the .fizz's tag (0) into a register to compare
                            Instr::ConstantInt(Register(3), 0),
                            // Compare
                            Instr::Eq(Register(4), IRType::Int, Register(2), Register(3)),
                            // Jump if they're the same
                            Instr::JumpIf(Register(4), BasicBlockID(2)),
                            // Do it all over again for the other variant .buzz
                            Instr::GetEnumTag(Register(6), Register(1)),
                            Instr::ConstantInt(Register(7), 1),
                            Instr::Eq(Register(8), IRType::Int, Register(6), Register(7)),
                            Instr::JumpIf(Register(8), BasicBlockID(3)),
                            // We should have jumped no matter what
                            Instr::Unreachable,
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(10),
                                IRType::Int,
                                PhiPredecessors(vec![
                                    (Register(5), BasicBlockID(2)),
                                    (Register(9), BasicBlockID(3))
                                ])
                            ),
                            Instr::Ret(IRType::Int, Some(Register(10)))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::ConstantInt(Register(5), 123),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::ConstantInt(Register(9), 456),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                ],
                env_ty: IRType::Struct(vec![])
            }]
        )
    }

    // #[test]
    // fn lowers_captured_value() {
    //     let lowered = lower(
    //         "
    //     let x = 1
    //     func add(y) { x + y }
    //     add(2)
    //     ",
    //     )
    //     .unwrap();
    //     assert_lowered_functions!(
    //         lowered,
    //         vec![
    //             IRFunction {
    //                 ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
    //                 name: "@_5_aadd".into(),
    //                 blocks: vec![BasicBlock {
    //                     id: BasicBlockID(0),
    //                     instructions: vec![Instr::Ret(IRType::Int, Some(Register(1)))],
    //                 }],
    //                 env_ty: IRType::Struct(vec![])
    //             },
    //             IRFunction {
    //                 ty: IRType::Func(vec![], IRType::Void.into()),
    //                 name: "@main".into(),
    //                 blocks: vec![BasicBlock {
    //                     id: BasicBlockID(0),
    //                     instructions: vec![
    //                         Instr::Ref(
    //                             Register(1),
    //                             IRType::Func(vec![IRType::Int], IRType::Int.into()),
    //                             RefKind::Func("@_5_foo".into())
    //                         ),
    //                         Instr::Ret(
    //                             IRType::Func(vec![IRType::Int], IRType::Int.into()),
    //                             Some(Register(1))
    //                         )
    //                     ],
    //                 }],
    //                 env_ty: IRType::Struct(vec![])
    //             },
    //         ]
    //     )
    // }
    #[test]
    fn lowers_captured_value() {
        let lowered = lower(
            "
        let x = 1
        func add(y) { x + y }
        add(2)
        ",
        )
        .unwrap();

        // The function signature for `add` only includes its explicit parameters.
        let add_func_type = IRType::Func(vec![IRType::Int], Box::new(IRType::Int));
        let env_struct_type = IRType::Struct(vec![IRType::Int]);

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: add_func_type.clone(),
                    name: "@_5_add".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::GetElementPointer {
                                dest: Register(2),
                                ty: IRType::Int,
                                from: Register(0),
                                index: 0
                            },
                            Instr::Add(Register(3), IRType::Int, Register(2), Register(1)),
                            Instr::Ret(IRType::Int, Some(Register(3))),
                        ],
                    }],
                    env_ty: env_struct_type.clone(),
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // === Part 1: Setup `let x = 1` and environment ===
                            // The environment struct now holds the VALUE of x, not a pointer.
                            Instr::ConstantInt(Register(1), 1),
                            Instr::MakeStruct {
                                dest: Register(2),
                                ty: env_struct_type.clone(),
                                values: RegisterList(vec![Register(1)])
                            },
                            Instr::Alloc {
                                dest: Register(3),
                                ty: env_struct_type.clone()
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(3),
                                ty: env_struct_type.clone()
                            },
                            // %3 is now the env_ptr.

                            // === Part 2: Create the `add` closure ===
                            Instr::Ref(
                                Register(4),
                                add_func_type.clone(),
                                RefKind::Func("@_5_add".into())
                            ),
                            Instr::Alloc {
                                dest: Register(5),
                                ty: IRType::closure()
                            },
                            // Adhering to your specified GEP -> Store order
                            Instr::GetElementPointer {
                                dest: Register(6),
                                from: Register(5),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(7),
                                from: Register(5),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(4),
                                location: Register(7),
                                ty: IRType::Pointer
                            },
                            // %5 is the pointer to the `add` closure.

                            // === Part 3: Call `add(2)` ===
                            Instr::ConstantInt(Register(8), 2), // The argument `y`.
                            // Unpack the closure
                            Instr::GetElementPointer {
                                dest: Register(9),
                                from: Register(4),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(10),
                                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                                addr: Register(9)
                            },
                            Instr::GetElementPointer {
                                dest: Register(11),
                                from: Register(4),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(12),
                                ty: IRType::Pointer,
                                addr: Register(11)
                            }, // Load func_ptr
                            // Make the call. The `args` list includes the env_ptr (%11) and the explicit arg `y` (%8).
                            Instr::Call {
                                dest_reg: Register(13),
                                ty: IRType::Int,
                                callee: Register(10),
                                args: RegisterList(vec![Register(12), Register(8)]),
                            },
                            Instr::Ret(IRType::Int, Some(Register(13))),
                        ],
                    }],
                    env_ty: IRType::EMPTY_STRUCT,
                },
            ]
        )
    }
}
