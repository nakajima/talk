use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    ir::value::RecordId,
    node_id::NodeID,
    node_kinds::{
        expr::Expr,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    token_kind::TokenKind,
    types::{
        infer_row::Row,
        infer_ty::Ty,
        typed_ast::TypedExpr,
    },
};
use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Register(pub String);

#[derive(Debug, Clone)]
pub enum Value {
    Reg(u32),
    Int(i64),
    Float(f64),
    Bool(bool),
    Void,
    Uninit,
    Poison,
    Record(RecordId, Vec<Value>),
    RawPtr(usize),
    RawBuffer(Vec<u8>),
    Bind(usize),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Reg(a), Value::Reg(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Void, Value::Void) => true,
            (Value::Uninit, Value::Uninit) => true,
            (Value::Poison, Value::Poison) => true,
            (Value::Record(a, b), Value::Record(c, d)) => a == c && b == d,
            (Value::RawPtr(a), Value::RawPtr(b)) => a == b,
            (Value::RawBuffer(a), Value::RawBuffer(b)) => a == b,
            (Value::Bind(a), Value::Bind(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Value {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InlineIRInstructionKind {
    #[doc = "$dest = const $ty $val $meta"]
    Constant {
        dest: Register,
        ty: TypeAnnotation,
        val: Value,
    },
    #[doc = "$dest = cmp $ty $lhs $op $rhs $meta"]
    Cmp {
        dest: Register,
        lhs: Value,
        rhs: Value,
        ty: TypeAnnotation,
        op: TokenKind,
    },
    #[doc = "$dest = add $ty $a $b $meta"]
    Add {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = sub $ty $a $b $meta"]
    Sub {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = mul $ty $a $b $meta"]
    Mul {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = div $ty $a $b $meta"]
    Div {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = ref $ty $val"]
    Ref {
        dest: Register,
        ty: TypeAnnotation,
        val: Value,
    },
    #[doc = "$dest = call $ty $callee $args $meta"]
    Call {
        dest: Register,
        ty: TypeAnnotation,
        callee: Value,
        args: Vec<Value>,
    },
    #[doc = "$dest = record $ty $record $meta"]
    Record {
        dest: Register,
        ty: TypeAnnotation,
        record: Vec<Value>,
    },
    #[doc = "$dest = getfield $ty $record $field $meta"]
    GetField {
        dest: Register,
        ty: TypeAnnotation,
        record: Register,
        field: Value,
    },
    #[doc = "setfield $ty $record $field $val $meta"]
    SetField {
        dest: Register,
        val: Value,
        ty: TypeAnnotation,
        record: Register,
        field: Value,
    },
    #[doc = "_print $val"]
    _Print { val: Value },
    #[doc = "$dest = alloc $ty $count"]
    Alloc {
        dest: Register,
        ty: TypeAnnotation,
        count: Value,
    },
    #[doc = "free $addr"]
    Free { addr: Value },
    #[doc = "$dest = load $ty $addr"]
    Load {
        dest: Register,
        ty: TypeAnnotation,
        addr: Value,
    },
    #[doc = "store $ty $value $addr"]
    Store {
        value: Value,
        ty: TypeAnnotation,
        addr: Value,
    },
    #[doc = "move $ty $from $to"]
    Move {
        from: Value,
        ty: TypeAnnotation,
        to: Value,
    },
    #[doc = "copy $ty $from $to $length"]
    Copy {
        ty: TypeAnnotation,
        from: Value,
        to: Value,
        length: Value,
    },
    #[doc = "$dest = gep $ty $addr $offset_index"]
    Gep {
        dest: Register,
        ty: TypeAnnotation,
        addr: Value,
        offset_index: Value,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct InlineIRInstruction {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    pub binds: Vec<Expr>,
    #[drive(skip)]
    pub instr_name_span: Span,
    #[drive(skip)]
    pub kind: InlineIRInstructionKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedInlineIRInstruction {
    pub id: NodeID,
    pub span: Span,
    pub binds: Vec<TypedExpr>,
    pub instr_name_span: Span,
    pub kind: InlineIRInstructionKind,
}

impl TypedInlineIRInstruction {
    pub fn mapping(
        self,
        m: &mut impl FnMut(Ty) -> Ty,
        r: &mut impl FnMut(Row) -> Row,
    ) -> Self {
        TypedInlineIRInstruction {
            id: self.id,
            span: self.span,
            binds: self.binds.into_iter().map(|b| b.mapping(m, r)).collect(),
            instr_name_span: self.instr_name_span,
            kind: self.kind,
        }
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Reg(reg) => write!(f, "%{reg}"),
            Value::Int(int) => write!(f, "{int}"),
            Value::Float(float) => write!(f, "{float}"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Void => write!(f, "()"),
            Value::Uninit => write!(f, "uninit"),
            Value::Poison => write!(f, "poison"),
            Value::Record(sym, fields) => write!(f, "{sym:?} {{ {:?} }}", fields),
            Value::RawPtr(ptr) => write!(f, "rawptr({})", ptr),
            Value::RawBuffer(buffer) => write!(f, "[{:?}]", buffer),
            Value::Bind(i) => write!(f, "${i}"),
        }
    }
}

impl TypeAnnotation {
    fn simple_display(&self) -> String {
        match &self.kind {
            TypeAnnotationKind::Nominal { name, .. } => name.name_str(),
            TypeAnnotationKind::SelfType(name) => name.name_str(),
            #[allow(clippy::todo)]
            _ => todo!(),
        }
    }
}

impl Display for InlineIRInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            InlineIRInstructionKind::Constant { dest, ty, val } => {
                write!(f, "{dest} = const {} {val}", ty.simple_display())
            }
            InlineIRInstructionKind::Cmp {
                dest,
                lhs,
                rhs,
                ty,
                op,
            } => write!(
                f,
                "{dest} = cmp {} {} {} {}",
                ty.simple_display(),
                lhs,
                op,
                rhs
            ),
            InlineIRInstructionKind::Add { dest, ty, a, b } => {
                write!(f, "{dest} = add {} {} {}", ty.simple_display(), a, b)
            }
            InlineIRInstructionKind::Sub { dest, ty, a, b } => {
                write!(f, "{dest} = sub {} {} {}", ty.simple_display(), a, b)
            }
            InlineIRInstructionKind::Mul { dest, ty, a, b } => {
                write!(f, "{dest} = mul {} {} {}", ty.simple_display(), a, b)
            }
            InlineIRInstructionKind::Div { dest, ty, a, b } => {
                write!(f, "{dest} = div {} {} {}", ty.simple_display(), a, b)
            }
            InlineIRInstructionKind::Ref { dest, ty, val } => {
                write!(f, "{dest} = ref {} {}", ty.simple_display(), val)
            }
            InlineIRInstructionKind::Call {
                dest,
                ty,
                callee,
                args,
            } => write!(
                f,
                "{dest} = call {} {} {{{}}}",
                ty.simple_display(),
                callee,
                args.iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            InlineIRInstructionKind::Record { dest, ty, record } => write!(
                f,
                "{dest} = record {} {{{}}}",
                ty.simple_display(),
                record
                    .iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            InlineIRInstructionKind::GetField {
                dest,
                ty,
                record,
                field,
            } => write!(
                f,
                "{dest} = getfield {} {} {}",
                ty.simple_display(),
                record,
                field
            ),
            InlineIRInstructionKind::SetField {
                dest,
                val,
                ty,
                record,
                field,
            } => write!(
                f,
                "setfield {dest} {} {} {} {}",
                ty.simple_display(),
                record,
                field,
                val
            ),
            InlineIRInstructionKind::_Print { val } => write!(f, "_print {}", val),
            InlineIRInstructionKind::Alloc { dest, ty, count } => {
                write!(f, "{dest} = alloc {} {}", ty.simple_display(), count)
            }
            InlineIRInstructionKind::Free { addr } => write!(f, "free {}", addr),
            InlineIRInstructionKind::Load { dest, ty, addr } => {
                write!(f, "{dest} = load {} {}", ty.simple_display(), addr)
            }
            InlineIRInstructionKind::Store { value, ty, addr } => {
                write!(f, "store {} {} {}", ty.simple_display(), value, addr)
            }
            InlineIRInstructionKind::Move { from, ty, to } => {
                write!(f, "move {} {} {}", ty.simple_display(), from, to)
            }
            InlineIRInstructionKind::Copy {
                ty,
                from,
                to,
                length,
            } => {
                write!(f, "copy {} {} {} {}", ty.simple_display(), from, to, length)
            }
            InlineIRInstructionKind::Gep {
                dest,
                ty,
                addr,
                offset_index,
            } => {
                write!(
                    f,
                    "{dest} = gep {} {} {}",
                    ty.simple_display(),
                    addr,
                    offset_index
                )
            }
        }
    }
}

impl_into_node!(InlineIRInstruction);
