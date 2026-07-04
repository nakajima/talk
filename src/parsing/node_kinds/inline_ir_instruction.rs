use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{
        expr::Expr,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    token_kind::TokenKind,
};
use std::fmt::Display;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RecordId {
    Nominal(Symbol),
    Record(u32),
    Anon,
}

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
    #[doc = "$dest = cmp $ty $lhs $op $rhs"]
    Cmp {
        dest: Register,
        lhs: Value,
        rhs: Value,
        ty: TypeAnnotation,
        op: TokenKind,
    },
    #[doc = "$dest = add $ty $a $b"]
    Add {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = sub $ty $a $b"]
    Sub {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = mul $ty $a $b"]
    Mul {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = div $ty $a $b"]
    Div {
        dest: Register,
        ty: TypeAnnotation,
        a: Value,
        b: Value,
    },
    #[doc = "$dest = alloc $ty $count"]
    Alloc {
        dest: Register,
        ty: TypeAnnotation,
        count: Value,
    },
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
    #[doc = "$dest = io_write $fd $buf $count"]
    IoWrite {
        dest: Register,
        fd: Value,
        buf: Value,
        count: Value,
    },
    #[doc = "$dest = trunc $val"]
    Trunc { dest: Register, val: Value },
    #[doc = "$dest = is_unique $ptr"]
    IsUnique { dest: Register, ptr: Value },
    #[doc = "$dest = itof $val"]
    IntToFloat { dest: Register, val: Value },
    #[doc = "$dest = btoi $val"]
    ByteToInt { dest: Register, val: Value },
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
            Value::Float(float) => {
                let s = format!("{float}");
                if s.contains('.') {
                    write!(f, "{s}")
                } else {
                    write!(f, "{s}.0")
                }
            }
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
            TypeAnnotationKind::Borrow { mutable, inner } => {
                if *mutable {
                    format!("&mut {}", inner.simple_display())
                } else {
                    format!("&{}", inner.simple_display())
                }
            }
            TypeAnnotationKind::Unique { inner } => {
                format!("*{}", inner.simple_display())
            }
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                if generics.is_empty() {
                    name.name_str()
                } else {
                    let args = generics
                        .iter()
                        .map(TypeAnnotation::simple_display)
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{args}>", name.name_str())
                }
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } => {
                if member_generics.is_empty() {
                    format!("{}.{}", base.simple_display(), member)
                } else {
                    let args = member_generics
                        .iter()
                        .map(TypeAnnotation::simple_display)
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}.{}<{args}>", base.simple_display(), member)
                }
            }
            TypeAnnotationKind::SelfType(name) => name.name_str(),
            TypeAnnotationKind::Func { params, returns } => {
                let params = params
                    .iter()
                    .map(TypeAnnotation::simple_display)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({params}) -> {}", returns.simple_display())
            }
            TypeAnnotationKind::Tuple(items) => {
                let items = items
                    .iter()
                    .map(TypeAnnotation::simple_display)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            TypeAnnotationKind::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| {
                        format!(
                            "{}: {}",
                            field.label.name_str(),
                            field.value.simple_display()
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{ {fields} }}")
            }
            TypeAnnotationKind::Any {
                protocol,
                assoc_bindings,
            } => {
                if assoc_bindings.is_empty() {
                    format!("any {}", protocol.simple_display())
                } else {
                    let bindings = assoc_bindings
                        .iter()
                        .map(|binding| {
                            format!(
                                "{} = {}",
                                binding.name.name_str(),
                                binding.value.simple_display()
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("any {}<{bindings}>", protocol.simple_display())
                }
            }
        }
    }
}

impl Display for InlineIRInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
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
            InlineIRInstructionKind::Alloc { dest, ty, count } => {
                write!(f, "{dest} = alloc {} {}", ty.simple_display(), count)
            }
            InlineIRInstructionKind::Load { dest, ty, addr } => {
                write!(f, "{dest} = load {} {}", ty.simple_display(), addr)
            }
            InlineIRInstructionKind::Store { value, ty, addr } => {
                write!(f, "store {} {} {}", ty.simple_display(), value, addr)
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
            InlineIRInstructionKind::IoWrite {
                dest,
                fd,
                buf,
                count,
            } => write!(f, "{dest} = io_write {} {} {}", fd, buf, count),
            InlineIRInstructionKind::Trunc { dest, val } => {
                write!(f, "{dest} = trunc {}", val)
            }
            InlineIRInstructionKind::IsUnique { dest, ptr } => {
                write!(f, "{dest} = is_unique {}", ptr)
            }
            InlineIRInstructionKind::IntToFloat { dest, val } => {
                write!(f, "{dest} = itof {}", val)
            }
            InlineIRInstructionKind::ByteToInt { dest, val } => {
                write!(f, "{dest} = btoi {}", val)
            }
        }
    }
}

impl_into_node!(InlineIRInstruction);
