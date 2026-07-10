use crate::CmpOp;
use crate::interp::Value;
use crate::symbol::{LocalSymbolId, ModuleId, ModuleSymbolId, Symbol};
use crate::{Chunk, Insn, IoOp, MemKind, Module};

const MAGIC: &[u8; 7] = b"TALKBC\0";
const FORMAT_VERSION: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodeError {
    UnsupportedConstant(&'static str),
    TooManyItems(&'static str),
    StringTooLong,
}

impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedConstant(kind) => {
                write!(f, "unsupported bytecode constant: {kind}")
            }
            Self::TooManyItems(section) => {
                write!(f, "too many items in bytecode section: {section}")
            }
            Self::StringTooLong => write!(f, "string is too long to encode in bytecode"),
        }
    }
}

impl std::error::Error for EncodeError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    TooShort,
    BadMagic,
    UnsupportedVersion(u32),
    UnexpectedEof,
    InvalidUtf8,
    InvalidTag(&'static str, u8),
    TrailingBytes,
    InvalidIndex(&'static str),
    IntegerOverflow,
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooShort => write!(f, "bytecode image is too short"),
            Self::BadMagic => write!(f, "bytecode image has invalid magic"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported Talk bytecode version {version}")
            }
            Self::UnexpectedEof => write!(f, "unexpected end of bytecode image"),
            Self::InvalidUtf8 => write!(f, "bytecode image contains invalid UTF-8"),
            Self::InvalidTag(section, tag) => write!(f, "invalid {section} tag {tag}"),
            Self::TrailingBytes => write!(f, "bytecode image has trailing bytes"),
            Self::InvalidIndex(kind) => write!(f, "bytecode image contains invalid {kind} index"),
            Self::IntegerOverflow => write!(f, "bytecode integer conversion overflowed"),
        }
    }
}

impl std::error::Error for DecodeError {}

impl Module {
    pub fn encode_bytecode(&self) -> Result<Vec<u8>, EncodeError> {
        let mut encoder = Encoder { bytes: Vec::new() };
        encoder.module(self)?;
        Ok(encoder.bytes)
    }

    pub fn decode_bytecode(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut decoder = Decoder { bytes, cursor: 0 };
        let module = decoder.module()?;
        if decoder.cursor != decoder.bytes.len() {
            return Err(DecodeError::TrailingBytes);
        }
        module.validate()?;
        Ok(module)
    }
}

struct Encoder {
    bytes: Vec<u8>,
}

impl Encoder {
    fn module(&mut self, module: &Module) -> Result<(), EncodeError> {
        self.bytes.extend_from_slice(MAGIC);
        self.u32(FORMAT_VERSION);
        self.u32(module.entry);
        self.chunks(&module.chunks)?;
        self.consts(&module.consts)?;
        self.u16_vec("arg_pool", &module.arg_pool)?;
        self.u32_vec("switch_pool", &module.switch_pool)?;
        self.strings("traps", &module.traps)?;
        self.bytes("statics", &module.statics)?;
        Ok(())
    }

    fn chunks(&mut self, chunks: &[Chunk]) -> Result<(), EncodeError> {
        self.len("chunks", chunks.len())?;
        for chunk in chunks {
            self.string(&chunk.name)?;
            self.u16(chunk.arity);
            self.u16(chunk.n_regs);
            self.len("code", chunk.code.len())?;
            for insn in &chunk.code {
                self.insn(*insn);
            }
        }
        Ok(())
    }

    fn consts(&mut self, consts: &[Value]) -> Result<(), EncodeError> {
        self.len("consts", consts.len())?;
        for value in consts {
            self.value(value)?;
        }
        Ok(())
    }

    fn value(&mut self, value: &Value) -> Result<(), EncodeError> {
        match value {
            Value::I64(v) => {
                self.u8(0);
                self.i64(*v);
            }
            Value::F64(v) => {
                self.u8(1);
                self.u64(v.to_bits());
            }
            Value::Bool(v) => {
                self.u8(2);
                self.u8(u8::from(*v));
            }
            Value::Byte(v) => {
                self.u8(3);
                self.u8(*v);
            }
            Value::Void => self.u8(4),
            Value::Ptr(v) => {
                self.u8(5);
                self.u32(*v);
            }
            Value::Record(..) => return Err(EncodeError::UnsupportedConstant("record")),
            Value::Tuple(..) => return Err(EncodeError::UnsupportedConstant("tuple")),
            Value::Variant(..) => return Err(EncodeError::UnsupportedConstant("variant")),
            Value::Existential(..) => return Err(EncodeError::UnsupportedConstant("existential")),
            Value::Closure(..) => return Err(EncodeError::UnsupportedConstant("closure")),
            Value::Cell(..) => return Err(EncodeError::UnsupportedConstant("cell")),
            Value::Object(..) => return Err(EncodeError::UnsupportedConstant("object")),
            Value::Cont(..) => return Err(EncodeError::UnsupportedConstant("continuation")),
        }
        Ok(())
    }

    fn insn(&mut self, insn: Insn) {
        match insn {
            Insn::Const { dest, k } => {
                self.u8(0);
                self.u16(dest);
                self.u32(k);
            }
            Insn::Move { dest, src } => {
                self.u8(1);
                self.u16(dest);
                self.u16(src);
            }
            Insn::Add { dest, a, b } => self.reg3(2, dest, a, b),
            Insn::Sub { dest, a, b } => self.reg3(3, dest, a, b),
            Insn::Mul { dest, a, b } => self.reg3(4, dest, a, b),
            Insn::Div { dest, a, b } => self.reg3(5, dest, a, b),
            Insn::Cmp { dest, a, b, op } => {
                self.u8(6);
                self.u16(dest);
                self.u16(a);
                self.u16(b);
                self.cmp_op(op);
            }
            Insn::Trunc { dest, src } => self.reg2(7, dest, src),
            Insn::IToF { dest, src } => self.reg2(8, dest, src),
            Insn::BToI { dest, src } => self.reg2(48, dest, src),
            Insn::CellNew { dest, init } => self.reg2(9, dest, init),
            Insn::CellGet { dest, cell } => self.reg2(10, dest, cell),
            Insn::CellSet { cell, src } => self.reg2(11, cell, src),
            Insn::RecordNew {
                dest,
                symbol,
                args_start,
                args_len,
            } => {
                self.u8(12);
                self.u16(dest);
                self.symbol(symbol);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::GetField { dest, rec, index } => {
                self.u8(13);
                self.u16(dest);
                self.u16(rec);
                self.u16(index);
            }
            Insn::VariantNew {
                dest,
                symbol,
                tag,
                args_start,
                args_len,
            } => {
                self.u8(14);
                self.u16(dest);
                self.symbol(symbol);
                self.u16(tag);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::GetTag { dest, src } => self.reg2(15, dest, src),
            Insn::GetPayload { dest, src, index } => {
                self.u8(16);
                self.u16(dest);
                self.u16(src);
                self.u16(index);
            }
            Insn::ExistentialPack {
                dest,
                protocol,
                args_start,
                args_len,
            } => {
                self.u8(17);
                self.u16(dest);
                self.symbol(protocol);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::ExistentialWitness { dest, src, index } => {
                self.u8(18);
                self.u16(dest);
                self.u16(src);
                self.u16(index);
            }
            Insn::ExistentialPayload { dest, src } => self.reg2(19, dest, src),
            Insn::TupleNew {
                dest,
                args_start,
                args_len,
            } => {
                self.u8(20);
                self.u16(dest);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::Extract { dest, src, index } => {
                self.u8(21);
                self.u16(dest);
                self.u16(src);
                self.u16(index);
            }
            Insn::SetField {
                dest,
                rec,
                src,
                index,
            } => {
                self.u8(22);
                self.u16(dest);
                self.u16(rec);
                self.u16(src);
                self.u16(index);
            }
            Insn::Alloc { dest, count } => self.reg2(23, dest, count),
            Insn::Free { dest, ptr } => self.reg2(24, dest, ptr),
            Insn::Retain { dest, ptr } => self.reg2(38, dest, ptr),
            Insn::IsUnique { dest, ptr } => self.reg2(39, dest, ptr),
            Insn::ObjectNew {
                dest,
                args_start,
                args_len,
            } => {
                self.u8(40);
                self.u16(dest);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::SetFinalizer { obj, closure } => self.reg2(41, obj, closure),
            Insn::ObjectGet { dest, obj, index } => self.reg3(42, dest, obj, index),
            Insn::ObjectSet { obj, src, index } => self.reg3(43, obj, src, index),
            Insn::RegionAcquire { dest, src } => self.reg2(44, dest, src),
            Insn::RegionRelease { dest, src } => self.reg2(45, dest, src),
            Insn::MakeCont { dest } => {
                self.u8(46);
                self.u16(dest);
            }
            Insn::CallCont { callee, src } => self.reg2(47, callee, src),
            Insn::Load { dest, ptr, kind } => {
                self.u8(25);
                self.u16(dest);
                self.u16(ptr);
                self.mem_kind(kind);
            }
            Insn::Store { ptr, src, kind } => {
                self.u8(26);
                self.u16(ptr);
                self.u16(src);
                self.mem_kind(kind);
            }
            Insn::Copy { from, to, len } => self.reg3(27, from, to, len),
            Insn::Swap { a, b, kind } => {
                self.u8(49);
                self.u16(a);
                self.u16(b);
                self.mem_kind(kind);
            }
            Insn::Io { dest, op, a, b, c } => {
                self.u8(28);
                self.u16(dest);
                self.io_op(op);
                self.u16(a);
                self.u16(b);
                self.u16(c);
            }
            Insn::Call {
                dest,
                chunk,
                args_start,
                args_len,
            } => self.call_like(29, dest, chunk, args_start, args_len),
            Insn::MakeClosure {
                dest,
                chunk,
                args_start,
                args_len,
            } => self.call_like(30, dest, chunk, args_start, args_len),
            Insn::EnvGet { dest, index } => self.reg2(31, dest, index),
            Insn::CallIndirect {
                dest,
                callee,
                args_start,
                args_len,
            } => {
                self.u8(32);
                self.u16(dest);
                self.u16(callee);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::Jump { target } => {
                self.u8(33);
                self.u32(target);
            }
            Insn::Branch {
                cond,
                then_target,
                else_target,
            } => {
                self.u8(34);
                self.u16(cond);
                self.u32(then_target);
                self.u32(else_target);
            }
            Insn::Switch {
                tag,
                targets_start,
                targets_len,
            } => {
                self.u8(35);
                self.u16(tag);
                self.u32(targets_start);
                self.u16(targets_len);
            }
            Insn::Ret { src } => {
                self.u8(36);
                self.u16(src);
            }
            Insn::Trap { message } => {
                self.u8(37);
                self.u32(message);
            }
        }
    }

    fn call_like(&mut self, tag: u8, dest: u16, chunk: u32, args_start: u32, args_len: u16) {
        self.u8(tag);
        self.u16(dest);
        self.u32(chunk);
        self.u32(args_start);
        self.u16(args_len);
    }

    fn reg2(&mut self, tag: u8, a: u16, b: u16) {
        self.u8(tag);
        self.u16(a);
        self.u16(b);
    }

    fn reg3(&mut self, tag: u8, a: u16, b: u16, c: u16) {
        self.u8(tag);
        self.u16(a);
        self.u16(b);
        self.u16(c);
    }

    fn cmp_op(&mut self, op: CmpOp) {
        self.u8(match op {
            CmpOp::Eq => 0,
            CmpOp::Ne => 1,
            CmpOp::Lt => 2,
            CmpOp::Le => 3,
            CmpOp::Gt => 4,
            CmpOp::Ge => 5,
        });
    }

    fn mem_kind(&mut self, kind: MemKind) {
        self.u8(match kind {
            MemKind::Byte => 0,
            MemKind::I64 => 1,
            MemKind::F64 => 2,
            MemKind::Bool => 3,
            MemKind::Ptr => 4,
            MemKind::Boxed => 5,
        });
    }

    fn io_op(&mut self, op: IoOp) {
        self.u8(match op {
            IoOp::Read => 0,
            IoOp::Write => 1,
            IoOp::Open => 2,
            IoOp::Close => 3,
            IoOp::Sleep => 4,
            IoOp::Poll => 5,
            IoOp::Ctl => 6,
            IoOp::Socket => 7,
            IoOp::Bind => 8,
            IoOp::Listen => 9,
            IoOp::Connect => 10,
            IoOp::Accept => 11,
            IoOp::CwdLen => 12,
            IoOp::CwdCopy => 13,
            IoOp::GetenvLen => 14,
            IoOp::GetenvCopy => 15,
            IoOp::Argc => 16,
            IoOp::ArgLen => 17,
            IoOp::ArgCopy => 18,
            IoOp::DirCount => 19,
            IoOp::DirEntryKind => 20,
            IoOp::DirEntryLen => 21,
            IoOp::DirEntryCopy => 22,
            IoOp::Exit => 23,
        });
    }

    fn symbol(&mut self, symbol: Symbol) {
        match symbol {
            Symbol::Struct(id) => self.module_symbol(0, id.module_id.0, id.local_id),
            Symbol::Enum(id) => self.module_symbol(1, id.module_id.0, id.local_id),
            Symbol::TypeAlias(id) => self.module_symbol(2, id.module_id.0, id.local_id),
            Symbol::TypeParameter(id) => self.module_symbol(3, id.module_id.0, id.local_id),
            Symbol::Global(id) => self.module_symbol(4, id.module_id.0, id.local_id),
            Symbol::DeclaredLocal(id) => self.local_symbol(5, id.0),
            Symbol::PatternBindLocal(id) => self.local_symbol(6, id.0),
            Symbol::ParamLocal(id) => self.local_symbol(7, id.0),
            Symbol::Builtin(id) => self.module_symbol(8, id.module_id.0, id.local_id),
            Symbol::Property(id) => self.module_symbol(9, id.module_id.0, id.local_id),
            Symbol::Synthesized(id) => self.module_symbol(10, id.module_id.0, id.local_id),
            Symbol::InstanceMethod(id) => self.module_symbol(11, id.module_id.0, id.local_id),
            Symbol::Initializer(id) => self.module_symbol(12, id.module_id.0, id.local_id),
            Symbol::StaticMethod(id) => self.module_symbol(13, id.module_id.0, id.local_id),
            Symbol::Variant(id) => self.module_symbol(14, id.module_id.0, id.local_id),
            Symbol::Protocol(id) => self.module_symbol(15, id.module_id.0, id.local_id),
            Symbol::AssociatedType(id) => self.module_symbol(16, id.module_id.0, id.local_id),
            Symbol::MethodRequirement(id) => self.module_symbol(17, id.module_id.0, id.local_id),
            Symbol::Effect(id) => self.module_symbol(18, id.module_id.0, id.local_id),
            Symbol::Main => self.local_symbol(19, 0),
            Symbol::Library => self.local_symbol(20, 0),
        }
    }

    fn module_symbol(&mut self, tag: u8, module_id: u16, local_id: u32) {
        self.u8(tag);
        self.u16(module_id);
        self.u32(local_id);
    }

    fn local_symbol(&mut self, tag: u8, local_id: u32) {
        self.u8(tag);
        self.u32(local_id);
    }

    fn strings(&mut self, section: &'static str, strings: &[String]) -> Result<(), EncodeError> {
        self.len(section, strings.len())?;
        for string in strings {
            self.string(string)?;
        }
        Ok(())
    }

    fn string(&mut self, value: &str) -> Result<(), EncodeError> {
        self.bytes("string", value.as_bytes())
    }

    fn bytes(&mut self, section: &'static str, bytes: &[u8]) -> Result<(), EncodeError> {
        self.len(section, bytes.len())?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }

    fn u16_vec(&mut self, section: &'static str, values: &[u16]) -> Result<(), EncodeError> {
        self.len(section, values.len())?;
        for value in values {
            self.u16(*value);
        }
        Ok(())
    }

    fn u32_vec(&mut self, section: &'static str, values: &[u32]) -> Result<(), EncodeError> {
        self.len(section, values.len())?;
        for value in values {
            self.u32(*value);
        }
        Ok(())
    }

    fn len(&mut self, section: &'static str, len: usize) -> Result<(), EncodeError> {
        let len = u32::try_from(len).map_err(|_| EncodeError::TooManyItems(section))?;
        self.u32(len);
        Ok(())
    }

    fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }
}

struct Decoder<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl<'a> Decoder<'a> {
    fn module(&mut self) -> Result<Module, DecodeError> {
        if self.bytes.len() < MAGIC.len() + 4 {
            return Err(DecodeError::TooShort);
        }
        let magic = self.take(MAGIC.len())?;
        if magic != MAGIC {
            return Err(DecodeError::BadMagic);
        }
        let version = self.u32()?;
        if version != FORMAT_VERSION {
            return Err(DecodeError::UnsupportedVersion(version));
        }
        let entry = self.u32()?;
        let chunks = self.chunks()?;
        let consts = self.consts()?;
        let arg_pool = self.u16_vec()?;
        let switch_pool = self.u32_vec()?;
        let traps = self.strings()?;
        let statics = self.byte_vec()?;
        Ok(Module {
            chunks,
            consts,
            arg_pool,
            switch_pool,
            traps,
            statics,
            entry,
        })
    }

    fn chunks(&mut self) -> Result<Vec<Chunk>, DecodeError> {
        let len = self.len()?;
        let mut chunks = Vec::with_capacity(len);
        for _ in 0..len {
            let name = self.string()?;
            let arity = self.u16()?;
            let n_regs = self.u16()?;
            let code_len = self.len()?;
            let mut code = Vec::with_capacity(code_len);
            for _ in 0..code_len {
                code.push(self.insn()?);
            }
            chunks.push(Chunk {
                name,
                code,
                arity,
                n_regs,
            });
        }
        Ok(chunks)
    }

    fn consts(&mut self) -> Result<Vec<Value>, DecodeError> {
        let len = self.len()?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.value()?);
        }
        Ok(values)
    }

    fn value(&mut self) -> Result<Value, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(Value::I64(self.i64()?)),
            1 => Ok(Value::F64(f64::from_bits(self.u64()?))),
            2 => Ok(Value::Bool(self.bool()?)),
            3 => Ok(Value::Byte(self.u8()?)),
            4 => Ok(Value::Void),
            5 => Ok(Value::Ptr(self.u32()?)),
            _ => Err(DecodeError::InvalidTag("constant", tag)),
        }
    }

    fn insn(&mut self) -> Result<Insn, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(Insn::Const {
                dest: self.u16()?,
                k: self.u32()?,
            }),
            1 => Ok(Insn::Move {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            2 => self.reg3(|dest, a, b| Insn::Add { dest, a, b }),
            3 => self.reg3(|dest, a, b| Insn::Sub { dest, a, b }),
            4 => self.reg3(|dest, a, b| Insn::Mul { dest, a, b }),
            5 => self.reg3(|dest, a, b| Insn::Div { dest, a, b }),
            6 => Ok(Insn::Cmp {
                dest: self.u16()?,
                a: self.u16()?,
                b: self.u16()?,
                op: self.cmp_op()?,
            }),
            7 => Ok(Insn::Trunc {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            8 => Ok(Insn::IToF {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            9 => Ok(Insn::CellNew {
                dest: self.u16()?,
                init: self.u16()?,
            }),
            10 => Ok(Insn::CellGet {
                dest: self.u16()?,
                cell: self.u16()?,
            }),
            11 => Ok(Insn::CellSet {
                cell: self.u16()?,
                src: self.u16()?,
            }),
            12 => Ok(Insn::RecordNew {
                dest: self.u16()?,
                symbol: self.symbol()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            13 => Ok(Insn::GetField {
                dest: self.u16()?,
                rec: self.u16()?,
                index: self.u16()?,
            }),
            14 => Ok(Insn::VariantNew {
                dest: self.u16()?,
                symbol: self.symbol()?,
                tag: self.u16()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            15 => Ok(Insn::GetTag {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            16 => Ok(Insn::GetPayload {
                dest: self.u16()?,
                src: self.u16()?,
                index: self.u16()?,
            }),
            17 => Ok(Insn::ExistentialPack {
                dest: self.u16()?,
                protocol: self.symbol()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            18 => Ok(Insn::ExistentialWitness {
                dest: self.u16()?,
                src: self.u16()?,
                index: self.u16()?,
            }),
            19 => Ok(Insn::ExistentialPayload {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            20 => Ok(Insn::TupleNew {
                dest: self.u16()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            21 => Ok(Insn::Extract {
                dest: self.u16()?,
                src: self.u16()?,
                index: self.u16()?,
            }),
            22 => Ok(Insn::SetField {
                dest: self.u16()?,
                rec: self.u16()?,
                src: self.u16()?,
                index: self.u16()?,
            }),
            23 => Ok(Insn::Alloc {
                dest: self.u16()?,
                count: self.u16()?,
            }),
            24 => Ok(Insn::Free {
                dest: self.u16()?,
                ptr: self.u16()?,
            }),
            25 => Ok(Insn::Load {
                dest: self.u16()?,
                ptr: self.u16()?,
                kind: self.mem_kind()?,
            }),
            26 => Ok(Insn::Store {
                ptr: self.u16()?,
                src: self.u16()?,
                kind: self.mem_kind()?,
            }),
            27 => Ok(Insn::Copy {
                from: self.u16()?,
                to: self.u16()?,
                len: self.u16()?,
            }),
            28 => Ok(Insn::Io {
                dest: self.u16()?,
                op: self.io_op()?,
                a: self.u16()?,
                b: self.u16()?,
                c: self.u16()?,
            }),
            29 => Ok(Insn::Call {
                dest: self.u16()?,
                chunk: self.u32()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            30 => Ok(Insn::MakeClosure {
                dest: self.u16()?,
                chunk: self.u32()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            31 => Ok(Insn::EnvGet {
                dest: self.u16()?,
                index: self.u16()?,
            }),
            32 => Ok(Insn::CallIndirect {
                dest: self.u16()?,
                callee: self.u16()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            33 => Ok(Insn::Jump {
                target: self.u32()?,
            }),
            34 => Ok(Insn::Branch {
                cond: self.u16()?,
                then_target: self.u32()?,
                else_target: self.u32()?,
            }),
            35 => Ok(Insn::Switch {
                tag: self.u16()?,
                targets_start: self.u32()?,
                targets_len: self.u16()?,
            }),
            36 => Ok(Insn::Ret { src: self.u16()? }),
            38 => Ok(Insn::Retain {
                dest: self.u16()?,
                ptr: self.u16()?,
            }),
            39 => Ok(Insn::IsUnique {
                dest: self.u16()?,
                ptr: self.u16()?,
            }),
            37 => Ok(Insn::Trap {
                message: self.u32()?,
            }),
            40 => Ok(Insn::ObjectNew {
                dest: self.u16()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            41 => Ok(Insn::SetFinalizer {
                obj: self.u16()?,
                closure: self.u16()?,
            }),
            42 => self.reg3(|dest, obj, index| Insn::ObjectGet { dest, obj, index }),
            43 => self.reg3(|obj, src, index| Insn::ObjectSet { obj, src, index }),
            44 => Ok(Insn::RegionAcquire {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            45 => Ok(Insn::RegionRelease {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            46 => Ok(Insn::MakeCont { dest: self.u16()? }),
            47 => Ok(Insn::CallCont {
                callee: self.u16()?,
                src: self.u16()?,
            }),
            48 => Ok(Insn::BToI {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            49 => Ok(Insn::Swap {
                a: self.u16()?,
                b: self.u16()?,
                kind: self.mem_kind()?,
            }),
            _ => Err(DecodeError::InvalidTag("instruction", tag)),
        }
    }

    fn reg3<F>(&mut self, build: F) -> Result<Insn, DecodeError>
    where
        F: FnOnce(u16, u16, u16) -> Insn,
    {
        Ok(build(self.u16()?, self.u16()?, self.u16()?))
    }

    fn cmp_op(&mut self) -> Result<CmpOp, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(CmpOp::Eq),
            1 => Ok(CmpOp::Ne),
            2 => Ok(CmpOp::Lt),
            3 => Ok(CmpOp::Le),
            4 => Ok(CmpOp::Gt),
            5 => Ok(CmpOp::Ge),
            _ => Err(DecodeError::InvalidTag("comparison operator", tag)),
        }
    }

    fn mem_kind(&mut self) -> Result<MemKind, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(MemKind::Byte),
            1 => Ok(MemKind::I64),
            2 => Ok(MemKind::F64),
            3 => Ok(MemKind::Bool),
            4 => Ok(MemKind::Ptr),
            5 => Ok(MemKind::Boxed),
            _ => Err(DecodeError::InvalidTag("memory kind", tag)),
        }
    }

    fn io_op(&mut self) -> Result<IoOp, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(IoOp::Read),
            1 => Ok(IoOp::Write),
            2 => Ok(IoOp::Open),
            3 => Ok(IoOp::Close),
            4 => Ok(IoOp::Sleep),
            5 => Ok(IoOp::Poll),
            6 => Ok(IoOp::Ctl),
            7 => Ok(IoOp::Socket),
            8 => Ok(IoOp::Bind),
            9 => Ok(IoOp::Listen),
            10 => Ok(IoOp::Connect),
            11 => Ok(IoOp::Accept),
            12 => Ok(IoOp::CwdLen),
            13 => Ok(IoOp::CwdCopy),
            14 => Ok(IoOp::GetenvLen),
            15 => Ok(IoOp::GetenvCopy),
            16 => Ok(IoOp::Argc),
            17 => Ok(IoOp::ArgLen),
            18 => Ok(IoOp::ArgCopy),
            19 => Ok(IoOp::DirCount),
            20 => Ok(IoOp::DirEntryKind),
            21 => Ok(IoOp::DirEntryLen),
            22 => Ok(IoOp::DirEntryCopy),
            23 => Ok(IoOp::Exit),
            _ => Err(DecodeError::InvalidTag("io operation", tag)),
        }
    }

    fn symbol(&mut self) -> Result<Symbol, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(Symbol::Struct(self.module_symbol()?)),
            1 => Ok(Symbol::Enum(self.module_symbol()?)),
            2 => Ok(Symbol::TypeAlias(self.module_symbol()?)),
            3 => Ok(Symbol::TypeParameter(self.module_symbol()?)),
            4 => Ok(Symbol::Global(self.module_symbol()?)),
            5 => Ok(Symbol::DeclaredLocal(LocalSymbolId(self.u32()?))),
            6 => Ok(Symbol::PatternBindLocal(LocalSymbolId(self.u32()?))),
            7 => Ok(Symbol::ParamLocal(LocalSymbolId(self.u32()?))),
            8 => Ok(Symbol::Builtin(self.module_symbol()?)),
            9 => Ok(Symbol::Property(self.module_symbol()?)),
            10 => Ok(Symbol::Synthesized(self.module_symbol()?)),
            11 => Ok(Symbol::InstanceMethod(self.module_symbol()?)),
            12 => Ok(Symbol::Initializer(self.module_symbol()?)),
            13 => Ok(Symbol::StaticMethod(self.module_symbol()?)),
            14 => Ok(Symbol::Variant(self.module_symbol()?)),
            15 => Ok(Symbol::Protocol(self.module_symbol()?)),
            16 => Ok(Symbol::AssociatedType(self.module_symbol()?)),
            17 => Ok(Symbol::MethodRequirement(self.module_symbol()?)),
            18 => Ok(Symbol::Effect(self.module_symbol()?)),
            19 => {
                let _ = self.u32()?;
                Ok(Symbol::Main)
            }
            20 => {
                let _ = self.u32()?;
                Ok(Symbol::Library)
            }
            _ => Err(DecodeError::InvalidTag("symbol", tag)),
        }
    }

    fn module_symbol(&mut self) -> Result<ModuleSymbolId, DecodeError> {
        Ok(ModuleSymbolId::new(ModuleId(self.u16()?), self.u32()?))
    }

    fn strings(&mut self) -> Result<Vec<String>, DecodeError> {
        let len = self.len()?;
        let mut strings = Vec::with_capacity(len);
        for _ in 0..len {
            strings.push(self.string()?);
        }
        Ok(strings)
    }

    fn string(&mut self) -> Result<String, DecodeError> {
        let bytes = self.byte_vec()?;
        String::from_utf8(bytes).map_err(|_| DecodeError::InvalidUtf8)
    }

    fn u16_vec(&mut self) -> Result<Vec<u16>, DecodeError> {
        let len = self.len()?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.u16()?);
        }
        Ok(values)
    }

    fn u32_vec(&mut self) -> Result<Vec<u32>, DecodeError> {
        let len = self.len()?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.u32()?);
        }
        Ok(values)
    }

    fn byte_vec(&mut self) -> Result<Vec<u8>, DecodeError> {
        let len = self.len()?;
        Ok(self.take(len)?.to_vec())
    }

    fn len(&mut self) -> Result<usize, DecodeError> {
        usize::try_from(self.u32()?).map_err(|_| DecodeError::IntegerOverflow)
    }

    fn bool(&mut self) -> Result<bool, DecodeError> {
        let value = self.u8()?;
        match value {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(DecodeError::InvalidTag("bool", value)),
        }
    }

    fn u8(&mut self) -> Result<u8, DecodeError> {
        let bytes = self.take(1)?;
        Ok(bytes[0])
    }

    fn u16(&mut self) -> Result<u16, DecodeError> {
        let bytes = self.take(2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    fn u32(&mut self) -> Result<u32, DecodeError> {
        let bytes = self.take(4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn u64(&mut self) -> Result<u64, DecodeError> {
        let bytes = self.take(8)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    fn i64(&mut self) -> Result<i64, DecodeError> {
        let bytes = self.take(8)?;
        Ok(i64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], DecodeError> {
        let end = self
            .cursor
            .checked_add(len)
            .ok_or(DecodeError::IntegerOverflow)?;
        if end > self.bytes.len() {
            return Err(DecodeError::UnexpectedEof);
        }
        let slice = &self.bytes[self.cursor..end];
        self.cursor = end;
        Ok(slice)
    }
}

impl Module {
    fn validate(&self) -> Result<(), DecodeError> {
        if self.entry as usize >= self.chunks.len() {
            return Err(DecodeError::InvalidIndex("entry chunk"));
        }
        for chunk in &self.chunks {
            chunk.validate(self)?;
        }
        Ok(())
    }
}

impl Chunk {
    fn validate(&self, module: &Module) -> Result<(), DecodeError> {
        if self.arity > self.n_regs {
            return Err(DecodeError::InvalidIndex("chunk arity"));
        }
        for insn in &self.code {
            insn.validate(module, self.n_regs)?;
        }
        Ok(())
    }
}

impl Insn {
    fn validate(&self, module: &Module, n_regs: u16) -> Result<(), DecodeError> {
        match *self {
            Insn::Const { dest, k } => {
                Register::new(n_regs).check(dest)?;
                if k as usize >= module.consts.len() {
                    return Err(DecodeError::InvalidIndex("constant"));
                }
            }
            Insn::Move { dest, src }
            | Insn::Trunc { dest, src }
            | Insn::IToF { dest, src }
            | Insn::BToI { dest, src }
            | Insn::Extract { dest, src, .. }
            | Insn::GetPayload { dest, src, .. }
            | Insn::ExistentialWitness { dest, src, .. }
            | Insn::ExistentialPayload { dest, src }
            | Insn::CellGet { dest, cell: src }
            | Insn::CellNew { dest, init: src }
            | Insn::Alloc { dest, count: src }
            | Insn::Free { dest, ptr: src }
            | Insn::Retain { dest, ptr: src }
            | Insn::IsUnique { dest, ptr: src }
            | Insn::RegionAcquire { dest, src }
            | Insn::RegionRelease { dest, src }
            | Insn::CallCont { callee: dest, src }
            | Insn::EnvGet { dest, index: src } => {
                Register::new(n_regs).check_many(&[dest, src])?
            }
            Insn::MakeCont { dest } => Register::new(n_regs).check(dest)?,
            Insn::Add { dest, a, b }
            | Insn::Sub { dest, a, b }
            | Insn::Mul { dest, a, b }
            | Insn::Div { dest, a, b }
            | Insn::Cmp { dest, a, b, .. } => Register::new(n_regs).check_many(&[dest, a, b])?,
            Insn::CellSet { cell, src } => Register::new(n_regs).check_many(&[cell, src])?,
            Insn::RecordNew {
                dest,
                args_start,
                args_len,
                ..
            }
            | Insn::TupleNew {
                dest,
                args_start,
                args_len,
            }
            | Insn::ExistentialPack {
                dest,
                args_start,
                args_len,
                ..
            }
            | Insn::ObjectNew {
                dest,
                args_start,
                args_len,
            } => {
                Register::new(n_regs).check(dest)?;
                module.check_arg_registers(args_start, args_len, n_regs)?;
            }
            Insn::SetFinalizer { obj, closure } => {
                Register::new(n_regs).check_many(&[obj, closure])?
            }
            Insn::ObjectGet {
                dest,
                obj,
                index: _,
            } => Register::new(n_regs).check_many(&[dest, obj])?,
            Insn::ObjectSet { obj, src, index: _ } => {
                Register::new(n_regs).check_many(&[obj, src])?
            }
            Insn::VariantNew {
                dest,
                args_start,
                args_len,
                ..
            } => {
                Register::new(n_regs).check(dest)?;
                module.check_arg_registers(args_start, args_len, n_regs)?;
            }
            Insn::GetField {
                dest,
                rec,
                index: _,
            } => Register::new(n_regs).check_many(&[dest, rec])?,
            Insn::GetTag { dest, src } => Register::new(n_regs).check_many(&[dest, src])?,
            Insn::SetField { dest, rec, src, .. } => {
                Register::new(n_regs).check_many(&[dest, rec, src])?
            }
            Insn::Load { dest, ptr, .. } => Register::new(n_regs).check_many(&[dest, ptr])?,
            Insn::Store { ptr, src, .. } => Register::new(n_regs).check_many(&[ptr, src])?,
            Insn::Copy { from, to, len } => Register::new(n_regs).check_many(&[from, to, len])?,
            Insn::Swap { a, b, .. } => Register::new(n_regs).check_many(&[a, b])?,
            Insn::Io { dest, a, b, c, .. } => Register::new(n_regs).check_many(&[dest, a, b, c])?,
            Insn::Call {
                dest,
                chunk,
                args_start,
                args_len,
            }
            | Insn::MakeClosure {
                dest,
                chunk,
                args_start,
                args_len,
            } => {
                Register::new(n_regs).check(dest)?;
                module.check_chunk(chunk)?;
                module.check_arg_registers(args_start, args_len, n_regs)?;
                if matches!(*self, Insn::Call { .. }) {
                    module.check_call_arity(chunk, args_len)?;
                }
            }
            Insn::CallIndirect {
                dest,
                callee,
                args_start,
                args_len,
            } => {
                Register::new(n_regs).check_many(&[dest, callee])?;
                module.check_arg_registers(args_start, args_len, n_regs)?;
            }
            Insn::Jump { target } => Self::check_target(target)?,
            Insn::Branch {
                cond,
                then_target,
                else_target,
            } => {
                Register::new(n_regs).check(cond)?;
                Self::check_target(then_target)?;
                Self::check_target(else_target)?;
            }
            Insn::Switch {
                tag,
                targets_start,
                targets_len,
            } => {
                Register::new(n_regs).check(tag)?;
                module.check_switch_range(targets_start, targets_len)?;
            }
            Insn::Ret { src } => Register::new(n_regs).check(src)?,
            Insn::Trap { message } => {
                if message as usize >= module.traps.len() {
                    return Err(DecodeError::InvalidIndex("trap message"));
                }
            }
        }
        Ok(())
    }

    fn check_target(target: u32) -> Result<(), DecodeError> {
        let _ = usize::try_from(target).map_err(|_| DecodeError::IntegerOverflow)?;
        Ok(())
    }
}

impl Module {
    fn check_chunk(&self, chunk: u32) -> Result<(), DecodeError> {
        if chunk as usize >= self.chunks.len() {
            return Err(DecodeError::InvalidIndex("chunk"));
        }
        Ok(())
    }

    fn arg_registers(&self, start: u32, len: u16) -> Result<&[u16], DecodeError> {
        let start = usize::try_from(start).map_err(|_| DecodeError::IntegerOverflow)?;
        let end = start
            .checked_add(usize::from(len))
            .ok_or(DecodeError::IntegerOverflow)?;
        self.arg_pool
            .get(start..end)
            .ok_or(DecodeError::InvalidIndex("argument pool"))
    }

    fn check_arg_registers(&self, start: u32, len: u16, n_regs: u16) -> Result<(), DecodeError> {
        Register::new(n_regs).check_many(self.arg_registers(start, len)?)
    }

    fn check_call_arity(&self, chunk: u32, args_len: u16) -> Result<(), DecodeError> {
        let target = &self.chunks[chunk as usize];
        if args_len != target.arity {
            return Err(DecodeError::InvalidIndex("call argument count"));
        }
        if args_len > target.n_regs {
            return Err(DecodeError::InvalidIndex("call frame"));
        }
        Ok(())
    }

    fn check_switch_range(&self, start: u32, len: u16) -> Result<(), DecodeError> {
        let start = usize::try_from(start).map_err(|_| DecodeError::IntegerOverflow)?;
        let end = start
            .checked_add(usize::from(len))
            .ok_or(DecodeError::IntegerOverflow)?;
        if end > self.switch_pool.len() {
            return Err(DecodeError::InvalidIndex("switch pool"));
        }
        Ok(())
    }
}

struct Register {
    n_regs: u16,
}

impl Register {
    fn new(n_regs: u16) -> Self {
        Self { n_regs }
    }

    fn check(&self, reg: u16) -> Result<(), DecodeError> {
        if reg >= self.n_regs {
            return Err(DecodeError::InvalidIndex("register"));
        }
        Ok(())
    }

    fn check_many(&self, regs: &[u16]) -> Result<(), DecodeError> {
        for reg in regs {
            self.check(*reg)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_simple_module() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Const { dest: 0, k: 0 }, Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
            }],
            consts: vec![Value::I64(42)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_bool_to_int_opcode() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::BToI { dest: 1, src: 0 },
                    Insn::Ret { src: 1 },
                ],
                arity: 0,
                n_regs: 2,
            }],
            consts: vec![Value::Bool(true)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_swap_opcode() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Swap {
                        a: 0,
                        b: 1,
                        kind: MemKind::I64,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 2,
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_object_opcodes() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::ObjectNew {
                        dest: 1,
                        args_start: 0,
                        args_len: 1,
                    },
                    Insn::SetFinalizer { obj: 1, closure: 2 },
                    Insn::ObjectGet {
                        dest: 2,
                        obj: 1,
                        index: 0,
                    },
                    Insn::ObjectSet {
                        obj: 1,
                        src: 2,
                        index: 0,
                    },
                    Insn::RegionAcquire { dest: 0, src: 1 },
                    Insn::RegionRelease { dest: 0, src: 1 },
                    Insn::Ret { src: 2 },
                ],
                arity: 0,
                n_regs: 3,
            }],
            consts: vec![Value::I64(7)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };
        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_module_with_pools_and_compound_opcodes() {
        let struct_symbol = Symbol::Struct(ModuleSymbolId::new(ModuleId(0), 1));
        let enum_symbol = Symbol::Enum(ModuleSymbolId::new(ModuleId(0), 2));
        let protocol_symbol = Symbol::Protocol(ModuleSymbolId::new(ModuleId(0), 3));
        let module = Module {
            chunks: vec![
                Chunk {
                    name: "main".into(),
                    code: vec![
                        Insn::Const { dest: 0, k: 0 },
                        Insn::Const { dest: 1, k: 1 },
                        Insn::Const { dest: 2, k: 2 },
                        Insn::RecordNew {
                            dest: 3,
                            symbol: struct_symbol,
                            args_start: 0,
                            args_len: 2,
                        },
                        Insn::VariantNew {
                            dest: 4,
                            symbol: enum_symbol,
                            tag: 7,
                            args_start: 1,
                            args_len: 2,
                        },
                        Insn::ExistentialPack {
                            dest: 5,
                            protocol: protocol_symbol,
                            args_start: 2,
                            args_len: 2,
                        },
                        Insn::TupleNew {
                            dest: 6,
                            args_start: 0,
                            args_len: 3,
                        },
                        Insn::Io {
                            dest: 7,
                            op: IoOp::Poll,
                            a: 0,
                            b: 1,
                            c: 2,
                        },
                        Insn::MakeClosure {
                            dest: 8,
                            chunk: 1,
                            args_start: 0,
                            args_len: 2,
                        },
                        Insn::CallIndirect {
                            dest: 9,
                            callee: 8,
                            args_start: 2,
                            args_len: 1,
                        },
                        Insn::Call {
                            dest: 10,
                            chunk: 1,
                            args_start: 2,
                            args_len: 1,
                        },
                        Insn::Switch {
                            tag: 0,
                            targets_start: 0,
                            targets_len: 3,
                        },
                        Insn::Trap { message: 0 },
                        Insn::Ret { src: 10 },
                    ],
                    arity: 0,
                    n_regs: 11,
                },
                Chunk {
                    name: "callee".into(),
                    code: vec![Insn::EnvGet { dest: 1, index: 0 }, Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 2,
                },
            ],
            consts: vec![
                Value::I64(42),
                Value::Bool(true),
                Value::Ptr(8),
                Value::Byte(3),
                Value::Void,
            ],
            arg_pool: vec![0, 1, 2, 0],
            switch_pool: vec![11, 12, 13],
            traps: vec!["round-trip trap".into()],
            statics: vec![1, 2, 3, 4],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
        assert_eq!(decoded.statics, module.statics);
    }

    #[test]
    fn rejects_bad_magic() {
        let err = Module::decode_bytecode(b"nope").unwrap_err();
        assert_eq!(err, DecodeError::TooShort);
    }

    #[test]
    fn rejects_invalid_constant_index() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Const { dest: 0, k: 99 }],
                arity: 0,
                n_regs: 1,
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let err = Module::decode_bytecode(&encoded).unwrap_err();
        assert_eq!(err, DecodeError::InvalidIndex("constant"));
    }

    #[test]
    fn rejects_arg_pool_register_out_of_range() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::TupleNew {
                        dest: 0,
                        args_start: 0,
                        args_len: 1,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 1,
            }],
            consts: vec![],
            arg_pool: vec![1],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let err = Module::decode_bytecode(&encoded).unwrap_err();
        assert_eq!(err, DecodeError::InvalidIndex("register"));
    }

    #[test]
    fn rejects_direct_call_argument_count_mismatch() {
        let module = Module {
            chunks: vec![
                Chunk {
                    name: "main".into(),
                    code: vec![
                        Insn::Call {
                            dest: 0,
                            chunk: 1,
                            args_start: 0,
                            args_len: 2,
                        },
                        Insn::Ret { src: 0 },
                    ],
                    arity: 0,
                    n_regs: 1,
                },
                Chunk {
                    name: "callee".into(),
                    code: vec![Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 1,
                },
            ],
            consts: vec![],
            arg_pool: vec![0, 0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let err = Module::decode_bytecode(&encoded).unwrap_err();
        assert_eq!(err, DecodeError::InvalidIndex("call argument count"));
    }

    #[test]
    fn rejects_chunk_arity_larger_than_register_file() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![],
                arity: 1,
                n_regs: 0,
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let err = Module::decode_bytecode(&encoded).unwrap_err();
        assert_eq!(err, DecodeError::InvalidIndex("chunk arity"));
    }

    #[test]
    fn indirect_call_argument_mismatch_returns_vm_error() {
        let module = Module {
            chunks: vec![
                Chunk {
                    name: "main".into(),
                    code: vec![
                        Insn::MakeClosure {
                            dest: 0,
                            chunk: 1,
                            args_start: 0,
                            args_len: 0,
                        },
                        Insn::Const { dest: 1, k: 0 },
                        Insn::CallIndirect {
                            dest: 2,
                            callee: 0,
                            args_start: 0,
                            args_len: 2,
                        },
                        Insn::Ret { src: 2 },
                    ],
                    arity: 0,
                    n_regs: 3,
                },
                Chunk {
                    name: "callee".into(),
                    code: vec![Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 1,
                },
            ],
            consts: vec![Value::I64(7)],
            arg_pool: vec![1, 1],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        let mut io = crate::io::StdioIO;
        let err = crate::interp::run(&decoded, &mut io).unwrap_err();
        assert!(err.contains("expected 1 arguments, got 2"));
    }
}
