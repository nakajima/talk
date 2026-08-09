use crate::CmpOp;
use crate::symbol::{ModuleId, ModuleSymbolId, Symbol};
use crate::{Chunk, Constant, FieldShape, Insn, IoOp, LayoutBody, LayoutDesc, MemKind, Module};

const MAGIC: &[u8; 7] = b"TALKBC\0";
/// The wire-format version, embedded in every image header and recorded
/// in artifact manifests (ADR 0043): a loader refuses any other version.
// Version 6 is the flat-aggregate format (ADR 0045): the module ships
// its layout table, one `AggNew` opcode builds every aggregate under a
// published layout, and field access is offset-addressed. The floor
// matches: earlier versions carried the symbol-headed representation
// this runtime no longer has, so they fail at the gate.
pub const FORMAT_VERSION: u32 = 7;
const MIN_SUPPORTED_FORMAT_VERSION: u32 = 7;

pub fn supports_format(version: u32) -> bool {
    (MIN_SUPPORTED_FORMAT_VERSION..=FORMAT_VERSION).contains(&version)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodeError {
    TooManyItems(&'static str),
    StringTooLong,
}

impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
        self.exports(&module.exports)?;
        self.chunks(&module.chunks)?;
        self.consts(&module.consts)?;
        self.u16_vec("arg_pool", &module.arg_pool)?;
        self.u32_vec("switch_pool", &module.switch_pool)?;
        self.strings("traps", &module.traps)?;
        self.bytes("statics", &module.statics)?;
        self.layouts(&module.layouts)?;
        Ok(())
    }

    fn layouts(&mut self, layouts: &[LayoutDesc]) -> Result<(), EncodeError> {
        self.len("layouts", layouts.len())?;
        for desc in layouts {
            match desc.symbol {
                None => self.u8(0),
                Some(symbol) => {
                    self.u8(1);
                    self.symbol(symbol);
                }
            }
            self.u16(desc.width);
            match &desc.body {
                LayoutBody::Unshaped => self.u8(0),
                LayoutBody::Product(fields) => {
                    self.u8(1);
                    self.layout_fields(fields)?;
                }
                LayoutBody::Sum(variants) => {
                    self.u8(2);
                    self.len("layout variants", variants.len())?;
                    for variant in variants {
                        self.layout_fields(variant)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn layout_fields(&mut self, fields: &[(u16, FieldShape)]) -> Result<(), EncodeError> {
        self.len("layout fields", fields.len())?;
        for &(offset, shape) in fields {
            self.u16(offset);
            match shape {
                FieldShape::Slot => self.u8(0),
                FieldShape::Spliced(child) => {
                    self.u8(1);
                    self.u32(child);
                }
            }
        }
        Ok(())
    }

    fn exports(&mut self, exports: &[(String, u32)]) -> Result<(), EncodeError> {
        self.len("exports", exports.len())?;
        for (name, chunk) in exports {
            self.string(name)?;
            self.u32(*chunk);
        }
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
                self.insn(*insn)?;
            }
            // The unwind table (ADR 0027): (suspension pc, entry pc).
            self.len("unwind", chunk.unwind.len())?;
            for &(suspension, entry) in &chunk.unwind {
                self.u32(suspension);
                self.u32(entry);
            }
        }
        Ok(())
    }

    fn consts(&mut self, consts: &[Constant]) -> Result<(), EncodeError> {
        self.len("consts", consts.len())?;
        for value in consts {
            self.constant(*value);
        }
        Ok(())
    }

    fn constant(&mut self, value: Constant) {
        match value {
            Constant::I64(v) => {
                self.u8(0);
                self.i64(v);
            }
            Constant::F64(v) => {
                self.u8(1);
                self.u64(v.to_bits());
            }
            Constant::Bool(v) => {
                self.u8(2);
                self.u8(u8::from(v));
            }
            Constant::Byte(v) => {
                self.u8(3);
                self.u8(v);
            }
            Constant::Void => self.u8(4),
            Constant::Ptr(v) => {
                self.u8(5);
                self.u32(v);
            }
        }
    }

    fn insn(&mut self, insn: Insn) -> Result<(), EncodeError> {
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
            Insn::IToB { dest, src } => self.reg2(62, dest, src),
            Insn::CellNew { dest, init } => self.reg2(9, dest, init),
            Insn::CellGet { dest, cell } => self.reg2(10, dest, cell),
            Insn::CellSet { cell, src } => self.reg2(11, cell, src),
            Insn::AggNew {
                dest,
                layout,
                tag,
                args_start,
                args_len,
            } => {
                self.u8(12);
                self.u16(dest);
                self.u32(layout);
                self.u16(tag);
                self.u32(args_start);
                self.u16(args_len);
            }
            Insn::Field {
                dest,
                src,
                offset,
                layout,
            } => {
                self.u8(13);
                self.u16(dest);
                self.u16(src);
                self.u16(offset);
                self.u32(layout);
            }
            Insn::FieldIndex { dest, src, index } => {
                self.u8(14);
                self.u16(dest);
                self.u16(src);
                self.u16(index);
            }
            Insn::GetElement {
                dest,
                rec,
                index,
                element,
            } => {
                self.u8(61);
                self.u16(dest);
                self.u16(rec);
                self.u16(index);
                self.u32(element);
            }
            Insn::GetTag { dest, src } => self.reg2(15, dest, src),
            Insn::SetFieldIndex {
                dest,
                rec,
                src,
                index,
            } => {
                self.u8(16);
                self.u16(dest);
                self.u16(rec);
                self.u16(src);
                self.u16(index);
            }
            Insn::ExistentialPack {
                dest,
                args_start,
                args_len,
            } => {
                self.u8(17);
                self.u16(dest);
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
            Insn::SetField {
                dest,
                rec,
                src,
                offset,
                layout,
            } => {
                self.u8(22);
                self.u16(dest);
                self.u16(rec);
                self.u16(src);
                self.u16(offset);
                self.u32(layout);
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
            Insn::UnwindRet => self.u8(50),
            Insn::PushHandler {
                effect,
                clause,
                cont,
            } => {
                self.u8(51);
                self.u32(effect);
                self.u16(clause);
                self.u16(cont);
            }
            Insn::FindHandler {
                clause,
                cont,
                index,
                effect,
            } => {
                self.u8(52);
                self.u32(effect);
                self.u16(clause);
                self.u16(cont);
                self.u16(index);
            }
            Insn::GetFloor { dest } => {
                self.u8(53);
                self.u16(dest);
            }
            Insn::SetFloor { src } => {
                self.u8(54);
                self.u16(src);
            }
            Insn::And { dest, a, b } => self.reg3(55, dest, a, b),
            Insn::Or { dest, a, b } => self.reg3(56, dest, a, b),
            Insn::Xor { dest, a, b } => self.reg3(57, dest, a, b),
            Insn::Shl { dest, a, b } => self.reg3(58, dest, a, b),
            Insn::Shr { dest, a, b } => self.reg3(59, dest, a, b),
            Insn::Not { dest, src } => self.reg2(60, dest, src),
            Insn::Load { dest, ptr, kind } => {
                self.u8(25);
                self.u16(dest);
                self.u16(ptr);
                self.mem_kind(kind);
            }
            Insn::CheckedIndexedLoad {
                dest,
                base,
                index,
                length,
                kind,
                failure_target,
            } => {
                self.u8(63);
                self.u16(dest);
                self.u16(base);
                self.u16(index);
                self.u16(length);
                self.mem_kind(kind);
                self.u32(failure_target);
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
        Ok(())
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
            Symbol::Library => self.local_symbol(2, 0),
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
        if !supports_format(version) {
            return Err(DecodeError::UnsupportedVersion(version));
        }
        let entry = self.u32()?;
        let exports = self.exports()?;
        let chunks = self.chunks()?;
        let consts = self.consts()?;
        let arg_pool = self.u16_vec()?;
        let switch_pool = self.u32_vec()?;
        let traps = self.strings()?;
        let statics = self.byte_vec()?;
        let layouts = self.layouts()?;
        Ok(Module {
            chunks,
            consts,
            arg_pool,
            switch_pool,
            traps,
            statics,
            layouts,
            entry,
            exports,
        })
    }

    fn layouts(&mut self) -> Result<Vec<LayoutDesc>, DecodeError> {
        let len = self.len_of(4)?;
        let mut layouts = Vec::with_capacity(len);
        for _ in 0..len {
            let symbol = match self.u8()? {
                0 => None,
                1 => Some(self.symbol()?),
                tag => return Err(DecodeError::InvalidTag("layout symbol", tag)),
            };
            let width = self.u16()?;
            let body = match self.u8()? {
                0 => LayoutBody::Unshaped,
                1 => LayoutBody::Product(self.layout_fields()?),
                2 => {
                    let variants = self.len_of(4)?;
                    let mut bodies = Vec::with_capacity(variants);
                    for _ in 0..variants {
                        bodies.push(self.layout_fields()?);
                    }
                    LayoutBody::Sum(bodies)
                }
                tag => return Err(DecodeError::InvalidTag("layout body", tag)),
            };
            layouts.push(LayoutDesc {
                symbol,
                width,
                body,
            });
        }
        Ok(layouts)
    }

    fn layout_fields(&mut self) -> Result<Vec<(u16, FieldShape)>, DecodeError> {
        let len = self.len_of(3)?;
        let mut fields = Vec::with_capacity(len);
        for _ in 0..len {
            let offset = self.u16()?;
            let shape = match self.u8()? {
                0 => FieldShape::Slot,
                1 => FieldShape::Spliced(self.u32()?),
                tag => return Err(DecodeError::InvalidTag("layout field", tag)),
            };
            fields.push((offset, shape));
        }
        Ok(fields)
    }

    fn exports(&mut self) -> Result<Vec<(String, u32)>, DecodeError> {
        let len = self.len_of(8)?;
        let mut exports = Vec::with_capacity(len);
        for _ in 0..len {
            let name = self.string()?;
            let chunk = self.u32()?;
            exports.push((name, chunk));
        }
        Ok(exports)
    }

    fn chunks(&mut self) -> Result<Vec<Chunk>, DecodeError> {
        let len = self.len_of(16)?;
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
            let unwind_len = self.len_of(8)?;
            let mut unwind = Vec::with_capacity(unwind_len);
            for _ in 0..unwind_len {
                let suspension = self.u32()?;
                let entry = self.u32()?;
                unwind.push((suspension, entry));
            }
            chunks.push(Chunk {
                name,
                code,
                arity,
                n_regs,
                unwind,
            });
        }
        Ok(chunks)
    }

    fn consts(&mut self) -> Result<Vec<Constant>, DecodeError> {
        let len = self.len()?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.constant()?);
        }
        Ok(values)
    }

    fn constant(&mut self) -> Result<Constant, DecodeError> {
        let tag = self.u8()?;
        match tag {
            0 => Ok(Constant::I64(self.i64()?)),
            1 => Ok(Constant::F64(f64::from_bits(self.u64()?))),
            2 => Ok(Constant::Bool(self.bool()?)),
            3 => Ok(Constant::Byte(self.u8()?)),
            4 => Ok(Constant::Void),
            5 => Ok(Constant::Ptr(self.u32()?)),
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
            12 => Ok(Insn::AggNew {
                dest: self.u16()?,
                layout: self.u32()?,
                tag: self.u16()?,
                args_start: self.u32()?,
                args_len: self.u16()?,
            }),
            13 => Ok(Insn::Field {
                dest: self.u16()?,
                src: self.u16()?,
                offset: self.u16()?,
                layout: self.u32()?,
            }),
            14 => Ok(Insn::FieldIndex {
                dest: self.u16()?,
                src: self.u16()?,
                index: self.u16()?,
            }),
            16 => Ok(Insn::SetFieldIndex {
                dest: self.u16()?,
                rec: self.u16()?,
                src: self.u16()?,
                index: self.u16()?,
            }),

            15 => Ok(Insn::GetTag {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            17 => Ok(Insn::ExistentialPack {
                dest: self.u16()?,
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
            22 => Ok(Insn::SetField {
                dest: self.u16()?,
                rec: self.u16()?,
                src: self.u16()?,
                offset: self.u16()?,
                layout: self.u32()?,
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
            63 => Ok(Insn::CheckedIndexedLoad {
                dest: self.u16()?,
                base: self.u16()?,
                index: self.u16()?,
                length: self.u16()?,
                kind: self.mem_kind()?,
                failure_target: self.u32()?,
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
            50 => Ok(Insn::UnwindRet),
            51 => Ok(Insn::PushHandler {
                effect: self.u32()?,
                clause: self.u16()?,
                cont: self.u16()?,
            }),
            52 => Ok(Insn::FindHandler {
                effect: self.u32()?,
                clause: self.u16()?,
                cont: self.u16()?,
                index: self.u16()?,
            }),
            53 => Ok(Insn::GetFloor { dest: self.u16()? }),
            54 => Ok(Insn::SetFloor { src: self.u16()? }),
            55 => self.reg3(|dest, a, b| Insn::And { dest, a, b }),
            56 => self.reg3(|dest, a, b| Insn::Or { dest, a, b }),
            57 => self.reg3(|dest, a, b| Insn::Xor { dest, a, b }),
            58 => self.reg3(|dest, a, b| Insn::Shl { dest, a, b }),
            59 => self.reg3(|dest, a, b| Insn::Shr { dest, a, b }),
            60 => Ok(Insn::Not {
                dest: self.u16()?,
                src: self.u16()?,
            }),
            61 => Ok(Insn::GetElement {
                dest: self.u16()?,
                rec: self.u16()?,
                index: self.u16()?,
                element: self.u32()?,
            }),
            62 => Ok(Insn::IToB {
                dest: self.u16()?,
                src: self.u16()?,
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
            2 => {
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
        let len = self.len_of(4)?;
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
        let len = self.len_of(2)?;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.u16()?);
        }
        Ok(values)
    }

    fn u32_vec(&mut self) -> Result<Vec<u32>, DecodeError> {
        let len = self.len_of(4)?;
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
        self.len_of(1)
    }

    /// Read a section count and reject it against the bytes actually
    /// present: images are untrusted, and every element of the section
    /// occupies at least `min_element_bytes` of input, so a count whose
    /// encoded size exceeds the remainder is a lie — caught before any
    /// allocation is sized from it, bounding amplification to the
    /// in-memory/encoded ratio of one honest element.
    fn len_of(&mut self, min_element_bytes: usize) -> Result<usize, DecodeError> {
        let len = usize::try_from(self.u32()?).map_err(|_| DecodeError::IntegerOverflow)?;
        let needed = len
            .checked_mul(min_element_bytes)
            .ok_or(DecodeError::IntegerOverflow)?;
        if needed > self.bytes.len() - self.cursor {
            return Err(DecodeError::TooShort);
        }
        Ok(len)
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
        self.validate_layouts()?;
        if self.entry as usize >= self.chunks.len() {
            return Err(DecodeError::InvalidIndex("entry chunk"));
        }
        for (_, chunk) in &self.exports {
            if *chunk as usize >= self.chunks.len() {
                return Err(DecodeError::InvalidIndex("export chunk"));
            }
        }
        for chunk in &self.chunks {
            chunk.validate(self)?;
        }
        Ok(())
    }
}

impl Module {
    /// Layout table sanity (images are untrusted): every spliced child
    /// must exist, be shaped, and land its span inside the parent's
    /// width; every slot field must land in bounds. Zero-width children
    /// may sit exactly at the width (they occupy nothing).
    fn validate_layouts(&self) -> Result<(), DecodeError> {
        // Returns the slots the fields occupy, so the caller can require
        // the declared width to be exactly what the body reaches — a
        // wider width would make every construction allocate padding.
        let check_fields = |width: u16, fields: &[(u16, FieldShape)]| {
            let mut reach: u32 = 0;
            for &(offset, shape) in fields {
                let span = match shape {
                    FieldShape::Slot => 1,
                    FieldShape::Spliced(child) => {
                        let child = self
                            .layouts
                            .get(child as usize)
                            .ok_or(DecodeError::InvalidIndex("layout child"))?;
                        if matches!(child.body, LayoutBody::Unshaped) {
                            return Err(DecodeError::InvalidIndex("layout child"));
                        }
                        u32::from(child.width)
                    }
                };
                if u32::from(offset) + span > u32::from(width) {
                    return Err(DecodeError::InvalidIndex("layout field offset"));
                }
                reach = reach.max(u32::from(offset) + span);
            }
            Ok(reach)
        };
        for desc in &self.layouts {
            match &desc.body {
                LayoutBody::Unshaped => {}
                LayoutBody::Product(fields) => {
                    if check_fields(desc.width, fields)? != u32::from(desc.width) {
                        return Err(DecodeError::InvalidIndex("layout width"));
                    }
                }
                LayoutBody::Sum(variants) => {
                    if desc.width == 0 {
                        return Err(DecodeError::InvalidIndex("layout tag slot"));
                    }
                    // The tag occupies slot 0; the widest variant's
                    // payload must reach the declared width exactly.
                    let mut reach: u32 = 1;
                    for variant in variants {
                        reach = reach.max(check_fields(desc.width, variant)?);
                    }
                    if reach != u32::from(desc.width) {
                        return Err(DecodeError::InvalidIndex("layout width"));
                    }
                }
            }
        }
        Ok(())
    }

    /// A construction or offset read's layout operand: must index the
    /// table and name a shaped entry.
    fn shaped_layout(&self, layout: u32) -> Result<&LayoutDesc, DecodeError> {
        let desc = self
            .layouts
            .get(layout as usize)
            .ok_or(DecodeError::InvalidIndex("layout"))?;
        if matches!(desc.body, LayoutBody::Unshaped) {
            return Err(DecodeError::InvalidIndex("layout"));
        }
        Ok(desc)
    }
}

impl Chunk {
    fn validate(&self, module: &Module) -> Result<(), DecodeError> {
        if self.arity > self.n_regs {
            return Err(DecodeError::InvalidIndex("chunk arity"));
        }
        for insn in &self.code {
            insn.validate(module, self.n_regs, self.code.len())?;
        }
        let mut previous_suspension = None;
        for &(suspension, entry) in &self.unwind {
            let suspension =
                usize::try_from(suspension).map_err(|_| DecodeError::IntegerOverflow)?;
            let entry = usize::try_from(entry).map_err(|_| DecodeError::IntegerOverflow)?;
            if suspension == 0 || suspension > self.code.len() {
                return Err(DecodeError::InvalidIndex("unwind suspension pc"));
            }
            if entry >= self.code.len() {
                return Err(DecodeError::InvalidIndex("unwind entry pc"));
            }
            if previous_suspension.is_some_and(|previous| suspension <= previous) {
                return Err(DecodeError::InvalidIndex("unwind table order"));
            }
            if !matches!(
                self.code[suspension - 1],
                Insn::Call { .. } | Insn::CallIndirect { .. }
            ) {
                return Err(DecodeError::InvalidIndex("unwind suspension instruction"));
            }
            previous_suspension = Some(suspension);
        }
        Ok(())
    }
}

impl Insn {
    fn validate(&self, module: &Module, n_regs: u16, code_len: usize) -> Result<(), DecodeError> {
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
            | Insn::IToB { dest, src }
            | Insn::Not { dest, src }
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
            // UnwindRet touches no registers; its legality is dynamic
            // (only during an abort unwind).
            Insn::UnwindRet => {}
            Insn::PushHandler { clause, cont, .. } => {
                Register::new(n_regs).check_many(&[clause, cont])?;
            }
            Insn::FindHandler {
                clause,
                cont,
                index,
                ..
            } => {
                Register::new(n_regs).check_many(&[clause, cont, index])?;
            }
            Insn::GetFloor { dest } => Register::new(n_regs).check(dest)?,
            Insn::SetFloor { src } => Register::new(n_regs).check(src)?,
            Insn::Add { dest, a, b }
            | Insn::Sub { dest, a, b }
            | Insn::Mul { dest, a, b }
            | Insn::Div { dest, a, b }
            | Insn::And { dest, a, b }
            | Insn::Or { dest, a, b }
            | Insn::Xor { dest, a, b }
            | Insn::Shl { dest, a, b }
            | Insn::Shr { dest, a, b }
            | Insn::Cmp { dest, a, b, .. } => {
                Register::new(n_regs).check(dest)?;
                Register::new(n_regs).check_rk(a, module)?;
                Register::new(n_regs).check_rk(b, module)?;
            }
            Insn::CellSet { cell, src } => Register::new(n_regs).check_many(&[cell, src])?,
            Insn::AggNew {
                dest,
                layout,
                tag,
                args_start,
                args_len,
            } => {
                Register::new(n_regs).check(dest)?;
                module.check_arg_registers(args_start, args_len, n_regs)?;
                let desc = module.shaped_layout(layout)?;
                let fields = match &desc.body {
                    LayoutBody::Product(fields) => {
                        if tag != 0 {
                            return Err(DecodeError::InvalidIndex("construction tag"));
                        }
                        fields
                    }
                    LayoutBody::Sum(variants) => variants
                        .get(usize::from(tag))
                        .ok_or(DecodeError::InvalidIndex("construction tag"))?,
                    LayoutBody::Unshaped => {
                        return Err(DecodeError::InvalidIndex("construction layout"));
                    }
                };
                if fields.len() != usize::from(args_len) {
                    return Err(DecodeError::InvalidIndex("construction arity"));
                }
            }
            Insn::ExistentialPack {
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
            Insn::Field {
                dest, src, layout, ..
            } => {
                Register::new(n_regs).check_many(&[dest, src])?;
                if layout != crate::NO_LAYOUT {
                    module.shaped_layout(layout)?;
                }
            }
            Insn::SetField {
                dest,
                rec,
                src,
                layout,
                ..
            } => {
                Register::new(n_regs).check_many(&[dest, rec, src])?;
                if layout != crate::NO_LAYOUT {
                    module.shaped_layout(layout)?;
                }
            }
            Insn::FieldIndex { dest, src, .. } => {
                Register::new(n_regs).check_many(&[dest, src])?;
            }
            Insn::SetFieldIndex { dest, rec, src, .. } => {
                Register::new(n_regs).check_many(&[dest, rec, src])?;
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
            Insn::GetElement {
                dest,
                rec,
                index,
                element,
            } => {
                Register::new(n_regs).check_many(&[dest, rec, index])?;
                if element != crate::NO_LAYOUT {
                    module.shaped_layout(element)?;
                }
            }
            Insn::GetTag { dest, src } => Register::new(n_regs).check_many(&[dest, src])?,
            Insn::Load { dest, ptr, .. } => Register::new(n_regs).check_many(&[dest, ptr])?,
            Insn::CheckedIndexedLoad {
                dest,
                base,
                index,
                length,
                failure_target,
                ..
            } => {
                Register::new(n_regs).check_many(&[dest, base, index, length])?;
                Self::check_target(failure_target, code_len)?;
            }
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
            Insn::Jump { target } => Self::check_target(target, code_len)?,
            Insn::Branch {
                cond,
                then_target,
                else_target,
            } => {
                Register::new(n_regs).check(cond)?;
                Self::check_target(then_target, code_len)?;
                Self::check_target(else_target, code_len)?;
            }
            Insn::Switch {
                tag,
                targets_start,
                targets_len,
            } => {
                Register::new(n_regs).check(tag)?;
                module.check_switch_range(targets_start, targets_len)?;
                let start = targets_start as usize;
                for target in &module.switch_pool[start..start + targets_len as usize] {
                    Self::check_target(*target, code_len)?;
                }
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

    /// A control-flow target must land inside the chunk it jumps
    /// within: validation happens before execution, not during it.
    fn check_target(target: u32, code_len: usize) -> Result<(), DecodeError> {
        let target = usize::try_from(target).map_err(|_| DecodeError::IntegerOverflow)?;
        if target >= code_len {
            return Err(DecodeError::InvalidIndex("control-flow target"));
        }
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
        let checker = Register::new(n_regs);
        for &field in self.arg_registers(start, len)? {
            checker.check_rk(field, self)?;
        }
        Ok(())
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
        // The interpreter requires at least the default target: an
        // empty switch must not cross the validate-before-execute
        // boundary.
        if len == 0 {
            return Err(DecodeError::InvalidIndex("empty switch"));
        }
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

    /// A register-or-constant operand: the constant half validates
    /// against the module pool instead of the frame width.
    fn check_rk(&self, field: u16, module: &Module) -> Result<(), DecodeError> {
        if field & crate::RK_CONST != 0 {
            if usize::from(field & crate::RK_INDEX) >= module.consts.len() {
                return Err(DecodeError::InvalidIndex("constant operand"));
            }
            return Ok(());
        }
        self.check(field)
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
    fn round_trips_checked_indexed_load() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::CheckedIndexedLoad {
                        dest: 0,
                        base: 1,
                        index: 2,
                        length: 3,
                        kind: MemKind::I64,
                        failure_target: 1,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 4,
                unwind: vec![],
            }],
            ..Module::default()
        };
        let decoded = Module::decode_bytecode(&module.encode_bytecode().unwrap()).unwrap();
        assert_eq!(decoded.chunks[0].code, module.chunks[0].code);
    }

    #[test]
    fn rejects_checked_indexed_load_with_bad_failure_target() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::CheckedIndexedLoad {
                    dest: 0,
                    base: 1,
                    index: 2,
                    length: 3,
                    kind: MemKind::I64,
                    failure_target: 1,
                }],
                arity: 0,
                n_regs: 4,
                unwind: vec![],
            }],
            ..Module::default()
        };
        assert!(Module::decode_bytecode(&module.encode_bytecode().unwrap()).is_err());
    }

    #[test]
    fn rejects_formats_below_the_floor() {
        // Version 4 carried opcodes this decoder no longer knows, so
        // accepting it would load a stale artifact that fails at
        // execution instead of at the gate.
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            ..Module::default()
        };
        let mut encoded = module.encode_bytecode().unwrap();
        encoded[MAGIC.len()..MAGIC.len() + 4]
            .copy_from_slice(&(MIN_SUPPORTED_FORMAT_VERSION - 1).to_le_bytes());
        assert!(Module::decode_bytecode(&encoded).is_err());
    }

    #[test]
    fn round_trips_layouts_and_flat_opcodes() {
        let storage_sym = Symbol::Struct(ModuleSymbolId::new(ModuleId(1), 8));
        let pair_sym = Symbol::Struct(ModuleSymbolId::new(ModuleId(1), 9));
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::AggNew {
                        dest: 1,
                        layout: 1,
                        tag: 0,
                        args_start: 0,
                        args_len: 2,
                    },
                    Insn::Field {
                        dest: 2,
                        src: 1,
                        offset: 0,
                        layout: 0,
                    },
                    Insn::SetField {
                        dest: 1,
                        rec: 1,
                        src: 0,
                        offset: 1,
                        layout: crate::NO_LAYOUT,
                    },
                    Insn::Ret { src: 2 },
                ],
                arity: 0,
                n_regs: 3,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(3)],
            arg_pool: vec![0, 0],
            layouts: vec![
                LayoutDesc {
                    symbol: Some(storage_sym),
                    width: 1,
                    body: LayoutBody::Product(vec![(0, FieldShape::Slot)]),
                },
                LayoutDesc {
                    symbol: Some(pair_sym),
                    width: 2,
                    body: LayoutBody::Product(vec![
                        (0, FieldShape::Spliced(0)),
                        (1, FieldShape::Slot),
                    ]),
                },
                LayoutDesc {
                    symbol: None,
                    width: 1,
                    body: LayoutBody::Unshaped,
                },
                LayoutDesc {
                    symbol: Some(pair_sym),
                    width: 2,
                    body: LayoutBody::Sum(vec![vec![], vec![(1, FieldShape::Slot)]]),
                },
            ],
            ..Module::default()
        };
        let decoded = Module::decode_bytecode(&module.encode_bytecode().unwrap()).unwrap();
        assert_eq!(decoded.layouts, module.layouts);
        assert_eq!(decoded.chunks[0].code, module.chunks[0].code);
    }

    #[test]
    fn rejects_constructions_that_disagree_with_their_layout() {
        let pair_sym = Symbol::Struct(ModuleSymbolId::new(ModuleId(1), 9));
        // Two args into a one-field product: the image lies about the
        // shape and must fail at the gate, not at execution.
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::AggNew {
                        dest: 1,
                        layout: 0,
                        tag: 0,
                        args_start: 0,
                        args_len: 2,
                    },
                    Insn::Ret { src: 1 },
                ],
                arity: 0,
                n_regs: 2,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(3)],
            arg_pool: vec![0, 0],
            layouts: vec![LayoutDesc {
                symbol: Some(pair_sym),
                width: 1,
                body: LayoutBody::Product(vec![(0, FieldShape::Slot)]),
            }],
            ..Module::default()
        };
        assert!(Module::decode_bytecode(&module.encode_bytecode().unwrap()).is_err());
    }

    #[test]
    fn rejects_spliced_children_that_escape_their_parent() {
        let pair_sym = Symbol::Struct(ModuleSymbolId::new(ModuleId(1), 9));
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            layouts: vec![
                LayoutDesc {
                    symbol: Some(pair_sym),
                    width: 2,
                    body: LayoutBody::Product(vec![(0, FieldShape::Slot), (1, FieldShape::Slot)]),
                },
                // A two-slot child spliced at offset 1 of a two-slot
                // parent overruns it.
                LayoutDesc {
                    symbol: Some(pair_sym),
                    width: 2,
                    body: LayoutBody::Product(vec![(1, FieldShape::Spliced(0))]),
                },
            ],
            ..Module::default()
        };
        assert!(Module::decode_bytecode(&module.encode_bytecode().unwrap()).is_err());
    }

    #[test]
    fn rejects_widths_wider_than_their_body() {
        // A declared width the body never reaches would make every
        // construction allocate the padding — the width must be exactly
        // what the fields (plus a sum's tag slot) occupy.
        let pair_sym = Symbol::Struct(ModuleSymbolId::new(ModuleId(1), 9));
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            layouts: vec![LayoutDesc {
                symbol: Some(pair_sym),
                width: 400,
                body: LayoutBody::Product(vec![(0, FieldShape::Slot), (1, FieldShape::Slot)]),
            }],
            ..Module::default()
        };
        assert!(Module::decode_bytecode(&module.encode_bytecode().unwrap()).is_err());
    }

    #[test]
    fn rejects_symbol_tags_outside_the_narrowed_codec() {
        // The wire codec names only what the layout table publishes:
        // struct and enum identities (plus the library fallback). The
        // old 21-tag vocabulary is gone with the representation that
        // needed it — a stray tag is a corrupt image.
        let bytes = [15u8, 0, 0, 0, 0, 0, 0];
        let mut decoder = Decoder {
            bytes: &bytes,
            cursor: 0,
        };
        assert!(matches!(
            decoder.symbol(),
            Err(DecodeError::InvalidTag("symbol", 15))
        ));
    }

    #[test]
    fn rejects_counts_that_violate_element_widths() {
        // A count can fit the one-byte lower bound while still lying
        // about a wider section: eight remaining bytes cannot hold
        // three u32s.
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&3u32.to_le_bytes());
        bytes.extend_from_slice(&[0u8; 8]);
        let mut decoder = Decoder {
            bytes: &bytes,
            cursor: 0,
        };
        assert!(decoder.u32_vec().is_err());
    }

    #[test]
    fn rejects_empty_switches() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Switch {
                        tag: 0,
                        targets_start: 0,
                        targets_len: 0,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(0)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let encoded = module.encode_bytecode().unwrap();
        assert!(Module::decode_bytecode(&encoded).is_err());
    }

    #[test]
    fn rejects_section_counts_larger_than_the_image() {
        // A malformed image may claim a section of billions of entries:
        // the decoder must reject it against the bytes actually present
        // instead of allocating for the claim (images are untrusted).
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Const { dest: 0, k: 0 }, Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(42)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let encoded = module.encode_bytecode().unwrap();
        // Corrupt every u32 in the image to the maximum count in turn:
        // wherever a section length lives, the claim now exceeds the
        // input, and decoding must fail cleanly rather than abort.
        for offset in 0..encoded.len().saturating_sub(4) {
            let mut corrupted = encoded.clone();
            corrupted[offset..offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());
            let _ = Module::decode_bytecode(&corrupted);
        }
        let mut huge_chunks = encoded.clone();
        let counts_at = MAGIC.len() + 4;
        huge_chunks[counts_at..counts_at + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(Module::decode_bytecode(&huge_chunks).is_err());
    }

    #[test]
    fn rejects_control_flow_targets_outside_the_chunk() {
        let jump = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Jump { target: 9 }, Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let encoded = jump.encode_bytecode().unwrap();
        assert!(Module::decode_bytecode(&encoded).is_err(), "jump");

        let switch = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Switch {
                        tag: 0,
                        targets_start: 0,
                        targets_len: 1,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(0)],
            arg_pool: vec![],
            switch_pool: vec![77],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let encoded = switch.encode_bytecode().unwrap();
        assert!(Module::decode_bytecode(&encoded).is_err(), "switch pool");
    }

    #[test]
    fn round_trips_simple_module() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Const { dest: 0, k: 0 }, Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(42)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_unwind_table_and_unwind_ret() {
        // ADR 0027: the chunk's unwind table and the UnwindRet insn
        // survive the encode/decode round trip.
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Call {
                        dest: 0,
                        chunk: 0,
                        args_start: 0,
                        args_len: 0,
                    },
                    Insn::UnwindRet,
                ],
                arity: 0,
                n_regs: 1,
                unwind: vec![(2, 2)],
            }],
            consts: vec![Constant::I64(42)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
        assert_eq!(decoded.chunks[0].unwind, vec![(2, 2)]);
        assert_eq!(decoded.chunks[0].code[2], Insn::UnwindRet);
    }

    #[test]
    fn rejects_invalid_unwind_tables() {
        fn module_with(unwind: Vec<(u32, u32)>) -> Module {
            Module {
                chunks: vec![Chunk {
                    name: "main".into(),
                    code: vec![
                        Insn::Call {
                            dest: 0,
                            chunk: 0,
                            args_start: 0,
                            args_len: 0,
                        },
                        Insn::Call {
                            dest: 0,
                            chunk: 0,
                            args_start: 0,
                            args_len: 0,
                        },
                        Insn::UnwindRet,
                    ],
                    arity: 0,
                    n_regs: 1,
                    unwind,
                }],
                consts: vec![],
                arg_pool: vec![],
                switch_pool: vec![],
                traps: vec![],
                statics: vec![],
                layouts: vec![],
                entry: 0,
                exports: vec![],
            }
        }

        for (unwind, expected) in [
            (
                vec![(0, 2)],
                DecodeError::InvalidIndex("unwind suspension pc"),
            ),
            (
                vec![(4, 2)],
                DecodeError::InvalidIndex("unwind suspension pc"),
            ),
            (vec![(1, 3)], DecodeError::InvalidIndex("unwind entry pc")),
            (
                vec![(1, 2), (1, 2)],
                DecodeError::InvalidIndex("unwind table order"),
            ),
            (
                vec![(2, 2), (1, 2)],
                DecodeError::InvalidIndex("unwind table order"),
            ),
            (
                vec![(3, 2)],
                DecodeError::InvalidIndex("unwind suspension instruction"),
            ),
        ] {
            let encoded = module_with(unwind).encode_bytecode().unwrap();
            assert_eq!(Module::decode_bytecode(&encoded).unwrap_err(), expected);
        }
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
                unwind: vec![],
            }],
            consts: vec![Constant::Bool(true)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_exports_table() {
        let module = Module {
            chunks: vec![Chunk {
                name: "f".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            exports: vec![("lex".into(), 0), ("parse_expr".into(), 0)],
            ..Default::default()
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.exports, module.exports);
    }

    #[test]
    fn rejects_export_with_bad_chunk_index() {
        let module = Module {
            chunks: vec![Chunk {
                name: "f".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            exports: vec![("lex".into(), 7)],
            ..Default::default()
        };

        let encoded = module.encode_bytecode().unwrap();
        assert_eq!(
            Module::decode_bytecode(&encoded).unwrap_err(),
            DecodeError::InvalidIndex("export chunk")
        );
    }

    #[test]
    fn round_trips_int_to_byte_opcode() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::IToB { dest: 1, src: 0 },
                    Insn::Ret { src: 1 },
                ],
                arity: 0,
                n_regs: 2,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(65)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
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
                unwind: vec![],
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
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
                unwind: vec![],
            }],
            consts: vec![Constant::I64(7)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        assert_eq!(decoded.render(), module.render());
    }

    #[test]
    fn round_trips_module_with_pools_and_compound_opcodes() {
        let struct_symbol = Symbol::Struct(ModuleSymbolId::new(ModuleId(0), 1));
        let enum_symbol = Symbol::Enum(ModuleSymbolId::new(ModuleId(0), 2));
        let module = Module {
            chunks: vec![
                Chunk {
                    name: "main".into(),
                    code: vec![
                        Insn::Const { dest: 0, k: 0 },
                        Insn::Const { dest: 1, k: 1 },
                        Insn::Const { dest: 2, k: 2 },
                        Insn::And {
                            dest: 2,
                            a: 0,
                            b: 1,
                        },
                        Insn::Or {
                            dest: 2,
                            a: 0,
                            b: 1,
                        },
                        Insn::Xor {
                            dest: 2,
                            a: 0,
                            b: 1,
                        },
                        Insn::Shl {
                            dest: 2,
                            a: 0,
                            b: 1,
                        },
                        Insn::Shr {
                            dest: 2,
                            a: 0,
                            b: 1,
                        },
                        Insn::Not { dest: 2, src: 0 },
                        Insn::AggNew {
                            dest: 3,
                            layout: 0,
                            tag: 0,
                            args_start: 0,
                            args_len: 2,
                        },
                        Insn::AggNew {
                            dest: 4,
                            layout: 1,
                            tag: 7,
                            args_start: 1,
                            args_len: 2,
                        },
                        Insn::ExistentialPack {
                            dest: 5,
                            args_start: 2,
                            args_len: 2,
                        },
                        Insn::AggNew {
                            dest: 6,
                            layout: 2,
                            tag: 0,
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
                    unwind: vec![],
                },
                Chunk {
                    name: "callee".into(),
                    code: vec![Insn::EnvGet { dest: 1, index: 0 }, Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 2,
                    unwind: vec![],
                },
            ],
            consts: vec![
                Constant::I64(42),
                Constant::Bool(true),
                Constant::Ptr(8),
                Constant::Byte(3),
                Constant::Void,
            ],
            arg_pool: vec![0, 1, 2, 0],
            switch_pool: vec![11, 12, 13],
            traps: vec!["round-trip trap".into()],
            statics: vec![1, 2, 3, 4],
            layouts: vec![
                LayoutDesc {
                    symbol: Some(struct_symbol),
                    width: 2,
                    body: LayoutBody::Product(vec![(0, FieldShape::Slot), (1, FieldShape::Slot)]),
                },
                LayoutDesc {
                    symbol: Some(enum_symbol),
                    width: 3,
                    body: LayoutBody::Sum(vec![
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        vec![(1, FieldShape::Slot), (2, FieldShape::Slot)],
                    ]),
                },
                LayoutDesc {
                    symbol: None,
                    width: 3,
                    body: LayoutBody::Product(vec![
                        (0, FieldShape::Slot),
                        (1, FieldShape::Slot),
                        (2, FieldShape::Slot),
                    ]),
                },
            ],
            entry: 0,
            exports: vec![],
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
                unwind: vec![],
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
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
                    Insn::AggNew {
                        dest: 0,
                        layout: 0,
                        tag: 0,
                        args_start: 0,
                        args_len: 1,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![],
            arg_pool: vec![1],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![LayoutDesc {
                symbol: None,
                width: 1,
                body: LayoutBody::Product(vec![(0, FieldShape::Slot)]),
            }],
            entry: 0,
            exports: vec![],
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
                    unwind: vec![],
                },
                Chunk {
                    name: "callee".into(),
                    code: vec![Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 1,
                    unwind: vec![],
                },
            ],
            consts: vec![],
            arg_pool: vec![0, 0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
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
                unwind: vec![],
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
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
                    unwind: vec![],
                },
                Chunk {
                    name: "callee".into(),
                    code: vec![Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 1,
                    unwind: vec![],
                },
            ],
            consts: vec![Constant::I64(7)],
            arg_pool: vec![1, 1],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };

        let encoded = module.encode_bytecode().unwrap();
        let decoded = Module::decode_bytecode(&encoded).unwrap();
        let mut io = crate::io::StdioIO::default();
        let err = crate::interp::run(&decoded, &mut io).unwrap_err();
        assert!(err.contains("expected 1 arguments, got 2"));
    }
}
