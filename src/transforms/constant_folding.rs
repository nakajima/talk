use std::collections::HashMap;

use crate::lowering::{
    instr::Instr, ir_function::IRFunction, ir_module::IRModule, register::Register,
};

#[derive(Default)]
pub struct ConstantFolder;

#[derive(Debug, Clone, PartialEq)]
enum ConstValue {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl ConstValue {
    fn add(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Int(a + b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Float(a + b)),
            _ => None,
        }
    }

    fn sub(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Int(a - b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Float(a - b)),
            _ => None,
        }
    }

    fn mul(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Int(a * b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Float(a * b)),
            _ => None,
        }
    }

    fn div(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Int(a / b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Float(a / b)),
            _ => None,
        }
    }

    fn eq(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Bool(a == b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Bool(a == b)),
            (Self::Bool(a), Self::Bool(b)) => Some(Self::Bool(a == b)),
            _ => None,
        }
    }

    fn ne(&self, other: &ConstValue) -> Option<ConstValue> {
        self.eq(other).map(|c| match c {
            Self::Bool(b) => Self::Bool(!b),
            _ => c,
        })
    }

    fn lt(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Bool(a < b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Bool(a < b)),
            _ => None,
        }
    }

    fn lte(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Bool(a <= b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Bool(a <= b)),
            _ => None,
        }
    }

    fn gt(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Bool(a > b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Bool(a > b)),
            _ => None,
        }
    }

    fn gte(&self, other: &ConstValue) -> Option<ConstValue> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Some(Self::Bool(a >= b)),
            (Self::Float(a), Self::Float(b)) => Some(Self::Bool(a >= b)),
            _ => None,
        }
    }
}

impl ConstantFolder {
    pub fn new() -> Self {
        Self
    }

    pub fn run(self, mut module: IRModule) -> IRModule {
        for func in &mut module.functions {
            Self::fold_function(func);
        }
        module
    }

    fn fold_function(func: &mut IRFunction) {
        for block in &mut func.blocks {
            Self::fold_block(block);
        }
    }

    fn fold_block(block: &mut crate::lowering::lowerer::BasicBlock) {
        use Instr::*;
        let mut constants: HashMap<Register, ConstValue> = HashMap::new();
        for instr in &mut block.instructions {
            let current = instr.clone();
            match current {
                ConstantInt(reg, v) => {
                    constants.insert(reg, ConstValue::Int(v));
                }
                ConstantFloat(reg, v) => {
                    constants.insert(reg, ConstValue::Float(v));
                }
                ConstantBool(reg, v) => {
                    constants.insert(reg, ConstValue::Bool(v));
                }
                Add(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.add(&v2) {
                            *instr = match res {
                                ConstValue::Int(i) => ConstantInt(dest, i),
                                ConstValue::Float(f) => ConstantFloat(dest, f),
                                ConstValue::Bool(bv) => ConstantBool(dest, bv),
                            };
                            constants.insert(dest, res);
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                Sub(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.sub(&v2) {
                            *instr = match res {
                                ConstValue::Int(i) => ConstantInt(dest, i),
                                ConstValue::Float(f) => ConstantFloat(dest, f),
                                ConstValue::Bool(bv) => ConstantBool(dest, bv),
                            };
                            constants.insert(dest, res);
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                Mul(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.mul(&v2) {
                            *instr = match res {
                                ConstValue::Int(i) => ConstantInt(dest, i),
                                ConstValue::Float(f) => ConstantFloat(dest, f),
                                ConstValue::Bool(bv) => ConstantBool(dest, bv),
                            };
                            constants.insert(dest, res);
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                Div(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.div(&v2) {
                            *instr = match res {
                                ConstValue::Int(i) => ConstantInt(dest, i),
                                ConstValue::Float(f) => ConstantFloat(dest, f),
                                ConstValue::Bool(bv) => ConstantBool(dest, bv),
                            };
                            constants.insert(dest, res);
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                Eq(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.eq(&v2) {
                            *instr = match res {
                                ConstValue::Bool(bv) => ConstantBool(dest, bv),
                                ConstValue::Int(i) => ConstantInt(dest, i),
                                ConstValue::Float(f) => ConstantFloat(dest, f),
                            };
                            constants.insert(dest, res);
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                Ne(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.ne(&v2) {
                            *instr = match res {
                                ConstValue::Bool(bv) => ConstantBool(dest, bv),
                                ConstValue::Int(i) => ConstantInt(dest, i),
                                ConstValue::Float(f) => ConstantFloat(dest, f),
                            };
                            constants.insert(dest, res);
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                LessThan(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.lt(&v2) {
                            *instr = ConstantBool(dest, matches!(res, ConstValue::Bool(true)));
                            if let ConstValue::Bool(bv) = res {
                                constants.insert(dest, ConstValue::Bool(bv));
                            }
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                LessThanEq(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.lte(&v2) {
                            *instr = ConstantBool(dest, matches!(res, ConstValue::Bool(true)));
                            if let ConstValue::Bool(bv) = res {
                                constants.insert(dest, ConstValue::Bool(bv));
                            }
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                GreaterThan(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.gt(&v2) {
                            *instr = ConstantBool(dest, matches!(res, ConstValue::Bool(true)));
                            if let ConstValue::Bool(bv) = res {
                                constants.insert(dest, ConstValue::Bool(bv));
                            }
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                GreaterThanEq(dest, _ty, a, b) => {
                    if let (Some(v1), Some(v2)) =
                        (constants.get(&a).cloned(), constants.get(&b).cloned())
                    {
                        if let Some(res) = v1.gte(&v2) {
                            *instr = ConstantBool(dest, matches!(res, ConstValue::Bool(true)));
                            if let ConstValue::Bool(bv) = res {
                                constants.insert(dest, ConstValue::Bool(bv));
                            }
                            continue;
                        }
                    }
                    constants.remove(&dest);
                }
                _ => {
                    if let Some(dest) = Self::dest_of(instr) {
                        constants.remove(&dest);
                    }
                }
            }
        }
    }

    fn dest_of(instr: &Instr) -> Option<Register> {
        use Instr::*;
        match instr {
            ConstantInt(r, _) | ConstantFloat(r, _) | ConstantBool(r, _) => Some(*r),
            Add(r, ..)
            | Sub(r, ..)
            | Mul(r, ..)
            | Div(r, ..)
            | StoreLocal(r, ..)
            | LoadLocal(r, ..)
            | Phi(r, ..)
            | Ref(r, ..)
            | Eq(r, ..)
            | Ne(r, ..)
            | LessThan(r, ..)
            | LessThanEq(r, ..)
            | GreaterThan(r, ..)
            | GreaterThanEq(r, ..)
            | GetEnumTag(r, _) => Some(*r),
            Alloc { dest, .. }
            | Const { dest, .. }
            | Load { dest, .. }
            | GetElementPointer { dest, .. }
            | MakeStruct { dest, .. }
            | GetValueOf { dest, .. }
            | Call { dest_reg: dest, .. }
            | GetEnumValue(dest, ..)
            | TagVariant(dest, ..) => Some(*dest),
            _ => None,
        }
    }
}
