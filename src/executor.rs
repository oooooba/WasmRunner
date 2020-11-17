use std::fmt;
use std::mem;

use crate::frame::*;
use crate::instance::*;
use crate::instr::*;
use crate::module::*;
use crate::types::*;
use crate::value::*;

pub const PAGE_SIZE: usize = 64 * 1024;

#[derive(Debug, PartialEq, Eq)]
pub struct Label {
    arity: usize,
    cont_addr: CodeAddr,
}

impl Label {
    fn new(arity: usize, cont_addr: CodeAddr) -> Self {
        Self { arity, cont_addr }
    }

    fn arity(&self) -> usize {
        self.arity
    }

    fn cont_addr(&self) -> CodeAddr {
        self.cont_addr
    }
}

#[derive(Debug, PartialEq, Eq)]
enum StackEntry {
    Value(Value),
    Label(Label),
    Frame(Frame),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Stack {
    stack: Vec<StackEntry>,
}

impl Stack {
    fn new() -> Self {
        Self { stack: Vec::new() }
    }

    fn assert_stack_is_empty(&self) {
        assert_eq!(self.stack.len(), 0);
    }

    pub fn push_i32(&mut self, n: u32) -> Result<(), ExecutionError> {
        self.push_value(Value::new(ValueKind::I32(n)))
    }

    pub fn pop_i32(&mut self) -> Result<u32, ExecutionError> {
        let v = self.pop_value()?;
        match v.kind() {
            ValueKind::I32(n) => Ok(n),
            _ => Err(ExecutionError::TypeConfusion {
                expected: Valtype::I32,
                actual: v.typ(),
            }),
        }
    }

    pub fn push_i64(&mut self, n: u64) -> Result<(), ExecutionError> {
        self.push_value(Value::new(ValueKind::I64(n)))
    }

    pub fn pop_i64(&mut self) -> Result<u64, ExecutionError> {
        let v = self.pop_value()?;
        match v.kind() {
            ValueKind::I64(n) => Ok(n),
            _ => Err(ExecutionError::TypeConfusion {
                expected: Valtype::I64,
                actual: v.typ(),
            }),
        }
    }

    pub fn push_f32(&mut self, n: F32Bytes) -> Result<(), ExecutionError> {
        self.push_value(Value::new(ValueKind::F32(n)))
    }

    pub fn pop_f32(&mut self) -> Result<F32Bytes, ExecutionError> {
        let v = self.pop_value()?;
        match v.kind() {
            ValueKind::F32(n) => Ok(n),
            _ => Err(ExecutionError::TypeConfusion {
                expected: Valtype::F32,
                actual: v.typ(),
            }),
        }
    }

    pub fn push_f64(&mut self, n: F64Bytes) -> Result<(), ExecutionError> {
        self.push_value(Value::new(ValueKind::F64(n)))
    }

    pub fn pop_f64(&mut self) -> Result<F64Bytes, ExecutionError> {
        let v = self.pop_value()?;
        match v.kind() {
            ValueKind::F64(n) => Ok(n),
            _ => Err(ExecutionError::TypeConfusion {
                expected: Valtype::F64,
                actual: v.typ(),
            }),
        }
    }

    pub fn push_value(&mut self, val: Value) -> Result<(), ExecutionError> {
        self.stack.push(StackEntry::Value(val));
        Ok(())
    }

    pub fn pop_value(&mut self) -> Result<Value, ExecutionError> {
        let e = self.pop_stack_entry()?;
        let s = match e {
            StackEntry::Value(v) => return Ok(v),
            StackEntry::Label(_) => "Label",
            StackEntry::Frame(_) => "Frame",
        };
        Err(ExecutionError::StackEntryConfusion {
            expected: "Value",
            actual: s,
        })
    }

    pub fn push_label(&mut self, label: Label) -> Result<(), ExecutionError> {
        self.stack.push(StackEntry::Label(label));
        Ok(())
    }

    pub fn pop_label(&mut self) -> Result<Label, ExecutionError> {
        let e = self.pop_stack_entry()?;
        let s = match e {
            StackEntry::Value(_) => "Value",
            StackEntry::Label(l) => return Ok(l),
            StackEntry::Frame(_) => "Frame",
        };
        Err(ExecutionError::StackEntryConfusion {
            expected: "Label",
            actual: s,
        })
    }

    pub fn push_frame(&mut self, frame: Frame) -> Result<(), ExecutionError> {
        self.stack.push(StackEntry::Frame(frame));
        Ok(())
    }

    pub fn pop_frame(&mut self) -> Result<Frame, ExecutionError> {
        let e = self.pop_stack_entry()?;
        let s = match e {
            StackEntry::Value(_) => "Value",
            StackEntry::Label(_) => "Label",
            StackEntry::Frame(f) => return Ok(f),
        };
        Err(ExecutionError::StackEntryConfusion {
            expected: "Frame",
            actual: s,
        })
    }

    fn peek_stack_entry(&self) -> Result<&StackEntry, ExecutionError> {
        self.stack
            .last()
            .ok_or(ExecutionError::StackOperationFailure(
                "cannot peek from empty stack",
            ))
    }

    fn pop_stack_entry(&mut self) -> Result<StackEntry, ExecutionError> {
        self.stack
            .pop()
            .ok_or(ExecutionError::StackOperationFailure(
                "cannot pop empty stack",
            ))
    }
}

pub struct Context {
    store: Store,
    stack: Stack,
    current_frame: Frame,
    dummy_frame: Frame,
    code_addr: CodeAddr,
}

impl Context {
    pub fn new() -> Self {
        let dummy_frame = Frame::new(Vec::new(), 0, None, None, usize::MAX);
        Self {
            store: Store::new(),
            stack: Stack::new(),
            current_frame: dummy_frame.make_clone(),
            dummy_frame,
            code_addr: 0,
        }
    }

    pub fn reset(&mut self) {
        self.stack = Stack::new();
        self.current_frame = self.dummy_frame.make_clone();
    }

    pub fn stack(&self) -> &Stack {
        &self.stack
    }

    pub fn stack_mut(&mut self) -> &mut Stack {
        &mut self.stack
    }

    pub fn current_frame(&self) -> &Frame {
        &self.current_frame
    }

    pub fn current_frame_mut(&mut self) -> &mut Frame {
        &mut self.current_frame
    }

    pub fn update_frame(&mut self, frame: Frame) {
        self.current_frame = frame;
    }

    pub fn code_addr(&self) -> CodeAddr {
        self.code_addr
    }

    pub fn update_code_addr(&mut self, code_addr: CodeAddr) {
        self.code_addr = code_addr
    }

    pub fn increment_code_addr(&mut self) {
        self.code_addr += 1;
    }

    pub fn find_funcaddr(&self, name: &Name) -> Option<Funcaddr> {
        let addr = self.store.resolve(None, name);
        if let Some(Extarnval::Func(funcaddr)) = addr {
            Some(*funcaddr)
        } else {
            None
        }
    }

    pub fn load_global(&self, module_name: Option<&Name>, content_name: &Name) -> Option<Value> {
        let addr = self.store.resolve(module_name, content_name);
        let globaladdr = if let Some(Extarnval::Global(globaladdr)) = addr {
            globaladdr
        } else {
            return None;
        };
        let globalinst = &self.store.globals()[globaladdr.to_usize()];
        Some(globalinst.value())
    }

    pub fn register_content(
        &mut self,
        module_name: Option<Name>,
        content_name: Name,
        content: Extarnval,
    ) -> Option<Extarnval> {
        self.store
            .register_content(module_name, content_name, content)
    }

    pub fn register_hostfunc(
        &mut self,
        functype: Functype,
        hostfunc: Hostfunc,
    ) -> Result<Funcaddr, ExecutionError> {
        self.store.allochostfunc(functype, hostfunc)
    }

    pub fn register_global(
        &mut self,
        globaltype: &Globaltype,
        val: Value,
    ) -> Result<Globaladdr, ExecutionError> {
        self.store.allocglobal(globaltype, val)
    }

    pub fn register_table(&mut self, tabletype: &Tabletype) -> Result<Tableaddr, ExecutionError> {
        self.store.alloctable(tabletype)
    }

    pub fn register_mem(&mut self, memtype: &Memtype) -> Result<Memaddr, ExecutionError> {
        self.store.allocmem(memtype)
    }
}

fn execute_instr(
    instr: &Instr,
    stack: &mut Stack,
    frame: &mut Frame,
    store: &mut Store,
) -> Result<(), ExecutionError> {
    use InstrKind::*;
    match &instr.kind {
        ConstI32(c) => stack.push_i32(*c),
        ConstI64(c) => stack.push_i64(*c),
        ConstF32(c) => stack.push_f32(*c),
        ConstF64(c) => stack.push_f64(*c),

        UnopI32(op) => {
            let c = stack.pop_i32()?;
            let v = match op {
                IUnopKind::Clz => c.leading_zeros(),
                IUnopKind::Ctz => c.trailing_zeros(),
                IUnopKind::Popcnt => c.count_ones(),
            };
            stack.push_i32(v)
        }
        UnopI64(op) => {
            let c = stack.pop_i64()?;
            let v = match op {
                IUnopKind::Clz => c.leading_zeros() as u64,
                IUnopKind::Ctz => c.trailing_zeros() as u64,
                IUnopKind::Popcnt => c.count_ones() as u64,
            };
            stack.push_i64(v)
        }
        UnopF32(op) => {
            let c = stack.pop_f32()?;
            let v = match op {
                FUnopKind::Abs => c.to_absolute_value().to_f32(),
                FUnopKind::Neg => c.to_negated_value().to_f32(),
                FUnopKind::Ceil => c.to_f32().ceil(),
                FUnopKind::Floor => c.to_f32().floor(),
                FUnopKind::Trunc => c.to_f32().trunc(),
                FUnopKind::Nearest => {
                    let f = c.to_f32();
                    if 0.0 < f && f <= 0.5 {
                        0.0
                    } else if -0.5 <= f && f < 0.0 {
                        -0.0
                    } else {
                        let n = f.round();
                        if (f - n).abs() == 0.5 && n.rem_euclid(2.0) == 1.0 {
                            if n > 0.0 {
                                n - 1.0
                            } else {
                                n + 1.0
                            }
                        } else {
                            n
                        }
                    }
                }
                FUnopKind::Sqrt => c.to_f32().sqrt(),
            };
            let v = F32Bytes::new(v);
            stack.push_f32(v)
        }
        UnopF64(op) => {
            let c = stack.pop_f64()?;
            let v = match op {
                FUnopKind::Abs => c.to_absolute_value().to_f64(),
                FUnopKind::Neg => c.to_negated_value().to_f64(),
                FUnopKind::Ceil => c.to_f64().ceil(),
                FUnopKind::Floor => c.to_f64().floor(),
                FUnopKind::Trunc => c.to_f64().trunc(),
                FUnopKind::Nearest => {
                    let f = c.to_f64();
                    if 0.0 < f && f <= 0.5 {
                        0.0
                    } else if -0.5 <= f && f < 0.0 {
                        -0.0
                    } else {
                        let n = f.round();
                        if (f - n).abs() == 0.5 && n.rem_euclid(2.0) == 1.0 {
                            if n > 0.0 {
                                n - 1.0
                            } else {
                                n + 1.0
                            }
                        } else {
                            n
                        }
                    }
                }
                FUnopKind::Sqrt => c.to_f64().sqrt(),
            };
            let v = F64Bytes::new(v);
            stack.push_f64(v)
        }

        Extend(kind) => {
            let value_kind = match kind {
                ExtendKind::I32As8S => ValueKind::I32(stack.pop_i32()? as i8 as u32),
                ExtendKind::I32As16S => ValueKind::I32(stack.pop_i32()? as i16 as u32),
                ExtendKind::I64As8S => ValueKind::I64(stack.pop_i64()? as i8 as u64),
                ExtendKind::I64As16S => ValueKind::I64(stack.pop_i64()? as i16 as u64),
                ExtendKind::I64As32S => ValueKind::I64(stack.pop_i64()? as i32 as u64),
            };
            stack.push_value(Value::new(value_kind))
        }

        BinopI32(op) => {
            let c2 = stack.pop_i32()?;
            let c1 = stack.pop_i32()?;
            let v = match op {
                IBinopKind::Add => c1.wrapping_add(c2),
                IBinopKind::Sub => c1.wrapping_sub(c2),
                IBinopKind::Mul => c1.wrapping_mul(c2),
                IBinopKind::DivS => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    let c1 = c1 as i32;
                    let c2 = c2 as i32;
                    let (result, overflows) = c1.overflowing_div(c2);
                    if overflows {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    result as u32
                }
                IBinopKind::DivU => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    c1 / c2
                }
                IBinopKind::RemS => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    let c1 = c1 as i32;
                    let c2 = c2 as i32;
                    let (result, _) = c1.overflowing_rem(c2);
                    result as u32
                }
                IBinopKind::RemU => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    c1 % c2
                }
                IBinopKind::And => c1 & c2,
                IBinopKind::Or => c1 | c2,
                IBinopKind::Xor => c1 ^ c2,
                IBinopKind::Shl => c1 << (c2 % 32),
                IBinopKind::ShrS => ((c1 as i32) >> (c2 % 32)) as u32,
                IBinopKind::ShrU => c1 >> (c2 % 32),
                IBinopKind::Rotl => c1.rotate_left(c2 % 32),
                IBinopKind::Rotr => c1.rotate_right(c2 % 32),
            };
            stack.push_i32(v)
        }
        BinopI64(op) => {
            let c2 = stack.pop_i64()?;
            let c1 = stack.pop_i64()?;
            let v = match op {
                IBinopKind::Add => c1.wrapping_add(c2),
                IBinopKind::Sub => c1.wrapping_sub(c2),
                IBinopKind::Mul => c1.wrapping_mul(c2),
                IBinopKind::DivS => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    let c1 = c1 as i64;
                    let c2 = c2 as i64;
                    let (result, overflows) = c1.overflowing_div(c2);
                    if overflows {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    result as u64
                }
                IBinopKind::DivU => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    c1 / c2
                }
                IBinopKind::RemS => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    let c1 = c1 as i64;
                    let c2 = c2 as i64;
                    let (result, _) = c1.overflowing_rem(c2);
                    result as u64
                }
                IBinopKind::RemU => {
                    if c2 == 0 {
                        return Err(ExecutionError::ZeroDivision);
                    }
                    c1 % c2
                }
                IBinopKind::And => c1 & c2,
                IBinopKind::Or => c1 | c2,
                IBinopKind::Xor => c1 ^ c2,
                IBinopKind::Shl => c1 << (c2 % 64),
                IBinopKind::ShrS => ((c1 as i64) >> (c2 % 64)) as u64,
                IBinopKind::ShrU => c1 >> (c2 % 64),
                IBinopKind::Rotl => c1.rotate_left((c2 % 64) as u32),
                IBinopKind::Rotr => c1.rotate_right((c2 % 64) as u32),
            };
            stack.push_i64(v)
        }
        BinopF32(op) => {
            let c2 = stack.pop_f32()?;
            let c1 = stack.pop_f32()?;
            let v = match op {
                FBinopKind::Add => c1.to_f32() + c2.to_f32(),
                FBinopKind::Sub => c1.to_f32() - c2.to_f32(),
                FBinopKind::Mul => c1.to_f32() * c2.to_f32(),
                FBinopKind::Div => c1.to_f32() / c2.to_f32(),
                FBinopKind::Min => {
                    if c1.is_nan() || c2.is_nan() {
                        f32::NAN
                    } else if (c1.is_positive_zero() && c2.is_negative_zero())
                        || (c1.is_negative_zero() && c2.is_positive_zero())
                    {
                        -0.0
                    } else {
                        c1.to_f32().min(c2.to_f32())
                    }
                }
                FBinopKind::Max => {
                    if c1.is_nan() || c2.is_nan() {
                        f32::NAN
                    } else if (c1.is_positive_zero() && c2.is_negative_zero())
                        || (c1.is_negative_zero() && c2.is_positive_zero())
                    {
                        0.0
                    } else {
                        c1.to_f32().max(c2.to_f32())
                    }
                }
                FBinopKind::Copysign => {
                    if (c1.is_positive() && c2.is_positive())
                        || (c1.is_negative() && c2.is_negative())
                    {
                        c1.to_f32()
                    } else {
                        c1.to_negated_value().to_f32()
                    }
                }
            };
            let v = F32Bytes::new(v);
            stack.push_f32(v)
        }
        BinopF64(op) => {
            let c2 = stack.pop_f64()?;
            let c1 = stack.pop_f64()?;
            let v = match op {
                FBinopKind::Add => c1.to_f64() + c2.to_f64(),
                FBinopKind::Sub => c1.to_f64() - c2.to_f64(),
                FBinopKind::Mul => c1.to_f64() * c2.to_f64(),
                FBinopKind::Div => c1.to_f64() / c2.to_f64(),
                FBinopKind::Min => {
                    if c1.is_nan() || c2.is_nan() {
                        f64::NAN
                    } else if (c1.is_positive_zero() && c2.is_negative_zero())
                        || (c1.is_negative_zero() && c2.is_positive_zero())
                    {
                        -0.0
                    } else {
                        c1.to_f64().min(c2.to_f64())
                    }
                }
                FBinopKind::Max => {
                    if c1.is_nan() || c2.is_nan() {
                        f64::NAN
                    } else if (c1.is_positive_zero() && c2.is_negative_zero())
                        || (c1.is_negative_zero() && c2.is_positive_zero())
                    {
                        0.0
                    } else {
                        c1.to_f64().max(c2.to_f64())
                    }
                }
                FBinopKind::Copysign => {
                    if (c1.is_positive() && c2.is_positive())
                        || (c1.is_negative() && c2.is_negative())
                    {
                        c1.to_f64()
                    } else {
                        c1.to_negated_value().to_f64()
                    }
                }
            };
            let v = F64Bytes::new(v);
            stack.push_f64(v)
        }

        TestopI32(op) => {
            let c = stack.pop_i32()?;
            let v = match op {
                TestopKind::Eqz if c == 0 => 1,
                TestopKind::Eqz => 0,
            };
            stack.push_i32(v)
        }
        TestopI64(op) => {
            let c = stack.pop_i64()?;
            let v = match op {
                TestopKind::Eqz if c == 0 => 1,
                TestopKind::Eqz => 0,
            };
            stack.push_i32(v)
        }

        RelopI32(op) => {
            let c2 = stack.pop_i32()?;
            let c1 = stack.pop_i32()?;
            let v = match op {
                IRelopKind::Eq if c1 == c2 => 1,
                IRelopKind::Ne if c1 != c2 => 1,
                IRelopKind::LtS if (c1 as i32) < (c2 as i32) => 1,
                IRelopKind::LtU if c1 < c2 => 1,
                IRelopKind::GtS if (c1 as i32) > (c2 as i32) => 1,
                IRelopKind::GtU if c1 > c2 => 1,
                IRelopKind::LeS if (c1 as i32) <= (c2 as i32) => 1,
                IRelopKind::LeU if c1 <= c2 => 1,
                IRelopKind::GeS if (c1 as i32) >= (c2 as i32) => 1,
                IRelopKind::GeU if c1 >= c2 => 1,
                _ => 0,
            };
            stack.push_i32(v)
        }
        RelopI64(op) => {
            let c2 = stack.pop_i64()?;
            let c1 = stack.pop_i64()?;
            let v = match op {
                IRelopKind::Eq if c1 == c2 => 1,
                IRelopKind::Ne if c1 != c2 => 1,
                IRelopKind::LtS if (c1 as i64) < (c2 as i64) => 1,
                IRelopKind::LtU if c1 < c2 => 1,
                IRelopKind::GtS if (c1 as i64) > (c2 as i64) => 1,
                IRelopKind::GtU if c1 > c2 => 1,
                IRelopKind::LeS if (c1 as i64) <= (c2 as i64) => 1,
                IRelopKind::LeU if c1 <= c2 => 1,
                IRelopKind::GeS if (c1 as i64) >= (c2 as i64) => 1,
                IRelopKind::GeU if c1 >= c2 => 1,
                _ => 0,
            };
            stack.push_i32(v)
        }
        RelopF32(op) => {
            let c2 = stack.pop_f32()?;
            let c1 = stack.pop_f32()?;
            let v = match op {
                FRelopKind::Eq if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Eq if c1.is_positive_zero() && c2.is_negative_zero() => 1,
                FRelopKind::Eq if c1.is_negative_zero() && c2.is_positive_zero() => 1,
                FRelopKind::Eq if c1 == c2 => 1,
                FRelopKind::Ne if c1.is_nan() || c2.is_nan() => 1,
                FRelopKind::Ne if c1.is_positive_zero() && c2.is_negative_zero() => 0,
                FRelopKind::Ne if c1.is_negative_zero() && c2.is_positive_zero() => 0,
                FRelopKind::Ne if c1 != c2 => 1,
                FRelopKind::Lt if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Lt if c1.to_f32() < c2.to_f32() => 1,
                FRelopKind::Gt if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Gt if c1.to_f32() > c2.to_f32() => 1,
                FRelopKind::Le if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Le if c1.is_positive_zero() && c2.is_negative_zero() => 1,
                FRelopKind::Le if c1.is_negative_zero() && c2.is_positive_zero() => 1,
                FRelopKind::Le if c1.to_f32() <= c2.to_f32() => 1,
                FRelopKind::Ge if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Ge if c1.is_positive_zero() && c2.is_negative_zero() => 1,
                FRelopKind::Ge if c1.is_negative_zero() && c2.is_positive_zero() => 1,
                FRelopKind::Ge if c1.to_f32() >= c2.to_f32() => 1,
                _ => 0,
            };
            stack.push_i32(v)
        }
        RelopF64(op) => {
            let c2 = stack.pop_f64()?;
            let c1 = stack.pop_f64()?;
            let v = match op {
                FRelopKind::Eq if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Eq if c1.is_positive_zero() && c2.is_negative_zero() => 1,
                FRelopKind::Eq if c1.is_negative_zero() && c2.is_positive_zero() => 1,
                FRelopKind::Eq if c1 == c2 => 1,
                FRelopKind::Ne if c1.is_nan() || c2.is_nan() => 1,
                FRelopKind::Ne if c1.is_positive_zero() && c2.is_negative_zero() => 0,
                FRelopKind::Ne if c1.is_negative_zero() && c2.is_positive_zero() => 0,
                FRelopKind::Ne if c1 != c2 => 1,
                FRelopKind::Lt if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Lt if c1.to_f64() < c2.to_f64() => 1,
                FRelopKind::Gt if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Gt if c1.to_f64() > c2.to_f64() => 1,
                FRelopKind::Le if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Le if c1.is_positive_zero() && c2.is_negative_zero() => 1,
                FRelopKind::Le if c1.is_negative_zero() && c2.is_positive_zero() => 1,
                FRelopKind::Le if c1.to_f64() <= c2.to_f64() => 1,
                FRelopKind::Ge if c1.is_nan() || c2.is_nan() => 0,
                FRelopKind::Ge if c1.is_positive_zero() && c2.is_negative_zero() => 1,
                FRelopKind::Ge if c1.is_negative_zero() && c2.is_positive_zero() => 1,
                FRelopKind::Ge if c1.to_f64() >= c2.to_f64() => 1,
                _ => 0,
            };
            stack.push_i32(v)
        }

        Cvtop(op) => {
            let value_kind = match op {
                CvtopKind::I32WrapI64 => ValueKind::I32(stack.pop_i64()? as u32),
                CvtopKind::I64ExtendI32S => ValueKind::I64(stack.pop_i32()? as i32 as i64 as u64),
                CvtopKind::I64ExtendI32U => ValueKind::I64(stack.pop_i32()? as u64),
                CvtopKind::I32TruncF32S => {
                    let v = stack.pop_f32()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f32() as i64;
                    if !(i32::MIN as i64 <= v && v <= i32::MAX as i64) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I32(v as i32 as u32)
                }
                CvtopKind::I32TruncF32U => {
                    let v = stack.pop_f32()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f32() as i64;
                    if !(0 <= v && v <= u32::MAX as i64) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I32(v as u32)
                }
                CvtopKind::I32TruncF64S => {
                    let v = stack.pop_f64()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f64() as i64;
                    if !(i32::MIN as i64 <= v && v <= i32::MAX as i64) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I32(v as i32 as u32)
                }
                CvtopKind::I32TruncF64U => {
                    let v = stack.pop_f64()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f64() as i64;
                    if !(0 <= v && v <= u32::MAX as i64) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I32(v as u32)
                }
                CvtopKind::I64TruncF32S => {
                    let v = stack.pop_f32()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f32() as i128;
                    if !(i64::MIN as i128 <= v && v <= i64::MAX as i128) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I64(v as i64 as u64)
                }
                CvtopKind::I64TruncF32U => {
                    let v = stack.pop_f32()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f32() as i128;
                    if !(0 <= v && v <= u64::MAX as i128) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I64(v as u64)
                }
                CvtopKind::I64TruncF64S => {
                    let v = stack.pop_f64()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f64() as i128;
                    if !(i64::MIN as i128 <= v && v <= i64::MAX as i128) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I64(v as i64 as u64)
                }
                CvtopKind::I64TruncF64U => {
                    let v = stack.pop_f64()?;
                    if v.is_infinite() {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    if v.is_nan() {
                        return Err(ExecutionError::InvalidConversionToInteger);
                    }
                    let v = v.to_f64() as i128;
                    if !(0 <= v && v <= u64::MAX as i128) {
                        return Err(ExecutionError::IntegerOverflow);
                    }
                    ValueKind::I64(v as u64)
                }
                CvtopKind::I32TruncSatF32S => {
                    let v = stack.pop_f32()?.to_f32();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            i32::MIN
                        } else {
                            i32::MAX
                        }
                    } else if (v as i64) < (i32::MIN as i64) {
                        i32::MIN
                    } else if (v as i64) > (i32::MAX as i64) {
                        i32::MAX
                    } else {
                        v as i32
                    };
                    ValueKind::I32(v as u32)
                }
                CvtopKind::I32TruncSatF32U => {
                    let v = stack.pop_f32()?.to_f32();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            u32::MIN
                        } else {
                            u32::MAX
                        }
                    } else if (v as i64) < (u32::MIN as i64) {
                        u32::MIN
                    } else if (v as i64) > (u32::MAX as i64) {
                        u32::MAX
                    } else {
                        v as u32
                    };
                    ValueKind::I32(v)
                }
                CvtopKind::I32TruncSatF64S => {
                    let v = stack.pop_f64()?.to_f64();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            i32::MIN
                        } else {
                            i32::MAX
                        }
                    } else if (v as i64) < (i32::MIN as i64) {
                        i32::MIN
                    } else if (v as i64) > (i32::MAX as i64) {
                        i32::MAX
                    } else {
                        v as i32
                    };
                    ValueKind::I32(v as u32)
                }
                CvtopKind::I32TruncSatF64U => {
                    let v = stack.pop_f64()?.to_f64();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            u32::MIN
                        } else {
                            u32::MAX
                        }
                    } else if (v as i64) < (u32::MIN as i64) {
                        u32::MIN
                    } else if (v as i64) > (u32::MAX as i64) {
                        u32::MAX
                    } else {
                        v as u32
                    };
                    ValueKind::I32(v)
                }
                CvtopKind::I64TruncSatF32S => {
                    let v = stack.pop_f32()?.to_f32();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            i64::MIN
                        } else {
                            i64::MAX
                        }
                    } else if (v as i128) < (i64::MIN as i128) {
                        i64::MIN
                    } else if (v as i128) > (i64::MAX as i128) {
                        i64::MAX
                    } else {
                        v as i64
                    };
                    ValueKind::I64(v as u64)
                }
                CvtopKind::I64TruncSatF32U => {
                    let v = stack.pop_f32()?.to_f32();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            u64::MIN
                        } else {
                            u64::MAX
                        }
                    } else if (v as i128) < (u64::MIN as i128) {
                        u64::MIN
                    } else if (v as i128) > (u64::MAX as i128) {
                        u64::MAX
                    } else {
                        v as u64
                    };
                    ValueKind::I64(v)
                }
                CvtopKind::I64TruncSatF64S => {
                    let v = stack.pop_f64()?.to_f64();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            i64::MIN
                        } else {
                            i64::MAX
                        }
                    } else if (v as i128) < (i64::MIN as i128) {
                        i64::MIN
                    } else if (v as i128) > (i64::MAX as i128) {
                        i64::MAX
                    } else {
                        v as i64
                    };
                    ValueKind::I64(v as u64)
                }
                CvtopKind::I64TruncSatF64U => {
                    let v = stack.pop_f64()?.to_f64();
                    let v = if v.is_nan() {
                        0
                    } else if v.is_infinite() {
                        if v.is_sign_negative() {
                            u64::MIN
                        } else {
                            u64::MAX
                        }
                    } else if (v as i128) < (u64::MIN as i128) {
                        u64::MIN
                    } else if (v as i128) > (u64::MAX as i128) {
                        u64::MAX
                    } else {
                        v as u64
                    };
                    ValueKind::I64(v)
                }
                CvtopKind::F32ConvertI32S => {
                    ValueKind::F32(F32Bytes::new(stack.pop_i32()? as i32 as f32))
                }
                CvtopKind::F32ConvertI32U => ValueKind::F32(F32Bytes::new(stack.pop_i32()? as f32)),
                CvtopKind::F32ConvertI64S => {
                    ValueKind::F32(F32Bytes::new(stack.pop_i64()? as i64 as f32))
                }
                CvtopKind::F32ConvertI64U => ValueKind::F32(F32Bytes::new(stack.pop_i64()? as f32)),
                CvtopKind::F64ConvertI32S => {
                    ValueKind::F64(F64Bytes::new(stack.pop_i32()? as i32 as f64))
                }
                CvtopKind::F64ConvertI32U => ValueKind::F64(F64Bytes::new(stack.pop_i32()? as f64)),
                CvtopKind::F64ConvertI64S => {
                    ValueKind::F64(F64Bytes::new(stack.pop_i64()? as i64 as f64))
                }
                CvtopKind::F64ConvertI64U => ValueKind::F64(F64Bytes::new(stack.pop_i64()? as f64)),
                CvtopKind::F32DemoteF64 => {
                    let v = stack.pop_f64()?;
                    let v = if v.is_nan() {
                        f32::NAN
                    } else {
                        v.to_f64() as f32
                    };
                    ValueKind::F32(F32Bytes::new(v))
                }
                CvtopKind::F64PromoteF32 => {
                    let v = stack.pop_f32()?;
                    let v = if v.is_nan() {
                        f64::NAN
                    } else {
                        v.to_f32() as f64
                    };
                    ValueKind::F64(F64Bytes::new(v))
                }
                CvtopKind::I32ReinterpretF32 => {
                    ValueKind::I32(u32::from_le_bytes(stack.pop_f32()?.to_bytes()))
                }
                CvtopKind::I64ReinterpretF64 => {
                    ValueKind::I64(u64::from_le_bytes(stack.pop_f64()?.to_bytes()))
                }
                CvtopKind::F32ReinterpretI32 => {
                    ValueKind::F32(F32Bytes::from_bytes(stack.pop_i32()?.to_le_bytes()))
                }
                CvtopKind::F64ReinterpretI64 => {
                    ValueKind::F64(F64Bytes::from_bytes(stack.pop_i64()?.to_le_bytes()))
                }
            };
            stack.push_value(Value::new(value_kind))
        }

        Drop => stack.pop_value().map(|_| ()),
        Select => {
            let c = stack.pop_i32()?;
            let val2 = stack.pop_value()?;
            let val1 = stack.pop_value()?;
            let val = if c != 0 { val1 } else { val2 };
            stack.push_value(val)
        }

        GetLocal(idx) => {
            let v = frame.get(*idx)?;
            stack.push_value(v)
        }
        SetLocal(idx) => {
            let v = stack.pop_value()?;
            frame.set(*idx, v)
        }
        TeeLocal(idx) => {
            let v = stack.pop_value()?;
            stack.push_value(v)?;
            frame.set(*idx, v)
        }
        GetGlobal(idx) => {
            let globaladdr = frame.resolve_globaladdr(*idx)?;
            let globalinst = &store.globals()[globaladdr.to_usize()];
            let v = globalinst.value();
            stack.push_value(v)
        }
        SetGlobal(idx) => {
            let v = stack.pop_value()?;
            let globaladdr = frame.resolve_globaladdr(*idx)?;
            let globalinst = &mut store.globals_mut()[globaladdr.to_usize()];
            globalinst.update_value(v);
            Ok(())
        }

        LoadI32(opt, memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &store.mems()[memaddr.to_usize()];
            let v = match opt {
                None => meminst.read_i32(ea)?,
                Some(LoadI32Opt::S8) => meminst.read_i8(ea)? as i8 as i32 as u32,
                Some(LoadI32Opt::U8) => meminst.read_i8(ea)? as u32,
                Some(LoadI32Opt::S16) => meminst.read_i16(ea)? as i16 as i32 as u32,
                Some(LoadI32Opt::U16) => meminst.read_i16(ea)? as u32,
            };
            stack.push_i32(v)
        }
        LoadI64(opt, memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &store.mems()[memaddr.to_usize()];
            let v = match opt {
                None => meminst.read_i64(ea)?,
                Some(LoadI64Opt::S8) => meminst.read_i8(ea)? as i8 as i64 as u64,
                Some(LoadI64Opt::U8) => meminst.read_i8(ea)? as u64,
                Some(LoadI64Opt::S16) => meminst.read_i16(ea)? as i16 as i64 as u64,
                Some(LoadI64Opt::U16) => meminst.read_i16(ea)? as u64,
                Some(LoadI64Opt::S32) => meminst.read_i32(ea)? as i32 as i64 as u64,
                Some(LoadI64Opt::U32) => meminst.read_i32(ea)? as u64,
            };
            stack.push_i64(v)
        }
        LoadF32(memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &store.mems()[memaddr.to_usize()];
            let v = meminst.read_f32(ea)?;
            stack.push_f32(v)
        }
        LoadF64(memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &store.mems()[memaddr.to_usize()];
            let v = meminst.read_f64(ea)?;
            stack.push_f64(v)
        }

        StoreI32(opt, memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let v = stack.pop_i32()?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &mut store.mems_mut()[memaddr.to_usize()];
            match opt {
                None => meminst.write_i32(ea, v),
                Some(StoreI32Opt::L8) => meminst.write_i8(ea, v as u8),
                Some(StoreI32Opt::L16) => meminst.write_i16(ea, v as u16),
            }
        }
        StoreI64(opt, memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let v = stack.pop_i64()?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &mut store.mems_mut()[memaddr.to_usize()];
            match opt {
                None => meminst.write_i64(ea, v),
                Some(StoreI64Opt::L8) => meminst.write_i8(ea, v as u8),
                Some(StoreI64Opt::L16) => meminst.write_i16(ea, v as u16),
                Some(StoreI64Opt::L32) => meminst.write_i32(ea, v as u32),
            }
        }
        StoreF32(memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let v = stack.pop_f32()?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &mut store.mems_mut()[memaddr.to_usize()];
            meminst.write_f32(ea, v)
        }
        StoreF64(memarg) => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let v = stack.pop_f64()?;
            let i = stack.pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &mut store.mems_mut()[memaddr.to_usize()];
            meminst.write_f64(ea, v)
        }
        MemorySize => {
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let meminst = &mut store.mems_mut()[memaddr.to_usize()];
            let result = meminst.size_in_page();
            assert!(result <= (u32::MAX as usize));
            stack.push_i32(result as u32)
        }
        MemoryGrow => {
            let n = stack.pop_i32()? as usize;
            let memaddr = frame.resolve_memaddr(Memidx::new(0))?;
            let meminst = &mut store.mems_mut()[memaddr.to_usize()];
            let result = meminst.grow(n)?.unwrap_or(u32::MAX);
            stack.push_i32(result)
        }

        _ => unreachable!("{:?}", instr),
    }
}

pub fn instantiate(ctx: &mut Context, module: &Module) -> Result<Moduleinst, ExecutionError> {
    let mut executor = Executor::new();

    let mut initial_global_values = Vec::new();
    for global in module.globals() {
        let value = executor.eval(ctx, None, global.init())?;
        initial_global_values.push(value);
    }

    let moduleinst = ctx.store.instantiate(module, initial_global_values)?;

    for elem in module.elems() {
        let eoval = executor.eval(ctx, Some(moduleinst.make_clone()), elem.offset())?;
        let eo = match eoval.kind() {
            ValueKind::I32(n) => n as usize,
            _ => unimplemented!(), // @todo raise Error
        };

        let tableidx = elem.table();
        let tableaddr = moduleinst.resolve_tableaddr(tableidx)?;
        let tableinst = &mut ctx.store.tables_mut()[tableaddr.to_usize()];

        let eend = eo + elem.init().len();
        if eend > tableinst.elem().len() {
            unimplemented!() // @todo raise Error
        }

        for (j, funcidx) in elem.init().iter().enumerate() {
            let funcaddr = moduleinst.resolve_funcaddr(*funcidx)?;
            tableinst.elem_mut()[eo + j] = Some(funcaddr);
        }
    }

    for datum in module.data() {
        let doval = executor.eval(ctx, Some(moduleinst.make_clone()), datum.offset())?;
        let dofst = match doval.kind() {
            ValueKind::I32(n) => n as usize,
            _ => unimplemented!(), // @todo raise Error
        };

        let memidx = datum.data();
        let memaddr = moduleinst.resolve_memaddr(memidx)?;
        let meminst = &mut ctx.store.mems_mut()[memaddr.to_usize()];

        let dend = dofst + datum.init().len();
        if dend > meminst.size() {
            unimplemented!() // @todo raise Error
        }

        for (i, &b) in datum.init().iter().enumerate() {
            meminst.write_i8(dofst + i, b)?;
        }
    }

    Ok(moduleinst)
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExecutionError {
    InstantiationFailure(String),
    TypeConfusion {
        expected: Valtype,
        actual: Valtype,
    },
    StackEntryConfusion {
        expected: &'static str,
        actual: &'static str,
    },
    StackOperationFailure(&'static str),
    OutOfRangeAccess {
        size: usize,
        index: usize,
        detail: &'static str,
    },
    ExplicitTrap,
    ZeroDivision,
    IntegerOverflow,
    OutOfBoundsMemoryAccess,
    UndefinedElement,
    IndirectCallTypeMismatch,
    InvalidConversionToInteger,
    UninitializedElement,
    ExecutorStateInconsistency(&'static str),
}

impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExecutionError::*;
        match self {
            TypeConfusion { expected, actual } => write!(
                f,
                "TypeConfusion: expected type {:?}, actual {:?}",
                expected, actual
            ),
            StackEntryConfusion { expected, actual } => write!(
                f,
                "StackEntryConfusion: expected entry type {:?}, actual {:?}",
                expected, actual
            ),
            StackOperationFailure(detail) => write!(f, "StackOperationFailure: {}", detail),
            InstantiationFailure(detail) => write!(f, "InstantiationFailure: {}", detail),
            OutOfRangeAccess {
                size,
                index,
                detail,
            } => write!(
                f,
                "OutOfRangeAccess: {}, size {}, index {}",
                detail, size, index
            ),
            ExplicitTrap => write!(f, "ExplicitTrap:"),
            ZeroDivision => write!(f, "ZeroDivision:"),
            IntegerOverflow => write!(f, "IntegerOverflow:"),
            OutOfBoundsMemoryAccess => write!(f, "OutOfBoundsMemoryAccess:"),
            UndefinedElement => write!(f, "UndefinedElement:"),
            IndirectCallTypeMismatch => write!(f, "IndirectCallTypeMismatch:"),
            InvalidConversionToInteger => write!(f, "InvalidConversionToInteger:"),
            UninitializedElement => write!(f, "UninitializedElement:"),
            ExecutorStateInconsistency(detail) => {
                write!(f, "ExecutorStateInconsistency: {}", detail)
            }
        }
    }
}

pub type CodeAddr = usize;

#[derive(Debug)]
enum Code {
    Instr(InstrSeq, usize),
    Nop,
    Unreachable,
    Block(Blocktype, CodeAddr),
    Loop(Blocktype, CodeAddr),
    If(Blocktype, CodeAddr, CodeAddr),
    Br(Labelidx),
    BrIf(Labelidx),
    BrTable(Vec<Labelidx>, Labelidx),
    Return,
    Call(Funcidx),
    CallIndirect(Typeidx),
    End(Option<CodeAddr>),
}

fn instr_seq_to_code(instr_seq: &InstrSeq) -> Vec<Code> {
    fn instr_seq_to_code_helper(instr_seq: &InstrSeq, code: &mut Vec<Code>) {
        for (i, instr) in instr_seq.instr_seq().iter().enumerate() {
            match &instr.kind {
                InstrKind::Nop => code.push(Code::Nop),
                InstrKind::Unreachable => code.push(Code::Unreachable),
                InstrKind::Block(blocktype, instr_seq) => {
                    let rewrite_index = code.len();
                    code.push(Code::Nop);
                    instr_seq_to_code_helper(&instr_seq, code);
                    let cont_addr = code.len();
                    code[rewrite_index] = Code::Block(blocktype.clone(), cont_addr);
                }
                InstrKind::Loop(blocktype, instr_seq) => {
                    let cont_addr = code.len();
                    code.push(Code::Loop(blocktype.clone(), cont_addr));
                    instr_seq_to_code_helper(&instr_seq, code);
                }
                InstrKind::If(blocktype, then_instr_seq, else_instr_seq) => {
                    let rewrite_index = code.len();
                    code.push(Code::Nop);
                    instr_seq_to_code_helper(&then_instr_seq, code);
                    let then_end_index = code.len() - 1;
                    let else_addr = code.len();
                    instr_seq_to_code_helper(&else_instr_seq, code);
                    let cont_addr = code.len();
                    code[rewrite_index] = Code::If(blocktype.clone(), else_addr, cont_addr);
                    code[then_end_index] = Code::End(Some(cont_addr));
                }
                InstrKind::Br(labelidx) => code.push(Code::Br(*labelidx)),
                InstrKind::BrIf(labelidx) => code.push(Code::BrIf(*labelidx)),
                InstrKind::BrTable(labelidxes, default_labelidx) => {
                    code.push(Code::BrTable(labelidxes.clone(), *default_labelidx))
                }
                InstrKind::Return => code.push(Code::Return),
                InstrKind::Call(funcidx) => code.push(Code::Call(*funcidx)),
                InstrKind::CallIndirect(typeidx) => code.push(Code::CallIndirect(*typeidx)),
                _ => code.push(Code::Instr(instr_seq.make_clone(), i)),
            };
        }
        code.push(Code::End(None));
    }
    let mut code = Vec::new();
    instr_seq_to_code_helper(instr_seq, &mut code);
    code
}

struct Executor {
    code: Vec<Code>,
    code_stack: Vec<Vec<Code>>, // @todo fix to manage Code  in Context
}

impl Executor {
    fn new() -> Self {
        Self {
            code: Vec::new(),
            code_stack: Vec::new(),
        }
    }

    fn current_code(&self, ctx: &Context) -> Option<&Code> {
        let code_addr = ctx.code_addr();
        if code_addr < self.code.len() {
            Some(&self.code[code_addr])
        } else {
            None
        }
    }

    fn enter_block(
        &mut self,
        ctx: &mut Context,
        next_code_addr: CodeAddr,
        num_params: usize,
        label: Label,
    ) -> Result<(), ExecutionError> {
        let mut args = Vec::new();
        for _ in 0..num_params {
            let arg = ctx.stack_mut().pop_value()?;
            args.push(arg);
        }

        ctx.stack_mut().push_label(label)?;

        while let Some(arg) = args.pop() {
            ctx.stack_mut().push_value(arg)?;
        }

        ctx.update_code_addr(next_code_addr);

        Ok(())
    }

    fn exit_block(
        &mut self,
        ctx: &mut Context,
        next_code_addr: Option<CodeAddr>,
    ) -> Result<(), ExecutionError> {
        let mut results = Vec::new();
        loop {
            let entry = ctx.stack().peek_stack_entry()?;
            use StackEntry::*;
            match entry {
                Value(_) => (),
                Label(_) => break,
                Frame(_) => unreachable!(), // @todo raise ExecutionError
            }
            let result = ctx.stack_mut().pop_value()?;
            results.push(result);
        }

        ctx.stack_mut().pop_label()?;

        while let Some(result) = results.pop() {
            ctx.stack_mut().push_value(result)?;
        }

        if let Some(next_code_addr) = next_code_addr {
            ctx.update_code_addr(next_code_addr);
        } else {
            ctx.increment_code_addr();
        }

        Ok(())
    }

    fn branch(&mut self, labelidx: Labelidx, ctx: &mut Context) -> Result<(), ExecutionError> {
        let mut values = Vec::new();
        loop {
            let entry = ctx.stack().peek_stack_entry()?;
            use StackEntry::*;
            match entry {
                Value(_) => (),
                Label(_) => break,
                Frame(_) => unreachable!(), // @todo create ExecutionError
            }
            let value = ctx.stack_mut().pop_value()?;
            values.push(value);
        }

        for _ in 0..labelidx.to_usize() {
            let _label = ctx.stack_mut().pop_label()?;
            loop {
                let entry = ctx.stack().peek_stack_entry()?;
                use StackEntry::*;
                match entry {
                    Value(_) => (),
                    Label(_) => break,
                    Frame(_) => unreachable!(), // @todo create ExecutionError
                }
                ctx.stack_mut().pop_value()?;
            }
        }

        let label = ctx.stack_mut().pop_label()?;
        for _ in 0..(values.len() - label.arity()) {
            values.pop();
        }
        while let Some(value) = values.pop() {
            ctx.stack_mut().push_value(value)?;
        }
        ctx.update_code_addr(label.cont_addr());

        Ok(())
    }

    fn enter_function(
        &mut self,
        ctx: &mut Context,
        module: Option<Moduleinst>,
        param_size: usize,
        return_size: usize,
        local_var_types: &[Valtype],
        mut code: Vec<Code>,
        return_code_addr: CodeAddr,
    ) -> Result<(), ExecutionError> {
        if param_size + local_var_types.len() > u32::MAX as usize {
            return Err(ExecutionError::StackOperationFailure(
                "number of locals reaches limitation",
            ));
        }

        let mut locals: Vec<Value> = local_var_types
            .iter()
            .rev()
            .map(|t| {
                let zero_val_kind = match t {
                    Valtype::I32 => ValueKind::I32(0),
                    Valtype::I64 => ValueKind::I64(0),
                    Valtype::F32 => ValueKind::F32(F32Bytes::new(0.0)),
                    Valtype::F64 => ValueKind::F64(F64Bytes::new(0.0)),
                };
                Value::new(zero_val_kind)
            })
            .collect();

        for _ in 0..param_size {
            let val = ctx.stack_mut().pop_value()?;
            locals.push(val);
        }

        locals.reverse();

        let prev_frame = ctx.current_frame().make_clone();
        let frame = Frame::new(
            locals,
            return_size,
            module,
            Some(prev_frame),
            return_code_addr,
        );
        ctx.stack_mut().push_frame(frame.make_clone())?;
        ctx.update_frame(frame);

        mem::swap(&mut self.code, &mut code);
        self.code_stack.push(code);

        Ok(())
    }

    fn exit_function(&mut self, ctx: &mut Context) -> Result<(), ExecutionError> {
        let mut result = Vec::new();
        let num_result = ctx.current_frame().num_result();
        for _ in 0..num_result {
            let ret = ctx.stack_mut().pop_value()?;
            result.push(ret);
        }

        loop {
            let entry = ctx.stack().peek_stack_entry()?;
            if let StackEntry::Frame(_) = entry {
                break;
            }
            ctx.stack_mut().pop_stack_entry()?;
        }

        let frame = ctx.stack_mut().pop_frame()?;
        let cont_code_addr = frame.return_code_addr();
        ctx.update_frame(frame.prev_frame().unwrap());
        ctx.update_code_addr(cont_code_addr);

        while let Some(ret) = result.pop() {
            ctx.stack_mut().push_value(ret)?;
        }

        let mut prev_code = self.code_stack.pop().unwrap();
        mem::swap(&mut self.code, &mut prev_code);

        Ok(())
    }

    fn eval(
        &mut self,
        ctx: &mut Context,
        moduleinst: Option<Moduleinst>,
        expr: &Expr,
    ) -> Result<Value, ExecutionError> {
        ctx.stack().assert_stack_is_empty();

        let param_size = 0;
        let return_size = 1;

        let code = instr_seq_to_code(expr.instr_seq());
        let cont_addr = code.len();
        let label = Label::new(return_size, cont_addr);
        let next_code_addr = 0;

        self.enter_function(
            ctx,
            moduleinst,
            param_size,
            return_size,
            &[],
            code,
            cont_addr,
        )?;
        self.enter_block(ctx, next_code_addr, 0, label)?;
        self.execute(ctx)?;

        let result = ctx.stack_mut().pop_value()?;

        ctx.stack().assert_stack_is_empty();

        Ok(result)
    }

    fn invoke_function(
        &mut self,
        ctx: &mut Context,
        funcaddr: Funcaddr,
    ) -> Result<(), ExecutionError> {
        let funcinst = &ctx.store.funcs()[funcaddr.to_usize()];

        match funcinst {
            Funcinst::UserDefined { typ, module, code } => {
                let func = code.make_clone();

                let param_size = typ.param_type().len();
                let return_size = typ.return_type().len();
                let module = module.make_clone();

                let code = instr_seq_to_code(func.body().instr_seq());

                let cont_addr = code.len();
                let label = Label::new(return_size, cont_addr);

                let return_code_addr = ctx.code_addr() + 1;

                let next_code_addr = 0;
                self.enter_function(
                    ctx,
                    Some(module),
                    param_size,
                    return_size,
                    func.locals(),
                    code,
                    return_code_addr,
                )?;
                self.enter_block(ctx, next_code_addr, 0, label)?;
            }

            Funcinst::Host { typ, hostcode } => {
                let param_size = typ.param_type().len();
                let func = hostcode.code();

                let mut params = Vec::new();
                for _ in 0..param_size {
                    let val = ctx.stack_mut().pop_value()?;
                    params.push(val);
                }
                params.reverse();

                let WasmRunnerResult::Values(mut result) = func(params)?;
                result.reverse();

                while let Some(ret) = result.pop() {
                    ctx.stack_mut().push_value(ret)?;
                }

                ctx.increment_code_addr();
            }
        }

        Ok(())
    }

    fn execute(&mut self, ctx: &mut Context) -> Result<(), ExecutionError> {
        // @todo fix to refer Frame
        while !self.code_stack.is_empty() {
            while let Some(code) = self.current_code(ctx) {
                use Code::*;
                match code {
                    Instr(instr_seq, index) => {
                        execute_instr(
                            &instr_seq.instr_seq()[*index],
                            &mut ctx.stack,
                            &mut ctx.current_frame,
                            &mut ctx.store,
                        )?;
                        ctx.increment_code_addr();
                    }
                    Nop => {
                        ctx.increment_code_addr();
                    }
                    Unreachable => return Err(ExecutionError::ExplicitTrap),
                    Block(blocktype, cont_addr) => {
                        let blocktype = ctx.current_frame().expand_blocktype(blocktype)?;
                        let num_params = blocktype.param_type().len();
                        let num_returns = blocktype.return_type().len();
                        let label = Label::new(num_returns, *cont_addr);
                        let next_code_addr = ctx.code_addr() + 1;
                        self.enter_block(ctx, next_code_addr, num_params, label)?;
                    }
                    Loop(blocktype, cont_addr) => {
                        let blocktype = ctx.current_frame().expand_blocktype(blocktype)?;
                        let num_params = blocktype.param_type().len();
                        let label = Label::new(num_params, *cont_addr);
                        let next_code_addr = ctx.code_addr() + 1;
                        self.enter_block(ctx, next_code_addr, num_params, label)?;
                    }
                    If(blocktype, else_addr, cont_addr) => {
                        let blocktype = ctx.current_frame().expand_blocktype(blocktype)?;
                        let num_params = blocktype.param_type().len();
                        let num_returns = blocktype.return_type().len();
                        let label = Label::new(num_returns, *cont_addr);
                        let cond = ctx.stack_mut().pop_i32()?;
                        let next_code_addr = if cond != 0 {
                            ctx.code_addr() + 1
                        } else {
                            *else_addr
                        };
                        self.enter_block(ctx, next_code_addr, num_params, label)?;
                    }
                    Br(labelidx) => {
                        let labelidx = *labelidx;
                        self.branch(labelidx, ctx)?;
                    }
                    BrIf(labelidx) => {
                        let c = ctx.stack_mut().pop_i32()?;
                        if c != 0 {
                            let labelidx = *labelidx;
                            self.branch(labelidx, ctx)?;
                        } else {
                            ctx.increment_code_addr();
                        }
                    }
                    BrTable(labelidxes, default_labelidx) => {
                        let i = ctx.stack_mut().pop_i32()? as usize;
                        let labelidx = if i < labelidxes.len() {
                            labelidxes[i]
                        } else {
                            *default_labelidx
                        };
                        self.branch(labelidx, ctx)?;
                    }
                    Return => break,
                    Call(funcidx) => {
                        let funcaddr = ctx.current_frame().resolve_funcaddr(*funcidx)?;
                        self.invoke_function(ctx, funcaddr)?;
                    }
                    CallIndirect(typeidx) => {
                        let tableaddr = ctx.current_frame().resolve_tableaddr(Tableidx::new(0))?;
                        let i = ctx.stack_mut().pop_i32()? as usize;
                        let tableinst = &ctx.store.tables()[tableaddr.to_usize()];
                        if i >= tableinst.elem().len() {
                            return Err(ExecutionError::UndefinedElement);
                        }
                        let typ = &ctx.current_frame().resolve_type(*typeidx)?;
                        if tableinst.elem()[i].is_none() {
                            return Err(ExecutionError::UninitializedElement);
                        }
                        let funcaddr = tableinst.elem()[i].unwrap();
                        let f = &ctx.store.funcs()[funcaddr.to_usize()];
                        if typ != f.typ() {
                            return Err(ExecutionError::IndirectCallTypeMismatch);
                        }
                        self.invoke_function(ctx, funcaddr)?;
                    }
                    End(next_code_addr) => {
                        let next_code_addr = *next_code_addr;
                        self.exit_block(ctx, next_code_addr)?;
                    }
                }
            }
            self.exit_function(ctx)?;
        }
        Ok(())
    }
}

pub fn invoke(
    ctx: &mut Context,
    funcaddr: Funcaddr,
    args: Vec<Value>,
) -> Result<WasmRunnerResult, ExecutionError> {
    ctx.stack().assert_stack_is_empty();
    let funcinst = &ctx.store.funcs()[funcaddr.to_usize()];
    let return_size = funcinst.typ().return_type().len();
    assert_eq!(args.len(), funcinst.typ().param_type().len()); // @todo Err

    for arg in args {
        ctx.stack_mut().push_value(arg)?;
    }

    let mut executor = Executor::new();
    executor.invoke_function(ctx, funcaddr)?;
    executor.execute(ctx)?;

    let mut result_values = Vec::new();
    for _ in 0..return_size {
        let value = ctx.stack_mut().pop_value()?;
        result_values.push(value);
    }
    result_values.reverse();

    ctx.stack().assert_stack_is_empty();
    Ok(WasmRunnerResult::Values(result_values))
}
