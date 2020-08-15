use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use crate::instance::*;
use crate::instr::*;
use crate::module::*;
use crate::types::*;
use crate::value::*;

#[derive(Debug, PartialEq, Eq)]
struct FrameInner {
    locals: Vec<Value>,
    module: Option<Moduleinst>,
    num_result: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Frame(Rc<RefCell<FrameInner>>);

impl Frame {
    pub fn new(locals: Vec<Value>, num_result: usize, module: Option<Moduleinst>) -> Self {
        Self(Rc::new(RefCell::new(FrameInner {
            locals,
            module,
            num_result,
        })))
    }

    pub fn resolve_funcaddr(&self, funcidx: Funcidx) -> Result<Funcaddr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_funcaddr(funcidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_tableaddr(&self, tableidx: Tableidx) -> Result<Tableaddr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_tableaddr(tableidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_memaddr(&self, memidx: Memidx) -> Result<Memaddr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_memaddr(memidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_type(&self, typeidx: Typeidx) -> Result<Functype, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_type(typeidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn num_result(&self) -> usize {
        self.0.borrow().num_result
    }

    fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }

    pub fn get(&self, idx: Localidx) -> Result<Value, ExecutionError> {
        let idx = idx.to_usize();
        let locals = &self.0.borrow().locals;
        if idx < locals.len() {
            Ok(locals[idx])
        } else {
            Err(ExecutionError::OutOfRangeAccess {
                size: locals.len(),
                index: idx,
                detail: "Local/Get",
            })
        }
    }

    pub fn set(&mut self, idx: Localidx, val: Value) -> Result<(), ExecutionError> {
        let idx = idx.to_usize();
        let locals = &mut self.0.borrow_mut().locals;
        if idx < locals.len() {
            locals[idx] = val;
            Ok(())
        } else {
            Err(ExecutionError::OutOfRangeAccess {
                size: locals.len(),
                index: idx,
                detail: "Local/Set",
            })
        }
    }

    fn expand_blocktype(&self, blocktype: &Blocktype) -> Result<Functype, ExecutionError> {
        use Blocktype::*;
        match blocktype {
            Empty => Ok(Functype::new(
                Resulttype::new(vec![]),
                Resulttype::new(vec![]),
            )),
            Valtype(valtype) => Ok(Functype::new(
                Resulttype::new(vec![]),
                Resulttype::new(vec![valtype.clone()]),
            )),
            S33(x) => self.0.borrow().module.as_ref().unwrap().resolve_type(*x),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Label {
    arity: usize,
}

impl Label {
    fn new(arity: usize) -> Self {
        Self { arity }
    }

    fn arity(&self) -> usize {
        self.arity
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
}

impl Context {
    pub fn new() -> Self {
        let unused_frame = Frame::new(Vec::new(), 0, None);
        Self {
            store: Store::new(),
            stack: Stack::new(),
            current_frame: unused_frame,
        }
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
}

#[derive(Debug, PartialEq, Eq)]
enum Control {
    Fallthrough,
    Branch(usize),
    Return,
}

fn execute(instr: &Instr, ctx: &mut Context) -> Result<Control, ExecutionError> {
    use Control::*;
    use InstrKind::*;
    match &instr.kind {
        ConstI32(c) => ctx.stack_mut().push_i32(*c).map(|_| Fallthrough),
        ConstI64(c) => ctx.stack_mut().push_i64(*c).map(|_| Fallthrough),

        UnopI32(op) => {
            let c = ctx.stack_mut().pop_i32()?;
            let v = match op {
                UnopKind::Ctz => c.trailing_zeros(),
            };
            ctx.stack_mut().push_i32(v).map(|_| Fallthrough)
        }
        UnopI64(op) => {
            let c = ctx.stack_mut().pop_i64()?;
            let v = match op {
                UnopKind::Ctz => c.trailing_zeros() as u64,
            };
            ctx.stack_mut().push_i64(v).map(|_| Fallthrough)
        }

        BinopI32(op) => {
            let c2 = ctx.stack_mut().pop_i32()?;
            let c1 = ctx.stack_mut().pop_i32()?;
            let v = match op {
                BinopKind::Add => c1.wrapping_add(c2),
                BinopKind::Sub => c1.wrapping_sub(c2),
                BinopKind::Mul => c1.wrapping_mul(c2),
                BinopKind::UDiv => {
                    if c2 != 0 {
                        c1 / c2
                    } else {
                        return Err(ExecutionError::ZeroDivision);
                    }
                }
            };
            ctx.stack_mut().push_i32(v).map(|_| Fallthrough)
        }

        TestopI32(op) => {
            let c = ctx.stack_mut().pop_i32()?;
            let v = match op {
                TestopKind::Eqz if c == 0 => 1,
                TestopKind::Eqz => 0,
            };
            ctx.stack_mut().push_i32(v).map(|_| Fallthrough)
        }

        RelopI32(op) => {
            let c2 = ctx.stack_mut().pop_i32()?;
            let c1 = ctx.stack_mut().pop_i32()?;
            let v = match op {
                RelopKind::Eq if c1 == c2 => 1,
                _ => 0,
            };
            ctx.stack_mut().push_i32(v).map(|_| Fallthrough)
        }

        Drop => ctx.stack_mut().pop_value().map(|_| Fallthrough),
        Select => {
            let c = ctx.stack_mut().pop_i32()?;
            let val2 = ctx.stack_mut().pop_value()?;
            let val1 = ctx.stack_mut().pop_value()?;
            let val = if c != 0 { val1 } else { val2 };
            ctx.stack_mut().push_value(val).map(|_| Fallthrough)
        }

        GetLocal(idx) => {
            let v = ctx.current_frame().get(*idx)?;
            ctx.stack_mut().push_value(v).map(|_| Fallthrough)
        }
        SetLocal(idx) => {
            let v = ctx.stack_mut().pop_value()?;
            ctx.current_frame_mut().set(*idx, v).map(|_| Fallthrough)
        }

        StoreI32(memarg) => {
            let memaddr = ctx.current_frame().resolve_memaddr(Memidx::new(0))?;
            let c = ctx.stack_mut().pop_i32()?;
            let i = ctx.stack_mut().pop_i32()? as usize;
            let ea = (memarg.offset() as usize) + i;
            let meminst = &mut ctx.store.mems_mut()[memaddr.to_usize()];
            meminst.write_i32(ea, c).map(|_| Fallthrough)
        }

        Nop => Ok(Fallthrough),
        Unreachable => Err(ExecutionError::ExplicitTrap),
        Block(blocktype, instr_seq) => {
            let arity = ctx
                .current_frame()
                .expand_blocktype(blocktype)?
                .return_type()
                .len();
            // @todo pop values
            let ctrl = execute_instr_seq(ctx, instr_seq, Label::new(arity))?;
            match ctrl {
                Branch(0) => Ok(Fallthrough),
                Branch(count) => Ok(Branch(count - 1)),
                ctrl => Ok(ctrl),
            }
        }
        Loop(blocktype, instr_seq) => {
            let arity = ctx
                .current_frame()
                .expand_blocktype(blocktype)?
                .return_type()
                .len();
            // @todo pop values
            let ctrl = loop {
                let ctrl = execute_instr_seq(ctx, instr_seq, Label::new(arity))?;
                match ctrl {
                    Branch(0) => (),
                    Branch(count) => break Branch(count - 1),
                    ctrl => break ctrl,
                }
            };
            Ok(ctrl)
        }
        If(blocktype, then_instr_seq, else_instr_seq) => {
            let arity = ctx
                .current_frame()
                .expand_blocktype(blocktype)?
                .return_type()
                .len();
            let cond = ctx.stack_mut().pop_i32()?;
            // @todo pop values
            let label = Label::new(arity);
            let ctrl = if cond != 0 {
                execute_instr_seq(ctx, then_instr_seq, label)
            } else {
                execute_instr_seq(ctx, else_instr_seq, label)
            }?;
            let ctrl = match ctrl {
                Branch(0) => Fallthrough,
                Branch(count) => Branch(count - 1),
                ctrl => ctrl,
            };
            Ok(ctrl)
        }
        Br(labelidx) => branch(labelidx, ctx),
        BrIf(labelidx) => {
            let c = ctx.stack_mut().pop_i32()?;
            if c != 0 {
                branch(labelidx, ctx)
            } else {
                Ok(Fallthrough)
            }
        }
        BrTable(labelidxes, default_labelidx) => {
            let i = ctx.stack_mut().pop_i32()? as usize;
            if i < labelidxes.len() {
                branch(&labelidxes[i], ctx)
            } else {
                branch(default_labelidx, ctx)
            }
        }
        InstrKind::Return => {
            let mut values = Vec::new();
            let num_results = ctx.current_frame().num_result();
            for _ in 0..num_results {
                let value = ctx.stack_mut().pop_value()?;
                values.push(value);
            }
            loop {
                let entry = ctx.stack().peek_stack_entry()?;
                use StackEntry::*;
                match entry {
                    Frame(_) => break,
                    _ => (),
                }
                ctx.stack_mut().pop_stack_entry()?;
            }
            while let Some(value) = values.pop() {
                ctx.stack_mut().push_value(value)?;
            }
            Ok(Control::Return)
        }
        Call(funcidx) => {
            let funcaddr = ctx.current_frame().resolve_funcaddr(*funcidx)?;
            invoke_func(ctx, funcaddr).map(|_| Fallthrough)
        }
        CallIndirect(typeidx) => {
            let tableaddr = ctx.current_frame().resolve_tableaddr(Tableidx::new(0))?;
            let i = ctx.stack_mut().pop_i32()? as usize;
            let tableinst = &ctx.store.tables()[tableaddr.to_usize()];
            if i >= tableinst.elem().len() {
                unimplemented!() // @todo raise Error
            }
            let typ = &ctx.current_frame().resolve_type(*typeidx)?;
            if tableinst.elem()[i].is_none() {
                unimplemented!() // @todo raise Error
            }
            let funcaddr = tableinst.elem()[i].unwrap();
            let f = &ctx.store.funcs()[funcaddr.to_usize()];
            if typ != f.typ() {
                unimplemented!() // @todo raise Error
            }
            invoke_func(ctx, funcaddr).map(|_| Fallthrough)
        }

        _ => unreachable!("{:?}", instr),
    }
}

fn branch(labelidx: &Labelidx, ctx: &mut Context) -> Result<Control, ExecutionError> {
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
    for _ in 0..(labelidx.to_usize()) {
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
    Ok(Control::Branch(labelidx.to_usize()))
}

pub fn instantiate(module: &Module) -> Result<(Moduleinst, Context), ExecutionError> {
    let mut ctx = Context::new();
    let moduleinst = ctx.store.instantiate(module)?;

    // @todo push Frame

    let mut offsets = Vec::new();
    for elem in module.elems() {
        let eoval = eval(&mut ctx, elem.offset())?;
        let eo = match eoval.kind() {
            ValueKind::I32(n) => n as usize,
            _ => unimplemented!(), // @todo raise Error
        };

        let tableidx = elem.table();
        let tableaddr = moduleinst.resolve_tableaddr(tableidx)?;
        let tableinst = &ctx.store.tables()[tableaddr.to_usize()];

        let eend = eo + elem.init().len();
        if eend > tableinst.elem().len() {
            unimplemented!() // @todo raise Error
        }

        offsets.push(eo);
    }

    // @todo pop Frame

    for (i, (elem, eo)) in module.elems().iter().zip(offsets.iter()).enumerate() {
        let tableinst = &mut ctx.store.tables_mut()[i];
        for (j, funcidx) in elem.init().iter().enumerate() {
            let funcaddr = moduleinst.resolve_funcaddr(*funcidx)?;
            tableinst.elem_mut()[eo + j] = Some(funcaddr);
        }
    }

    Ok((moduleinst, ctx))
}

fn eval(ctx: &mut Context, expr: &Expr) -> Result<Value, ExecutionError> {
    let label = Label::new(1);
    let ctrl = execute_instr_seq(ctx, expr.instr_seq(), label)?;
    match ctrl {
        Control::Branch(_) => unreachable!(),
        Control::Fallthrough => (),
        Control::Return => (),
    };
    ctx.stack_mut().pop_value()
}

fn execute_instr_seq(
    ctx: &mut Context,
    instr_seq: &InstrSeq,
    label: Label,
) -> Result<Control, ExecutionError> {
    // enter instr_seq with label
    let arity = label.arity();
    ctx.stack_mut().push_label(label)?;

    for instr in instr_seq.instr_seq().iter() {
        let ctrl = execute(instr, ctx)?;
        use Control::*;
        match ctrl {
            Fallthrough => (),
            ctrl => return Ok(ctrl),
        }
    }

    // exit instr_seq with label
    let mut tmp = Vec::new();
    for _ in 0..arity {
        let value = ctx.stack_mut().pop_value()?;
        tmp.push(value);
    }
    ctx.stack_mut().pop_label()?;
    while let Some(value) = tmp.pop() {
        ctx.stack_mut().push_value(value)?;
    }
    Ok(Control::Fallthrough)
}

fn invoke_func(ctx: &mut Context, funcaddr: Funcaddr) -> Result<Control, ExecutionError> {
    let funcinst = &ctx.store.funcs()[funcaddr.to_usize()];
    let func = funcinst.code().clone();

    let param_size = funcinst.typ().param_type().len();
    let return_size = funcinst.typ().return_type().len();
    let locals_size = func.locals().len();
    let body = func.body().make_clone();
    let module = funcinst.module().make_clone();

    if param_size + locals_size > u32::MAX as usize {
        return Err(ExecutionError::StackOperationFailure(
            "number of locals reaches limitation",
        ));
    }

    let mut locals = Vec::with_capacity(param_size + locals_size);
    for _ in 0..param_size {
        let val = ctx.stack_mut().pop_value()?;
        locals.push(val);
    }
    locals.reverse();

    for _ in 0..locals_size {
        let zero_val = Value::new(ValueKind::I32(0)); // @todo
        locals.push(zero_val);
    }

    let frame = Frame::new(locals, return_size, Some(module));
    ctx.stack_mut().push_frame(frame.make_clone())?;

    let prev_frame = ctx.current_frame().make_clone();
    ctx.update_frame(frame);

    let label = Label::new(return_size);
    let ctrl = execute_instr_seq(ctx, body.instr_seq(), label)?;
    let ctrl = match ctrl {
        Control::Branch(_) => unreachable!(),
        Control::Fallthrough => Control::Fallthrough,
        Control::Return => Control::Fallthrough,
    };

    let mut result = Vec::new();
    for _ in 0..return_size {
        let ret = ctx.stack_mut().pop_value()?;
        result.push(ret);
    }

    ctx.stack_mut().pop_frame()?;
    ctx.update_frame(prev_frame);

    for ret in result {
        ctx.stack_mut().push_value(ret)?;
    }

    Ok(ctrl)
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

    let dummy_frame = Frame::new(Vec::new(), 0, None);
    ctx.stack_mut().push_frame(dummy_frame.make_clone())?;
    ctx.update_frame(dummy_frame.make_clone());

    for arg in args {
        ctx.stack_mut().push_value(arg)?;
    }

    let ctrl = invoke_func(ctx, funcaddr)?;
    match ctrl {
        Control::Branch(_) => unreachable!(),
        Control::Fallthrough => (),
        Control::Return => unreachable!(),
    };

    let mut result_values = Vec::new();
    for _ in 0..return_size {
        let value = ctx.stack_mut().pop_value()?;
        result_values.push(value);
    }

    ctx.stack_mut().pop_frame()?;
    ctx.update_frame(dummy_frame);

    ctx.stack().assert_stack_is_empty();
    Ok(WasmRunnerResult::Values(result_values))
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
            ExecutorStateInconsistency(detail) => {
                write!(f, "ExecutorStateInconsistency: {}", detail)
            }
        }
    }
}
