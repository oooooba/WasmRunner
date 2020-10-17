use std::collections::VecDeque;

use crate::instr::*;
use crate::module::*;
use crate::types::*;

#[derive(Debug, PartialEq, Eq)]
enum TypeStackEntry {
    Type(Valtype),
    AnyType,
    Polymorphic,
}

struct TypeStack {
    stack: Vec<TypeStackEntry>,
}

impl TypeStack {
    fn new() -> Self {
        Self { stack: Vec::new() }
    }

    fn produce(&mut self, entry: TypeStackEntry) {
        use TypeStackEntry::*;
        if entry == Polymorphic {
            self.stack.clear();
        }
        self.stack.push(entry);
    }

    fn consume(&mut self, entry: TypeStackEntry) -> Result<TypeStackEntry, ValidationError> {
        use TypeStackEntry::*;
        match (self.stack.pop(), entry) {
            (_, Polymorphic) => panic!(),

            (Some(Type(valtype_s)), Type(valtype_e)) if valtype_s == valtype_e => {
                Ok(Type(valtype_s))
            }
            (Some(Type(_)), Type(_)) => unimplemented!(), // @todo
            (Some(Type(valtype_s)), AnyType) => Ok(Type(valtype_s)),

            (Some(AnyType), Type(valtype_e)) => Ok(Type(valtype_e)),
            (Some(AnyType), AnyType) => Ok(AnyType),

            (Some(Polymorphic), Type(valtype_e)) => {
                assert!(self.stack.is_empty());
                self.stack.push(Polymorphic);
                Ok(Type(valtype_e))
            }
            (Some(Polymorphic), AnyType) => {
                assert!(self.stack.is_empty());
                self.stack.push(Polymorphic);
                Ok(AnyType)
            }

            (None, _) => unimplemented!(), // @todo
        }
    }

    fn is_empty(&self) -> bool {
        match self.stack.last() {
            Some(TypeStackEntry::Polymorphic) => true,
            None => true,
            _ => false,
        }
    }
}

struct TypeContext {
    types: Vec<Functype>,
    funcs: Vec<Functype>,
    mems: Vec<Memtype>,
    globals: Vec<Globaltype>,
    locals: Vec<Valtype>,
    labels: VecDeque<Resulttype>,
    return_type: Option<Resulttype>,
}

impl TypeContext {
    fn new() -> Self {
        Self {
            types: Vec::new(),
            funcs: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            locals: Vec::new(),
            labels: VecDeque::new(),
            return_type: None,
        }
    }

    fn validate_limit(&self, limit: &Limit, k: usize) -> Result<(), ValidationError> {
        let n = limit.min() as usize;
        if n > k {
            return Err(ValidationError::Limit(format!(
                "min value ({}) must be less or equal to {}",
                n, k
            )));
        }
        if let Some(m) = limit.max().map(|m| m as usize) {
            if m > k {
                return Err(ValidationError::Limit(format!(
                    "max value ({}) must be less or equal to {}",
                    m, k
                )));
            }
            if n > m {
                return Err(ValidationError::Limit(format!(
                    "min value ({}) must be less or equal to max value ({})",
                    n, m
                )));
            }
        }
        Ok(())
    }

    fn validate_blocktype(&self, blocktype: &Blocktype) -> Result<Functype, ValidationError> {
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
            S33(x) if x.to_usize() < self.types.len() => {
                self.validate_functype(&self.types[x.to_usize()])?;
                Ok(self.types[x.to_usize()].make_clone())
            }
            _ => unimplemented!(), // @todo
        }
    }

    fn validate_functype(&self, _functype: &Functype) -> Result<(), ValidationError> {
        Ok(())
    }

    fn validate_instr(
        &mut self,
        instr: &Instr,
        type_stack: &mut TypeStack,
    ) -> Result<(), ValidationError> {
        use InstrKind::*;
        use TypeStackEntry::*;
        use Valtype::*;
        match &instr.kind {
            ConstI32(_) => type_stack.produce(Type(I32)),
            ConstI64(_) => type_stack.produce(Type(I64)),
            ConstF32(_) => type_stack.produce(Type(F32)),
            ConstF64(_) => type_stack.produce(Type(F64)),

            UnopI32(_) => self.validate_instr_helper_single_op(I32, I32, type_stack)?,
            UnopI64(_) => self.validate_instr_helper_single_op(I64, I64, type_stack)?,
            UnopF32(_) => self.validate_instr_helper_single_op(F32, F32, type_stack)?,
            UnopF64(_) => self.validate_instr_helper_single_op(F64, F64, type_stack)?,
            Extend(kind) => {
                use ExtendKind::*;
                match kind {
                    I32As8S => self.validate_instr_helper_single_op(I32, I32, type_stack)?,
                    I32As16S => self.validate_instr_helper_single_op(I32, I32, type_stack)?,
                    I64As8S => self.validate_instr_helper_single_op(I64, I64, type_stack)?,
                    I64As16S => self.validate_instr_helper_single_op(I64, I64, type_stack)?,
                    I64As32S => self.validate_instr_helper_single_op(I64, I64, type_stack)?,
                }
            }

            BinopI32(_) => self.validate_instr_helper_double_op(I32, I32, type_stack)?,
            BinopI64(_) => self.validate_instr_helper_double_op(I64, I64, type_stack)?,
            BinopF32(_) => self.validate_instr_helper_double_op(F32, F32, type_stack)?,
            BinopF64(_) => self.validate_instr_helper_double_op(F64, F64, type_stack)?,

            TestopI32(_) => self.validate_instr_helper_single_op(I32, I32, type_stack)?,
            TestopI64(_) => self.validate_instr_helper_single_op(I32, I64, type_stack)?,

            RelopI32(_) => self.validate_instr_helper_double_op(I32, I32, type_stack)?,
            RelopI64(_) => self.validate_instr_helper_double_op(I32, I64, type_stack)?,
            RelopF32(_) => self.validate_instr_helper_double_op(I32, F32, type_stack)?,
            RelopF64(_) => self.validate_instr_helper_double_op(I32, F64, type_stack)?,

            Cvtop(ref op) => {
                use CvtopKind::*;
                match op {
                    I32WrapI64 => self.validate_instr_helper_single_op(I32, I64, type_stack)?,
                    I64ExtendI32S => self.validate_instr_helper_single_op(I64, I32, type_stack)?,
                    I64ExtendI32U => self.validate_instr_helper_single_op(I64, I32, type_stack)?,
                    I32TruncF32S => self.validate_instr_helper_single_op(I32, F32, type_stack)?,
                    I32TruncF32U => self.validate_instr_helper_single_op(I32, F32, type_stack)?,
                    I32TruncF64S => self.validate_instr_helper_single_op(I32, F64, type_stack)?,
                    I32TruncF64U => self.validate_instr_helper_single_op(I32, F64, type_stack)?,
                    I64TruncF32S => self.validate_instr_helper_single_op(I64, F32, type_stack)?,
                    I64TruncF32U => self.validate_instr_helper_single_op(I64, F32, type_stack)?,
                    I64TruncF64S => self.validate_instr_helper_single_op(I64, F64, type_stack)?,
                    I64TruncF64U => self.validate_instr_helper_single_op(I64, F64, type_stack)?,
                    I32TruncSatF32S => {
                        self.validate_instr_helper_single_op(I32, F32, type_stack)?
                    }
                    I32TruncSatF32U => {
                        self.validate_instr_helper_single_op(I32, F32, type_stack)?
                    }
                    I32TruncSatF64S => {
                        self.validate_instr_helper_single_op(I32, F64, type_stack)?
                    }
                    I32TruncSatF64U => {
                        self.validate_instr_helper_single_op(I32, F64, type_stack)?
                    }
                    I64TruncSatF32S => {
                        self.validate_instr_helper_single_op(I64, F32, type_stack)?
                    }
                    I64TruncSatF32U => {
                        self.validate_instr_helper_single_op(I64, F32, type_stack)?
                    }
                    I64TruncSatF64S => {
                        self.validate_instr_helper_single_op(I64, F64, type_stack)?
                    }
                    I64TruncSatF64U => {
                        self.validate_instr_helper_single_op(I64, F64, type_stack)?
                    }
                    F32ConvertI32S => self.validate_instr_helper_single_op(F32, I32, type_stack)?,
                    F32ConvertI32U => self.validate_instr_helper_single_op(F32, I32, type_stack)?,
                    F32ConvertI64S => self.validate_instr_helper_single_op(F32, I64, type_stack)?,
                    F32ConvertI64U => self.validate_instr_helper_single_op(F32, I64, type_stack)?,
                    F64ConvertI32S => self.validate_instr_helper_single_op(F64, I32, type_stack)?,
                    F64ConvertI32U => self.validate_instr_helper_single_op(F64, I32, type_stack)?,
                    F64ConvertI64S => self.validate_instr_helper_single_op(F64, I64, type_stack)?,
                    F64ConvertI64U => self.validate_instr_helper_single_op(F64, I64, type_stack)?,
                    F32DemoteF64 => self.validate_instr_helper_single_op(F32, F64, type_stack)?,
                    F64PromoteF32 => self.validate_instr_helper_single_op(F64, F32, type_stack)?,
                    I32ReinterpretF32 => {
                        self.validate_instr_helper_single_op(I32, F32, type_stack)?
                    }
                    I64ReinterpretF64 => {
                        self.validate_instr_helper_single_op(I64, F64, type_stack)?
                    }
                    F32ReinterpretI32 => {
                        self.validate_instr_helper_single_op(F32, I32, type_stack)?
                    }
                    F64ReinterpretI64 => {
                        self.validate_instr_helper_single_op(F64, I64, type_stack)?
                    }
                }
            }

            Drop => {
                type_stack.consume(AnyType)?;
            }
            Select => {
                type_stack.consume(Type(I32))?;
                let t1 = type_stack.consume(AnyType)?;
                let t2 = type_stack.consume(AnyType)?;
                if t1 != t2 {
                    unimplemented!() // @todo
                }
                type_stack.produce(t1)
            }

            GetLocal(idx) => {
                if idx.to_usize() >= self.locals.len() {
                    unimplemented!()
                }
                type_stack.produce(Type(self.locals[idx.to_usize()].clone()));
            }
            SetLocal(idx) => {
                if idx.to_usize() >= self.locals.len() {
                    unimplemented!()
                }
                type_stack.consume(Type(self.locals[idx.to_usize()].clone()))?;
            }
            TeeLocal(idx) => {
                if idx.to_usize() >= self.locals.len() {
                    unimplemented!()
                }
                let t = self.locals[idx.to_usize()].clone();
                type_stack.consume(Type(t.clone()))?;
                type_stack.produce(Type(t));
            }
            GetGlobal(idx) => {
                if idx.to_usize() >= self.globals.len() {
                    unimplemented!()
                }
                type_stack.produce(Type(self.globals[idx.to_usize()].typ().clone()));
            }
            SetGlobal(idx) => {
                if idx.to_usize() >= self.globals.len() {
                    unimplemented!()
                }
                if self.globals[idx.to_usize()].mutability() != &Mutability::Var {
                    unimplemented!()
                }
                type_stack.consume(Type(self.globals[idx.to_usize()].typ().clone()))?;
            }

            LoadI32(opt, memarg) => {
                let bit_width = match opt {
                    None => 32,
                    Some(LoadI32Opt::S8) => 8,
                    Some(LoadI32Opt::U8) => 8,
                    Some(LoadI32Opt::S16) => 16,
                    Some(LoadI32Opt::U16) => 16,
                };
                self.validate_instr_helper_load(memarg, bit_width, I32, type_stack)?;
            }
            LoadI64(opt, memarg) => {
                let bit_width = match opt {
                    None => 64,
                    Some(LoadI64Opt::S8) => 8,
                    Some(LoadI64Opt::U8) => 8,
                    Some(LoadI64Opt::S16) => 16,
                    Some(LoadI64Opt::U16) => 16,
                    Some(LoadI64Opt::S32) => 32,
                    Some(LoadI64Opt::U32) => 32,
                };
                self.validate_instr_helper_load(memarg, bit_width, I64, type_stack)?;
            }
            LoadF32(memarg) => {
                self.validate_instr_helper_load(memarg, 32, F32, type_stack)?;
            }
            LoadF64(memarg) => {
                self.validate_instr_helper_load(memarg, 64, F64, type_stack)?;
            }
            StoreI32(opt, memarg) => {
                let bit_width = match opt {
                    None => 32,
                    Some(StoreI32Opt::L8) => 8,
                    Some(StoreI32Opt::L16) => 16,
                };
                self.validate_instr_helper_store(memarg, bit_width, I32, type_stack)?;
            }
            StoreI64(opt, memarg) => {
                let bit_width = match opt {
                    None => 64,
                    Some(StoreI64Opt::L8) => 8,
                    Some(StoreI64Opt::L16) => 16,
                    Some(StoreI64Opt::L32) => 32,
                };
                self.validate_instr_helper_store(memarg, bit_width, I64, type_stack)?;
            }
            StoreF32(memarg) => {
                self.validate_instr_helper_store(memarg, 32, F32, type_stack)?;
            }
            StoreF64(memarg) => {
                self.validate_instr_helper_store(memarg, 64, F64, type_stack)?;
            }
            MemoryGrow => {
                if self.mems.len() < 1 {
                    unimplemented!() // @todo
                }
                self.validate_memtype(&self.mems[0])?;
                type_stack.consume(Type(I32))?;
                type_stack.produce(Type(I32));
            }
            MemorySize => {
                if self.mems.len() < 1 {
                    unimplemented!() // @todo
                }
                self.validate_memtype(&self.mems[0])?;
                type_stack.produce(Type(I32));
            }

            Nop => (),
            Unreachable => type_stack.produce(Polymorphic),
            Block(blocktype, instr_seq) => {
                let functype = self.validate_blocktype(blocktype)?;
                self.labels.push_front(functype.return_type().clone());
                self.validate_instr_seq(instr_seq, functype.param_type(), functype.return_type())?;
                self.labels.pop_front();

                for t in functype.param_type().iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                for t in functype.return_type().iter() {
                    type_stack.produce(Type(t.clone()));
                }
            }
            Loop(blocktype, instr_seq) => {
                let functype = self.validate_blocktype(blocktype)?;
                self.labels.push_front(functype.param_type().clone());
                self.validate_instr_seq(instr_seq, functype.param_type(), functype.return_type())?;
                self.labels.pop_front();

                for t in functype.param_type().iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                for t in functype.return_type().iter() {
                    type_stack.produce(Type(t.clone()));
                }
            }
            If(blocktype, then_instr_seq, else_instr_seq) => {
                let functype = self.validate_blocktype(blocktype)?;
                self.labels.push_front(functype.return_type().clone());
                self.validate_instr_seq(
                    then_instr_seq,
                    functype.param_type(),
                    functype.return_type(),
                )?;
                assert_eq!(self.labels.front(), Some(functype.return_type()));
                self.validate_instr_seq(
                    else_instr_seq,
                    functype.param_type(),
                    functype.return_type(),
                )?;
                self.labels.pop_front();

                type_stack.consume(Type(I32))?;
                for t in functype.param_type().iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                for t in functype.return_type().iter() {
                    type_stack.produce(Type(t.clone()));
                }
            }
            Br(labelidx) => {
                let i = labelidx.to_usize();
                if i >= self.labels.len() {
                    unimplemented!() // @todo
                }
                let resulttype = &self.labels[i];
                for t in resulttype.iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                type_stack.produce(Polymorphic);
            }
            BrIf(labelidx) => {
                let i = labelidx.to_usize();
                if i >= self.labels.len() {
                    unimplemented!() // @todo
                }
                let resulttype = &self.labels[i];
                type_stack.consume(Type(I32))?;
                for t in resulttype.iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                for t in resulttype.iter() {
                    type_stack.produce(Type(t.clone()));
                }
            }
            BrTable(labelidxes, default_labelidx) => {
                if default_labelidx.to_usize() >= self.labels.len() {
                    unimplemented!() // @todo
                }
                let resulttype = &self.labels[default_labelidx.to_usize()];
                for labelidx in labelidxes {
                    let i = labelidx.to_usize();
                    if i >= self.labels.len() {
                        unimplemented!() // @todo
                    }
                    if &self.labels[i] != resulttype {
                        unimplemented!() // @todo
                    }
                }
                type_stack.consume(Type(I32))?;
                for t in resulttype.iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                type_stack.produce(Polymorphic);
            }
            Return => {
                let return_type = self.return_type.as_ref().unwrap();
                for t in return_type.iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                type_stack.produce(Polymorphic);
            }
            Call(funcidx) => {
                if funcidx.to_usize() >= self.funcs.len() {
                    unimplemented!()
                }
                let functype = &self.funcs[funcidx.to_usize()];
                for t in functype.param_type().iter().rev() {
                    type_stack.consume(Type(t.clone()))?;
                }
                for t in functype.return_type().iter().rev() {
                    type_stack.produce(Type(t.clone()));
                }
            }

            _ => unimplemented!(),
        }
        Ok(())
    }

    fn validate_instr_helper_single_op(
        &self,
        produced_type: Valtype,
        consumed_type: Valtype,
        type_stack: &mut TypeStack,
    ) -> Result<(), ValidationError> {
        type_stack.consume(TypeStackEntry::Type(consumed_type))?;
        type_stack.produce(TypeStackEntry::Type(produced_type));
        Ok(())
    }

    fn validate_instr_helper_double_op(
        &self,
        produced_type: Valtype,
        consumed_type: Valtype,
        type_stack: &mut TypeStack,
    ) -> Result<(), ValidationError> {
        type_stack.consume(TypeStackEntry::Type(consumed_type.clone()))?;
        type_stack.consume(TypeStackEntry::Type(consumed_type))?;
        type_stack.produce(TypeStackEntry::Type(produced_type));
        Ok(())
    }

    fn validate_instr_helper_load(
        &self,
        memarg: &Memarg,
        bit_width: u32,
        valtype: Valtype,
        type_stack: &mut TypeStack,
    ) -> Result<(), ValidationError> {
        if self.mems.len() < 1 {
            unimplemented!() // @todo
        }
        self.validate_memtype(&self.mems[0])?;
        if 2u32.saturating_pow(memarg.align()) > bit_width / 8 {
            unimplemented!() // @todo
        }
        type_stack.consume(TypeStackEntry::Type(Valtype::I32))?;
        type_stack.produce(TypeStackEntry::Type(valtype));
        Ok(())
    }

    fn validate_instr_helper_store(
        &self,
        memarg: &Memarg,
        bit_width: u32,
        valtype: Valtype,
        type_stack: &mut TypeStack,
    ) -> Result<(), ValidationError> {
        if self.mems.len() < 1 {
            unimplemented!() // @todo
        }
        self.validate_memtype(&self.mems[0])?;
        if 2u32.saturating_pow(memarg.align()) > bit_width / 8 {
            unimplemented!() // @todo
        }
        type_stack.consume(TypeStackEntry::Type(valtype))?;
        type_stack.consume(TypeStackEntry::Type(Valtype::I32))?;
        Ok(())
    }

    fn validate_instr_seq(
        &mut self,
        instr_seq: &InstrSeq,
        param_type: &Resulttype,
        return_type: &Resulttype,
    ) -> Result<(), ValidationError> {
        let mut type_stack = TypeStack::new();
        for t in param_type.iter().rev() {
            type_stack.produce(TypeStackEntry::Type(t.clone()));
        }
        for instr in instr_seq.instr_seq().iter() {
            self.validate_instr(instr, &mut type_stack)?;
        }
        for t_r in return_type.iter().rev() {
            type_stack.consume(TypeStackEntry::Type(t_r.clone()))?;
        }
        if type_stack.is_empty() {
            Ok(())
        } else {
            unimplemented!() // @todo
        }
    }

    fn validate_expr(
        &mut self,
        expr: &Expr,
        resulttype: &Resulttype,
    ) -> Result<(), ValidationError> {
        let param_resulttype = Resulttype::new(vec![]);
        self.validate_instr_seq(expr.instr_seq(), &param_resulttype, &resulttype)
    }

    fn validate_func(&mut self, func: &Func) -> Result<(), ValidationError> {
        let typ = self.types[func.typ().to_usize()].make_clone();
        self.validate_functype(&typ)?;

        self.locals = typ.param_type().to_vec();
        self.locals.append(&mut func.locals().clone());
        self.labels = VecDeque::new();
        self.labels.push_back(typ.return_type().clone());
        self.return_type = Some(typ.return_type().clone());

        self.validate_expr(func.body(), typ.return_type())?;

        self.locals = Vec::new();
        self.labels = VecDeque::new();
        self.return_type = None;

        Ok(())
    }

    fn validate_memtype(&self, memtype: &Memtype) -> Result<(), ValidationError> {
        self.validate_limit(memtype.limit(), 2usize.pow(16))
    }

    fn validate_mem(&self, mem: &Mem) -> Result<(), ValidationError> {
        self.validate_memtype(mem.typ())
    }

    fn validate_module(&mut self, module: &Module) -> Result<(), ValidationError> {
        let types = module
            .types()
            .iter()
            .map(|functype| functype.make_clone())
            .collect();
        let funcs = module
            .funcs()
            .iter()
            .map(|func| module.types()[func.typ().to_usize()].make_clone())
            .collect();
        let mems: Vec<Memtype> = module.mems().iter().map(|mem| mem.typ().clone()).collect();
        let globals: Vec<Globaltype> = module
            .globals()
            .iter()
            .map(|global| global.typ().clone())
            .collect();

        if mems.len() > 1 {
            return Err(ValidationError::Module(format!(
                "size of mems in module ({}) must be less or equal to 1",
                mems.len()
            )));
        }

        self.types = types;
        self.funcs = funcs;
        self.mems = mems;
        self.globals = globals;

        for functype in module.types() {
            self.validate_functype(functype)?;
        }

        for func in module.funcs() {
            self.validate_func(func)?;
        }

        for mem in module.mems() {
            self.validate_mem(mem)?;
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ValidationError {
    Limit(String),
    Module(String),
}

pub fn validate(module: &Module) -> Result<(), ValidationError> {
    let mut context = TypeContext::new();
    context.validate_module(module)
}
