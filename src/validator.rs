use crate::instr::*;
use crate::module::*;
use crate::types::*;

struct TypeContext {
    types: Vec<Functype>,
    funcs: Vec<Functype>,
    mems: Vec<Memtype>,
    globals: Vec<Globaltype>,
    locals: Vec<Valtype>,
    labels: Vec<Resulttype>,
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
            labels: Vec::new(),
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

    fn validate_functype(&self, _functype: &Functype) -> Result<(), ValidationError> {
        Ok(())
    }

    fn validate_instr(
        &mut self,
        instr: &Instr,
        type_stack: &mut Vec<Valtype>,
    ) -> Result<(), ValidationError> {
        use InstrKind::*;
        use Valtype::*;
        let len = type_stack.len();
        match &instr.kind {
            ConstI32(_) => type_stack.push(I32),
            ConstI64(_) => type_stack.push(I64),
            ConstF32(_) => type_stack.push(F32),
            ConstF64(_) => type_stack.push(F64),

            UnopI32(_) if type_stack.last() == Some(&I32) => (),
            UnopI64(_) if type_stack.last() == Some(&I64) => (),
            UnopF32(_) if type_stack.last() == Some(&F32) => (),
            UnopF64(_) if type_stack.last() == Some(&F64) => (),

            Extend(kind) => match kind {
                ExtendKind::I32As8S if type_stack.last() == Some(&I32) => (),
                ExtendKind::I32As16S if type_stack.last() == Some(&I32) => (),
                ExtendKind::I64As8S if type_stack.last() == Some(&I64) => (),
                ExtendKind::I64As16S if type_stack.last() == Some(&I64) => (),
                ExtendKind::I64As32S if type_stack.last() == Some(&I64) => (),
                _ => unimplemented!(), // @todo
            },

            BinopI32(_) if len >= 2 && type_stack[len - 1] == I32 && type_stack[len - 2] == I32 => {
                type_stack.pop();
            }
            BinopI64(_) if len >= 2 && type_stack[len - 1] == I64 && type_stack[len - 2] == I64 => {
                type_stack.pop();
            }
            BinopF32(_) if len >= 2 && type_stack[len - 1] == F32 && type_stack[len - 2] == F32 => {
                type_stack.pop();
            }
            BinopF64(_) if len >= 2 && type_stack[len - 1] == F64 && type_stack[len - 2] == F64 => {
                type_stack.pop();
            }

            TestopI32(_) if type_stack.last() == Some(&I32) => {
                type_stack.pop();
                type_stack.push(I32);
            }
            TestopI64(_) if type_stack.last() == Some(&I64) => {
                type_stack.pop();
                type_stack.push(I64);
            }

            RelopI32(_) if len >= 2 && type_stack[len - 1] == I32 && type_stack[len - 2] == I32 => {
                type_stack.pop();
                type_stack.pop();
                type_stack.push(I32);
            }
            RelopI64(_) if len >= 2 && type_stack[len - 1] == I64 && type_stack[len - 2] == I64 => {
                type_stack.pop();
                type_stack.pop();
                type_stack.push(I32);
            }
            RelopF32(_) if len >= 2 && type_stack[len - 1] == F32 && type_stack[len - 2] == F32 => {
                type_stack.pop();
                type_stack.pop();
                type_stack.push(I32);
            }
            RelopF64(_) if len >= 2 && type_stack[len - 1] == F64 && type_stack[len - 2] == F64 => {
                type_stack.pop();
                type_stack.pop();
                type_stack.push(I32);
            }
            Cvtop(ref op) => match op {
                CvtopKind::I32WrapI64 if type_stack.last() == Some(&I64) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I64ExtendI32S if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64ExtendI32U if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I32TruncF32S if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I32TruncF32U if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I32TruncF64S if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I32TruncF64U if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I64TruncF32S if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64TruncF32U if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64TruncF64S if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64TruncF64U if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I32TruncSatF32S if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I32TruncSatF32U if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I32TruncSatF64S if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I32TruncSatF64U if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I64TruncSatF32S if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64TruncSatF32U if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64TruncSatF64S if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::I64TruncSatF64U if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::F32ConvertI32S if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(F32);
                }
                CvtopKind::F32ConvertI32U if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(F32);
                }
                CvtopKind::F32ConvertI64S if type_stack.last() == Some(&I64) => {
                    type_stack.pop();
                    type_stack.push(F32);
                }
                CvtopKind::F32ConvertI64U if type_stack.last() == Some(&I64) => {
                    type_stack.pop();
                    type_stack.push(F32);
                }
                CvtopKind::F64ConvertI32S if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(F64);
                }
                CvtopKind::F64ConvertI32U if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(F64);
                }
                CvtopKind::F64ConvertI64S if type_stack.last() == Some(&I64) => {
                    type_stack.pop();
                    type_stack.push(F64);
                }
                CvtopKind::F64ConvertI64U if type_stack.last() == Some(&I64) => {
                    type_stack.pop();
                    type_stack.push(F64);
                }
                CvtopKind::F32DemoteF64 if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(F32);
                }
                CvtopKind::F64PromoteF32 if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(F64);
                }
                CvtopKind::I32ReinterpretF32 if type_stack.last() == Some(&F32) => {
                    type_stack.pop();
                    type_stack.push(I32);
                }
                CvtopKind::I64ReinterpretF64 if type_stack.last() == Some(&F64) => {
                    type_stack.pop();
                    type_stack.push(I64);
                }
                CvtopKind::F32ReinterpretI32 if type_stack.last() == Some(&I32) => {
                    type_stack.pop();
                    type_stack.push(F32);
                }
                CvtopKind::F64ReinterpretI64 if type_stack.last() == Some(&I64) => {
                    type_stack.pop();
                    type_stack.push(F64);
                }
                _ => unimplemented!(), // @todo
            },

            Drop if len >= 1 => {
                type_stack.pop();
            }
            Select
                if len >= 3
                    && type_stack[len - 1] == I32
                    && type_stack[len - 2] == type_stack[len - 3] =>
            {
                type_stack.pop();
                let t = type_stack.pop().unwrap();
                type_stack.pop();
                type_stack.push(t);
            }

            GetLocal(idx) if idx.to_usize() < self.locals.len() => {
                let t = self.locals[idx.to_usize()].clone();
                type_stack.push(t);
            }
            SetLocal(idx)
                if idx.to_usize() < self.locals.len()
                    && type_stack.last() == Some(&self.locals[idx.to_usize()]) =>
            {
                type_stack.pop();
            }
            TeeLocal(idx)
                if idx.to_usize() < self.locals.len()
                    && type_stack.last() == Some(&self.locals[idx.to_usize()]) =>
            {
                ()
            }
            GetGlobal(idx) if idx.to_usize() < self.globals.len() => {
                let t = self.globals[idx.to_usize()].typ().clone();
                type_stack.push(t);
            }
            SetGlobal(idx)
                if idx.to_usize() < self.globals.len()
                    && type_stack.last() == Some(self.globals[idx.to_usize()].typ())
                    && self.globals[idx.to_usize()].mutability() == &Mutability::Var =>
            {
                type_stack.pop();
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
                if type_stack.last() != Some(&I32) {
                    unimplemented!() // @todo
                }
            }
            MemorySize => {
                if self.mems.len() < 1 {
                    unimplemented!() // @todo
                }
                self.validate_memtype(&self.mems[0])?;
                type_stack.push(I32);
            }

            Nop => (),
            Unreachable => (),
            _ => unimplemented!(),
        }
        Ok(())
    }

    fn validate_instr_helper_load(
        &self,
        memarg: &Memarg,
        bit_width: u32,
        valtype: Valtype,
        type_stack: &mut Vec<Valtype>,
    ) -> Result<(), ValidationError> {
        if type_stack.last() != Some(&Valtype::I32) {
            unimplemented!() // @todo
        }
        if self.mems.len() < 1 {
            unimplemented!() // @todo
        }
        self.validate_memtype(&self.mems[0])?;
        if 2u32.saturating_pow(memarg.align()) > bit_width / 8 {
            unimplemented!() // @todo
        }
        type_stack.pop();
        type_stack.push(valtype);
        Ok(())
    }

    fn validate_instr_helper_store(
        &self,
        memarg: &Memarg,
        bit_width: u32,
        valtype: Valtype,
        type_stack: &mut Vec<Valtype>,
    ) -> Result<(), ValidationError> {
        let len = type_stack.len();
        if len < 2 {
            unimplemented!() // @todo
        }
        if type_stack[len - 2] != Valtype::I32 {
            unimplemented!() // @todo
        }
        if type_stack[len - 1] != valtype {
            unimplemented!() // @todo
        }
        if self.mems.len() < 1 {
            unimplemented!() // @todo
        }
        self.validate_memtype(&self.mems[0])?;
        if 2u32.saturating_pow(memarg.align()) > bit_width / 8 {
            unimplemented!() // @todo
        }
        type_stack.pop();
        type_stack.pop();
        Ok(())
    }

    fn validate_expr(
        &mut self,
        expr: &Expr,
        resulttype: &Resulttype,
    ) -> Result<(), ValidationError> {
        let mut type_stack: Vec<Valtype> = Vec::new();
        for instr in expr.instr_seq().instr_seq().iter() {
            self.validate_instr(instr, &mut type_stack)?;
        }
        let resulttype: Vec<Valtype> = resulttype.iter().map(|t| t.clone()).collect();
        if type_stack == resulttype {
            Ok(())
        } else {
            unimplemented!()
        }
    }

    fn validate_func(&mut self, func: &Func) -> Result<(), ValidationError> {
        let typ = self.types[func.typ().to_usize()].make_clone();
        self.validate_functype(&typ)?;

        self.locals = typ.param_type().to_vec();
        self.locals.append(&mut func.locals().clone());
        self.labels = vec![typ.return_type().clone()];
        self.return_type = Some(typ.return_type().clone());

        self.validate_expr(func.body(), typ.return_type())?;

        self.locals = Vec::new();
        self.labels = Vec::new();
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

        if mems.len() > 1 {
            return Err(ValidationError::Module(format!(
                "size of mems in module ({}) must be less or equal to 1",
                mems.len()
            )));
        }

        self.types = types;
        self.funcs = funcs;
        self.mems = mems;

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
