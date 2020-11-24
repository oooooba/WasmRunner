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

    fn consume(&mut self, entry: TypeStackEntry) -> Option<TypeStackEntry> {
        use TypeStackEntry::*;
        match (self.stack.pop(), entry) {
            (_, Polymorphic) => panic!(),

            (Some(Type(valtype_s)), Type(valtype_e)) if valtype_s == valtype_e => {
                Some(Type(valtype_s))
            }
            (Some(Type(_)), Type(_)) => None,
            (Some(Type(valtype_s)), AnyType) => Some(Type(valtype_s)),

            (Some(AnyType), Type(valtype_e)) => Some(Type(valtype_e)),
            (Some(AnyType), AnyType) => Some(AnyType),

            (Some(Polymorphic), Type(valtype_e)) => {
                assert!(self.stack.is_empty());
                self.stack.push(Polymorphic);
                Some(Type(valtype_e))
            }
            (Some(Polymorphic), AnyType) => {
                assert!(self.stack.is_empty());
                self.stack.push(Polymorphic);
                Some(AnyType)
            }

            (None, _) => None,
        }
    }

    fn is_empty(&self) -> bool {
        match self.stack.last() {
            Some(TypeStackEntry::Polymorphic) => {
                assert_eq!(self.stack.len(), 1);
                true
            }
            None => true,
            _ => false,
        }
    }
}

fn produce(type_stack: &mut TypeStack, entry: TypeStackEntry) {
    type_stack.produce(entry);
}

fn produce_with_resulttype(type_stack: &mut TypeStack, resulttype: &Resulttype) {
    for t in resulttype.iter() {
        produce(type_stack, TypeStackEntry::Type(t.clone()));
    }
}

fn consume(
    type_stack: &mut TypeStack,
    entry: TypeStackEntry,
) -> Result<TypeStackEntry, ValidationError> {
    type_stack
        .consume(entry)
        .ok_or(ValidationError::TypeMismatch)
}

fn consume_with_resulttype(
    type_stack: &mut TypeStack,
    resulttype: &Resulttype,
) -> Result<(), ValidationError> {
    for t in resulttype.iter().rev() {
        consume(type_stack, TypeStackEntry::Type(t.clone()))?;
    }
    Ok(())
}

struct TypeContext {
    types: Vec<Functype>,
    funcs: Vec<Functype>,
    tables: Vec<Tabletype>,
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
            tables: Vec::new(),
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

    fn validate_tabletype(&self, tabletype: &Tabletype) -> Result<(), ValidationError> {
        self.validate_limit(tabletype.limit(), 1usize << 32)
    }

    fn validate_memtype(&self, memtype: &Memtype) -> Result<(), ValidationError> {
        self.validate_limit(memtype.limit(), 2usize.pow(16))
    }

    fn validate_globaltype(&self, _globaltype: &Globaltype) -> Result<(), ValidationError> {
        Ok(())
    }

    fn validate_elem(&mut self, elem: &Elem) -> Result<(), ValidationError> {
        if elem.table().to_usize() >= self.tables.len() {
            unimplemented!()
        }

        if self.tables[elem.table().to_usize()].elemtype() != &Elemtype::Funcref {
            unimplemented!()
        }

        self.validate_expr(elem.offset(), &Resulttype::new(vec![Valtype::I32]))?;
        self.validate_const_expr(elem.offset())?;

        for funcidx in elem.init() {
            if funcidx.to_usize() >= self.funcs.len() {
                unimplemented!()
            }
        }

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
            ConstI32(_) => produce(type_stack, Type(I32)),
            ConstI64(_) => produce(type_stack, Type(I64)),
            ConstF32(_) => produce(type_stack, Type(F32)),
            ConstF64(_) => produce(type_stack, Type(F64)),

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
                consume(type_stack, AnyType)?;
            }
            Select => {
                consume(type_stack, Type(I32))?;
                let t1 = consume(type_stack, AnyType)?;
                let t2 = consume(type_stack, AnyType)?;
                if !(t1 == AnyType || t2 == AnyType || t1 == t2) {
                    unimplemented!() // @todo
                }
                produce(type_stack, t1)
            }

            GetLocal(idx) => {
                if idx.to_usize() >= self.locals.len() {
                    unimplemented!()
                }
                produce(type_stack, Type(self.locals[idx.to_usize()].clone()));
            }
            SetLocal(idx) => {
                if idx.to_usize() >= self.locals.len() {
                    unimplemented!()
                }
                consume(type_stack, Type(self.locals[idx.to_usize()].clone()))?;
            }
            TeeLocal(idx) => {
                if idx.to_usize() >= self.locals.len() {
                    unimplemented!()
                }
                let t = self.locals[idx.to_usize()].clone();
                consume(type_stack, Type(t.clone()))?;
                produce(type_stack, Type(t));
            }
            GetGlobal(idx) => {
                if idx.to_usize() >= self.globals.len() {
                    unimplemented!()
                }
                produce(type_stack, Type(self.globals[idx.to_usize()].typ().clone()));
            }
            SetGlobal(idx) => {
                if idx.to_usize() >= self.globals.len() {
                    unimplemented!()
                }
                if self.globals[idx.to_usize()].mutability() != &Mutability::Var {
                    unimplemented!()
                }
                consume(type_stack, Type(self.globals[idx.to_usize()].typ().clone()))?;
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
                consume(type_stack, Type(I32))?;
                produce(type_stack, Type(I32));
            }
            MemorySize => {
                if self.mems.len() < 1 {
                    unimplemented!() // @todo
                }
                self.validate_memtype(&self.mems[0])?;
                produce(type_stack, Type(I32));
            }

            Nop => (),
            Unreachable => produce(type_stack, Polymorphic),
            Block(blocktype, instr_seq) => {
                let functype = self.validate_blocktype(blocktype)?;
                self.labels.push_front(functype.return_type().clone());
                self.validate_instr_seq(instr_seq, functype.param_type(), functype.return_type())?;
                self.labels.pop_front();
                consume_with_resulttype(type_stack, functype.param_type())?;
                produce_with_resulttype(type_stack, functype.return_type());
            }
            Loop(blocktype, instr_seq) => {
                let functype = self.validate_blocktype(blocktype)?;
                self.labels.push_front(functype.param_type().clone());
                self.validate_instr_seq(instr_seq, functype.param_type(), functype.return_type())?;
                self.labels.pop_front();
                consume_with_resulttype(type_stack, functype.param_type())?;
                produce_with_resulttype(type_stack, functype.return_type());
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
                consume(type_stack, Type(I32))?;
                consume_with_resulttype(type_stack, functype.param_type())?;
                produce_with_resulttype(type_stack, functype.return_type());
            }
            Br(labelidx) => {
                let i = labelidx.to_usize();
                if i >= self.labels.len() {
                    unimplemented!() // @todo
                }
                let resulttype = &self.labels[i];
                consume_with_resulttype(type_stack, resulttype)?;
                produce(type_stack, Polymorphic);
            }
            BrIf(labelidx) => {
                let i = labelidx.to_usize();
                if i >= self.labels.len() {
                    unimplemented!() // @todo
                }
                let resulttype = &self.labels[i];
                consume(type_stack, Type(I32))?;
                consume_with_resulttype(type_stack, resulttype)?;
                produce_with_resulttype(type_stack, resulttype);
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
                        return Err(ValidationError::TypeMismatch);
                    }
                }
                consume(type_stack, Type(I32))?;
                consume_with_resulttype(type_stack, resulttype)?;
                produce(type_stack, Polymorphic);
            }
            Return => {
                let return_type = self.return_type.as_ref().unwrap();
                consume_with_resulttype(type_stack, return_type)?;
                produce(type_stack, Polymorphic);
            }
            Call(funcidx) => {
                if funcidx.to_usize() >= self.funcs.len() {
                    unimplemented!()
                }
                let functype = &self.funcs[funcidx.to_usize()];
                consume_with_resulttype(type_stack, functype.param_type())?;
                produce_with_resulttype(type_stack, functype.return_type());
            }
            CallIndirect(funcidx) => {
                if self.tables.len() < 1 {
                    unimplemented!() // @todo
                }
                if self.tables[0].elemtype() != &Elemtype::Funcref {
                    unimplemented!() // @todo
                }
                if funcidx.to_usize() >= self.types.len() {
                    unimplemented!()
                }
                let functype = &self.types[funcidx.to_usize()];
                consume(type_stack, Type(I32))?;
                consume_with_resulttype(type_stack, functype.param_type())?;
                produce_with_resulttype(type_stack, functype.return_type());
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
        consume(type_stack, TypeStackEntry::Type(consumed_type))?;
        produce(type_stack, TypeStackEntry::Type(produced_type));
        Ok(())
    }

    fn validate_instr_helper_double_op(
        &self,
        produced_type: Valtype,
        consumed_type: Valtype,
        type_stack: &mut TypeStack,
    ) -> Result<(), ValidationError> {
        consume(type_stack, TypeStackEntry::Type(consumed_type.clone()))?;
        consume(type_stack, TypeStackEntry::Type(consumed_type))?;
        produce(type_stack, TypeStackEntry::Type(produced_type));
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
            return Err(ValidationError::MemoryAccessAlignmentViolation);
        }
        consume(type_stack, TypeStackEntry::Type(Valtype::I32))?;
        produce(type_stack, TypeStackEntry::Type(valtype));
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
            return Err(ValidationError::MemoryAccessAlignmentViolation);
        }
        consume(type_stack, TypeStackEntry::Type(valtype))?;
        consume(type_stack, TypeStackEntry::Type(Valtype::I32))?;
        Ok(())
    }

    fn validate_instr_seq(
        &mut self,
        instr_seq: &InstrSeq,
        param_type: &Resulttype,
        return_type: &Resulttype,
    ) -> Result<(), ValidationError> {
        let mut type_stack = TypeStack::new();
        produce_with_resulttype(&mut type_stack, param_type);
        for instr in instr_seq.instr_seq().iter() {
            self.validate_instr(instr, &mut type_stack)?;
        }
        consume_with_resulttype(&mut type_stack, return_type)?;
        if type_stack.is_empty() {
            Ok(())
        } else {
            Err(ValidationError::TypeMismatch)
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

    fn validate_const_expr(&self, expr: &Expr) -> Result<(), ValidationError> {
        use InstrKind::*;
        for instr in expr.instr_seq().instr_seq().iter() {
            match &instr.kind {
                ConstI32(_) => (),
                ConstI64(_) => (),
                ConstF32(_) => (),
                ConstF64(_) => (),
                GetGlobal(idx) => {
                    if idx.to_usize() >= self.globals.len() {
                        unimplemented!()
                    }
                    if self.globals[idx.to_usize()].mutability() != &Mutability::Const {
                        unimplemented!()
                    }
                }
                _ => unimplemented!(),
            }
        }
        Ok(())
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

    fn validate_table(&self, table: &Table) -> Result<(), ValidationError> {
        self.validate_tabletype(table.typ())
    }

    fn validate_mem(&self, mem: &Mem) -> Result<(), ValidationError> {
        self.validate_memtype(mem.typ())
    }

    fn validate_global(&mut self, global: &Global) -> Result<(), ValidationError> {
        self.validate_globaltype(global.typ())?;
        self.validate_expr(
            global.init(),
            &Resulttype::new(vec![global.typ().typ().clone()]),
        )?;
        self.validate_const_expr(global.init())
    }

    fn validate_import(&self, import: &Import) -> Result<(), ValidationError> {
        self.validate_importdesc(import.desc())
    }

    fn validate_importdesc(&self, importdesc: &Importdesc) -> Result<(), ValidationError> {
        use Importdesc::*;
        match importdesc {
            Func(typeidx) => {
                if typeidx.to_usize() >= self.types.len() {
                    unimplemented!()
                }
                self.validate_functype(&self.types[typeidx.to_usize()])
            }
            Table(tabletype) => self.validate_tabletype(tabletype),
            Mem(memtype) => self.validate_memtype(memtype),
            Global(globaltype) => self.validate_globaltype(globaltype),
        }
    }

    fn validate_module(&mut self, module: &Module) -> Result<(), ValidationError> {
        let types = module
            .types()
            .iter()
            .map(|functype| functype.make_clone())
            .collect();
        let mut funcs = module
            .funcs()
            .iter()
            .map(|func| module.types()[func.typ().to_usize()].make_clone())
            .collect();
        let mut tables: Vec<Tabletype> = module
            .tables()
            .iter()
            .map(|table| table.typ().clone())
            .collect();
        let mut mems: Vec<Memtype> = module.mems().iter().map(|mem| mem.typ().clone()).collect();
        let mut globals: Vec<Globaltype> = module
            .globals()
            .iter()
            .map(|global| global.typ().clone())
            .collect();

        if tables.len() > 1 {
            return Err(ValidationError::Module(format!(
                "size of tables in module ({}) must be less or equal to 1",
                tables.len()
            )));
        }

        if mems.len() > 1 {
            return Err(ValidationError::Module(format!(
                "size of mems in module ({}) must be less or equal to 1",
                mems.len()
            )));
        }

        self.types = types;

        for functype in module.types() {
            self.validate_functype(functype)?;
        }

        let (mut imported_funcs, mut imported_tables, mut imported_mems, mut imported_globals) =
            self.extract_imported_contents(module)?;
        imported_funcs.append(&mut funcs);
        imported_tables.append(&mut tables);
        imported_mems.append(&mut mems);
        imported_globals.append(&mut globals);

        self.funcs = imported_funcs;
        self.tables = imported_tables;
        self.mems = imported_mems;
        self.globals = imported_globals;

        for func in module.funcs() {
            self.validate_func(func)?;
        }

        for table in module.tables() {
            self.validate_table(table)?;
        }

        for mem in module.mems() {
            self.validate_mem(mem)?;
        }

        for global in module.globals() {
            self.validate_global(global)?;
        }

        for elem in module.elems() {
            self.validate_elem(elem)?;
        }

        for import in module.imports() {
            self.validate_import(import)?;
        }

        Ok(())
    }

    fn extract_imported_contents(
        &self,
        module: &Module,
    ) -> Result<(Vec<Functype>, Vec<Tabletype>, Vec<Memtype>, Vec<Globaltype>), ValidationError>
    {
        let mut functypes = Vec::new();
        let mut tabletypes = Vec::new();
        let mut memtypes = Vec::new();
        let mut globaltypes = Vec::new();
        for import in module.imports() {
            use Importdesc::*;
            match import.desc() {
                Func(typeidx) => {
                    if typeidx.to_usize() >= self.types.len() {
                        unimplemented!()
                    }
                    functypes.push(self.types[typeidx.to_usize()].make_clone());
                }
                Table(tabletype) => tabletypes.push(tabletype.clone()),
                Mem(memtype) => memtypes.push(memtype.clone()),
                Global(globaltype) => globaltypes.push(globaltype.clone()),
            }
        }
        Ok((functypes, tabletypes, memtypes, globaltypes))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ValidationError {
    Limit(String),
    Module(String),
    TypeMismatch,
    MemoryAccessAlignmentViolation,
}

pub fn validate(module: &Module) -> Result<(), ValidationError> {
    let mut context = TypeContext::new();
    context.validate_module(module)
}
