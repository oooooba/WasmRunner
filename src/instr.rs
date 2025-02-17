use std::rc::Rc;

use crate::module::*;
use crate::types::*;
use crate::value::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Blocktype {
    Empty,
    Valtype(Valtype),
    S33(Typeidx),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IUnopKind {
    Clz,
    Ctz,
    Popcnt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IBinopKind {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Rotl,
    Rotr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FUnopKind {
    Abs,
    Neg,
    Ceil,
    Floor,
    Trunc,
    Nearest,
    Sqrt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExtendKind {
    I32As8S,
    I32As16S,
    I64As8S,
    I64As16S,
    I64As32S,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FBinopKind {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
    Copysign,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TestopKind {
    Eqz,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IRelopKind {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FRelopKind {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CvtopKind {
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F32DemoteF64,
    F64PromoteF32,
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LoadI32Opt {
    S8,
    U8,
    S16,
    U16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LoadI64Opt {
    S8,
    U8,
    S16,
    U16,
    S32,
    U32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StoreI32Opt {
    L8,
    L16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StoreI64Opt {
    L8,
    L16,
    L32,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Memarg {
    offset: u32,
    align: u32,
}

impl Memarg {
    pub fn new(offset: u32, align: u32) -> Self {
        Self { offset, align }
    }

    pub fn offset(&self) -> u32 {
        self.offset
    }

    pub fn align(&self) -> u32 {
        self.align
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TerminatorKind {
    End,
    Else,
}

#[derive(Debug, PartialEq, Eq)]
pub enum InstrKind {
    ConstI32(u32),
    ConstI64(u64),
    ConstF32(F32Bytes),
    ConstF64(F64Bytes),
    UnopI32(IUnopKind),
    UnopI64(IUnopKind),
    UnopF32(FUnopKind),
    UnopF64(FUnopKind),
    Extend(ExtendKind),
    BinopI32(IBinopKind),
    BinopI64(IBinopKind),
    BinopF32(FBinopKind),
    BinopF64(FBinopKind),
    TestopI32(TestopKind),
    TestopI64(TestopKind),
    RelopI32(IRelopKind),
    RelopI64(IRelopKind),
    RelopF32(FRelopKind),
    RelopF64(FRelopKind),
    Cvtop(CvtopKind),

    Drop,
    Select,

    GetLocal(Localidx),
    SetLocal(Localidx),
    TeeLocal(Localidx),
    GetGlobal(Globalidx),
    SetGlobal(Globalidx),

    LoadI32(Option<LoadI32Opt>, Memarg),
    LoadI64(Option<LoadI64Opt>, Memarg),
    LoadF32(Memarg),
    LoadF64(Memarg),
    StoreI32(Option<StoreI32Opt>, Memarg),
    StoreI64(Option<StoreI64Opt>, Memarg),
    StoreF32(Memarg),
    StoreF64(Memarg),
    MemoryGrow,
    MemorySize,

    Nop,
    Unreachable,
    Block(Blocktype, InstrSeq),
    Loop(Blocktype, InstrSeq),
    If(Blocktype, InstrSeq, InstrSeq),
    Br(Labelidx),
    BrIf(Labelidx),
    BrTable(Vec<Labelidx>, Labelidx),
    Return,
    Call(Funcidx),
    CallIndirect(Typeidx),

    Terminator(TerminatorKind),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Instr {
    pub kind: InstrKind,
}

impl Instr {
    pub fn new(kind: InstrKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct InstrSeqInner {
    instr_seq: Vec<Instr>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct InstrSeq(Rc<InstrSeqInner>);

impl InstrSeq {
    pub fn new(instr_seq: Vec<Instr>) -> Self {
        Self(Rc::new(InstrSeqInner { instr_seq }))
    }

    pub fn new_empty() -> Self {
        Self::new(Vec::new())
    }

    pub fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }

    pub fn instr_seq(&self) -> &Vec<Instr> {
        &self.0.instr_seq
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    instr_seq: InstrSeq,
}

impl Expr {
    pub fn new(instr_seq: InstrSeq) -> Self {
        Self { instr_seq }
    }

    pub fn make_clone(&self) -> Self {
        Self::new(self.instr_seq.make_clone())
    }

    pub fn instr_seq(&self) -> &InstrSeq {
        &self.instr_seq
    }
}
