use std::rc::Rc;

use crate::module::*;
use crate::types::*;

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
pub enum TestopKind {
    Eqz,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelopKind {
    Eq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CvtopKind {
    I32Extend8S,
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
    UnopI32(IUnopKind),
    UnopI64(IUnopKind),
    BinopI32(IBinopKind),
    TestopI32(TestopKind),
    RelopI32(RelopKind),
    Cvtop(CvtopKind),

    Drop,
    Select,

    GetLocal(Localidx),
    SetLocal(Localidx),
    TeeLocal(Localidx),
    GetGlobal(Globalidx),
    SetGlobal(Globalidx),

    LoadI32(Memarg),
    StoreI32(Memarg),
    Grow,

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
