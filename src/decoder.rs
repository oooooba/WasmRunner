use std::collections::HashSet;
use std::fmt;
use std::io::Read;
use std::iter;

use crate::instr::*;
use crate::module::*;
use crate::types::*;
use crate::value::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SectionId {
    Custom,
    Type,
    Import,
    Function,
    Table,
    Memory,
    Global,
    Export,
    Start,
    Element,
    Code,
    Data,
}

#[derive(Debug, PartialEq, Eq)]
struct FuncCode {
    locals: Vec<Valtype>,
    body: Expr,
}

pub struct Decoder<'a, R: Read> {
    reader: &'a mut R,
    read_bytes: usize,
}

impl<'a, R: Read> Decoder<'a, R> {
    pub fn new(reader: &'a mut R) -> Self {
        Self {
            reader,
            read_bytes: 0,
        }
    }

    pub fn run(&mut self) -> Result<Module, DecodeError> {
        self.decode_module()
    }

    fn read(&mut self, buf: &mut [u8]) -> Result<(), DecodeError> {
        self.reader
            .read_exact(buf)
            .map_err(|_| DecodeError::UnexpectedEnd)?;
        self.read_bytes += buf.len();
        Ok(())
    }

    fn decode_vec<E>(
        &mut self,
        elem_decoder: fn(&mut Self) -> Result<E, DecodeError>,
    ) -> Result<Vec<E>, DecodeError> {
        let num = self.decode_u32()?;
        let mut result = Vec::with_capacity(num as usize);
        for _ in 0..num {
            let elem = elem_decoder(self)?;
            result.push(elem);
        }
        Ok(result)
    }

    fn decode_byte(&mut self) -> Result<u8, DecodeError> {
        let mut buf = [0; 1];
        self.read(&mut buf)?;
        Ok(buf[0])
    }

    fn decode_u32(&mut self) -> Result<u32, DecodeError> {
        let mut result = 0u64;
        for i in 0..5 {
            let mut buf = [0; 1];
            self.read(&mut buf)?;
            let b = buf[0] as u64;
            result |= (b & 0x7F) << (i * 7);
            if (b & 0x80) == 0 {
                if result <= (u32::MAX as u64) {
                    return Ok(result as u32);
                } else {
                    return Err(DecodeError::InvalidIntegerRange);
                }
            }
        }
        Err(DecodeError::InvalidIntegerRepresentation)
    }

    fn decode_s32(&mut self) -> Result<i32, DecodeError> {
        let max_len = 5;
        let mut read_size = 0;
        let mut result = 0u64;
        for i in 0..max_len {
            let mut buf = [0; 1];
            self.read(&mut buf)?;
            read_size += 1;
            let b = buf[0] as u64;
            result |= (b & 0x7F) << (i * 7);
            if (b & 0x80) == 0 {
                break;
            } else if read_size == max_len {
                return Err(DecodeError::InvalidIntegerRepresentation);
            }
        }
        let shift_width = 64 - 7 * read_size;
        let result = ((result << shift_width) as i64) >> shift_width;
        if !((i32::MIN as i64) <= result && result <= (i32::MAX as i64)) {
            return Err(DecodeError::InvalidIntegerRange);
        }
        Ok(result as i32)
    }

    fn decode_s64(&mut self) -> Result<i64, DecodeError> {
        let max_len = 10;
        let mut read_size = 0;
        let mut result = 0u128;
        for i in 0..max_len {
            let mut buf = [0; 1];
            self.read(&mut buf)?;
            read_size += 1;
            let b = buf[0] as u128;
            result |= (b & 0x7F) << (i * 7);
            if (b & 0x80) == 0 {
                break;
            } else if read_size == max_len {
                return Err(DecodeError::InvalidIntegerRepresentation);
            }
        }
        let shift_width = 128 - 7 * read_size;
        let result = ((result << shift_width) as i128) >> shift_width;
        if !((i64::MIN as i128) <= result && result <= (i64::MAX as i128)) {
            return Err(DecodeError::InvalidIntegerRange);
        }
        Ok(result as i64)
    }

    fn decode_f32(&mut self) -> Result<f32, DecodeError> {
        let mut buf = [0; 4];
        self.read(&mut buf)?;
        Ok(f32::from_le_bytes(buf))
    }

    fn decode_f64(&mut self) -> Result<f64, DecodeError> {
        let mut buf = [0; 8];
        self.read(&mut buf)?;
        Ok(f64::from_le_bytes(buf))
    }

    fn decode_name(&mut self) -> Result<Name, DecodeError> {
        let bytes = self.decode_vec(Self::decode_byte)?;
        let name = String::from_utf8(bytes)
            .map_err(|e| DecodeError::InvalidUtf8Sequence(e.to_string()))?;
        Ok(Name::new(name))
    }

    fn decode_valtype(&mut self) -> Result<Valtype, DecodeError> {
        let b = self.decode_byte()?;
        match b {
            0x7F => Ok(Valtype::I32),
            0x7E => Ok(Valtype::I64),
            0x7D => Ok(Valtype::F32),
            0x7C => Ok(Valtype::F64),
            _ => Err(DecodeError::UnknownValtype(b)),
        }
    }

    fn decode_resulttype(&mut self) -> Result<Resulttype, DecodeError> {
        Ok(Resulttype::new(self.decode_vec(Self::decode_valtype)?))
    }

    fn decode_functype(&mut self) -> Result<Functype, DecodeError> {
        let b = self.decode_byte()?;
        if b != 0x60 {
            return Err(DecodeError::UnknownFunctype(b));
        }
        let rt1 = self.decode_resulttype()?;
        let rt2 = self.decode_resulttype()?;
        Ok(Functype::new(rt1, rt2))
    }

    fn decode_limit(&mut self) -> Result<Limit, DecodeError> {
        let b = self.decode_byte()?;
        let (min, max) = match b {
            0 => (self.decode_u32()?, None),
            1 => {
                let n = self.decode_u32()?;
                let m = self.decode_u32()?;
                (n, Some(m))
            }
            _ if b < 0x80 => return Err(DecodeError::InvalidIntegerRange),
            _ => return Err(DecodeError::InvalidIntegerRepresentation),
        };
        Ok(Limit::new(min, max))
    }

    fn decode_memtype(&mut self) -> Result<Memtype, DecodeError> {
        let limit = self.decode_limit()?;
        Ok(Memtype::new(limit))
    }

    fn decode_tabletype(&mut self) -> Result<Tabletype, DecodeError> {
        let elemtype = self.decode_elemtype()?;
        let limit = self.decode_limit()?;
        Ok(Tabletype::new(limit, elemtype))
    }

    fn decode_elemtype(&mut self) -> Result<Elemtype, DecodeError> {
        let b = self.decode_byte()?;
        match b {
            0x70 => Ok(Elemtype::Funcref),
            _ => Err(DecodeError::UnknownElemtype(b)),
        }
    }

    fn decode_globaltype(&mut self) -> Result<Globaltype, DecodeError> {
        let valtype = self.decode_valtype()?;
        let mutability = self.decode_mut()?;
        Ok(Globaltype::new(valtype, mutability))
    }

    fn decode_mut(&mut self) -> Result<Mutability, DecodeError> {
        let b = self.decode_byte()?;
        match b {
            0x00 => Ok(Mutability::Const),
            0x01 => Ok(Mutability::Var),
            _ => Err(DecodeError::UnknownMut(b)),
        }
    }

    fn decode_until(
        &mut self,
        terminator_set: HashSet<TerminatorKind>,
    ) -> Result<(InstrSeq, TerminatorKind), DecodeError> {
        let mut instrs = Vec::new();
        loop {
            let instr = self.decode_instr()?;
            if let InstrKind::Terminator(terminator_kind) = instr.kind {
                if terminator_set.contains(&terminator_kind) {
                    return Ok((InstrSeq::new(instrs), terminator_kind));
                }
            }
            instrs.push(instr);
        }
    }

    fn decode_blocktype(&mut self) -> Result<Blocktype, DecodeError> {
        // @todo support S33
        let b = self.decode_byte()?;
        let blocktype = match b {
            0x40 => Blocktype::Empty,
            0x7F => Blocktype::Valtype(Valtype::I32),
            0x7E => Blocktype::Valtype(Valtype::I64),
            0x7D => Blocktype::Valtype(Valtype::F32),
            0x7C => Blocktype::Valtype(Valtype::F64),
            _ => Blocktype::S33(Typeidx::new(b.into())),
        };
        Ok(blocktype)
    }

    fn decode_memarg(&mut self) -> Result<Memarg, DecodeError> {
        let align = self.decode_u32()?;
        let offset = self.decode_u32()?;
        Ok(Memarg::new(offset, align))
    }

    fn decode_instr(&mut self) -> Result<Instr, DecodeError> {
        let b = self.decode_byte()?;
        use InstrKind::*;
        match b {
            0x00 => Ok(Instr::new(Unreachable)),
            0x01 => Ok(Instr::new(Nop)),
            0x02 => {
                let blocktype = self.decode_blocktype()?;
                let instr_seq = self
                    .decode_until([TerminatorKind::End].iter().cloned().collect())?
                    .0;
                Ok(Instr::new(Block(blocktype, instr_seq)))
            }
            0x03 => {
                let blocktype = self.decode_blocktype()?;
                let instr_seq = self
                    .decode_until([TerminatorKind::End].iter().cloned().collect())?
                    .0;
                Ok(Instr::new(Loop(blocktype, instr_seq)))
            }
            0x04 => {
                let blocktype = self.decode_blocktype()?;
                let (then_instr_seq, terminator_kind) = self.decode_until(
                    [TerminatorKind::End, TerminatorKind::Else]
                        .iter()
                        .cloned()
                        .collect(),
                )?;
                let else_instr_seq = match terminator_kind {
                    TerminatorKind::End => InstrSeq::new_empty(),
                    TerminatorKind::Else => {
                        self.decode_until([TerminatorKind::End].iter().cloned().collect())?
                            .0
                    }
                };
                Ok(Instr::new(If(blocktype, then_instr_seq, else_instr_seq)))
            }
            0x05 => Ok(Instr::new(Terminator(TerminatorKind::Else))),
            0x0B => Ok(Instr::new(Terminator(TerminatorKind::End))),
            0x0C => Ok(Instr::new(Br(self.decode_labelidx()?))),
            0x0D => Ok(Instr::new(BrIf(self.decode_labelidx()?))),
            0x0E => {
                let labelidxes = self.decode_vec(Self::decode_labelidx)?;
                let default_labelidx = self.decode_labelidx()?;
                Ok(Instr::new(BrTable(labelidxes, default_labelidx)))
            }
            0x0F => Ok(Instr::new(Return)),
            0x10 => Ok(Instr::new(Call(self.decode_funcidx()?))),
            0x11 => {
                let typeidx = self.decode_typeidx()?;
                let b = self.decode_byte()?;
                if b != 0 {
                    return Err(DecodeError::ZeroFlagExpected);
                }
                Ok(Instr::new(CallIndirect(typeidx)))
            }

            0x1A => Ok(Instr::new(Drop)),
            0x1B => Ok(Instr::new(Select)),

            0x20 => Ok(Instr::new(GetLocal(self.decode_localidx()?))),
            0x21 => Ok(Instr::new(SetLocal(self.decode_localidx()?))),
            0x22 => Ok(Instr::new(TeeLocal(self.decode_localidx()?))),
            0x23 => Ok(Instr::new(GetGlobal(self.decode_globalidx()?))),
            0x24 => Ok(Instr::new(SetGlobal(self.decode_globalidx()?))),

            0x28 => Ok(Instr::new(LoadI32(None, self.decode_memarg()?))),
            0x29 => Ok(Instr::new(LoadI64(None, self.decode_memarg()?))),
            0x2A => Ok(Instr::new(LoadF32(self.decode_memarg()?))),
            0x2B => Ok(Instr::new(LoadF64(self.decode_memarg()?))),
            0x2C => Ok(Instr::new(LoadI32(
                Some(LoadI32Opt::S8),
                self.decode_memarg()?,
            ))),
            0x2D => Ok(Instr::new(LoadI32(
                Some(LoadI32Opt::U8),
                self.decode_memarg()?,
            ))),
            0x2E => Ok(Instr::new(LoadI32(
                Some(LoadI32Opt::S16),
                self.decode_memarg()?,
            ))),
            0x2F => Ok(Instr::new(LoadI32(
                Some(LoadI32Opt::U16),
                self.decode_memarg()?,
            ))),
            0x30 => Ok(Instr::new(LoadI64(
                Some(LoadI64Opt::S8),
                self.decode_memarg()?,
            ))),
            0x31 => Ok(Instr::new(LoadI64(
                Some(LoadI64Opt::U8),
                self.decode_memarg()?,
            ))),
            0x32 => Ok(Instr::new(LoadI64(
                Some(LoadI64Opt::S16),
                self.decode_memarg()?,
            ))),
            0x33 => Ok(Instr::new(LoadI64(
                Some(LoadI64Opt::U16),
                self.decode_memarg()?,
            ))),
            0x34 => Ok(Instr::new(LoadI64(
                Some(LoadI64Opt::S32),
                self.decode_memarg()?,
            ))),
            0x35 => Ok(Instr::new(LoadI64(
                Some(LoadI64Opt::U32),
                self.decode_memarg()?,
            ))),
            0x36 => Ok(Instr::new(StoreI32(None, self.decode_memarg()?))),
            0x37 => Ok(Instr::new(StoreI64(None, self.decode_memarg()?))),
            0x38 => Ok(Instr::new(StoreF32(self.decode_memarg()?))),
            0x39 => Ok(Instr::new(StoreF64(self.decode_memarg()?))),
            0x3A => Ok(Instr::new(StoreI32(
                Some(StoreI32Opt::L8),
                self.decode_memarg()?,
            ))),
            0x3B => Ok(Instr::new(StoreI32(
                Some(StoreI32Opt::L16),
                self.decode_memarg()?,
            ))),
            0x3C => Ok(Instr::new(StoreI64(
                Some(StoreI64Opt::L8),
                self.decode_memarg()?,
            ))),
            0x3D => Ok(Instr::new(StoreI64(
                Some(StoreI64Opt::L16),
                self.decode_memarg()?,
            ))),
            0x3E => Ok(Instr::new(StoreI64(
                Some(StoreI64Opt::L32),
                self.decode_memarg()?,
            ))),
            0x3F => {
                let b = self.decode_byte()?;
                if b != 0 {
                    return Err(DecodeError::ZeroFlagExpected);
                }
                Ok(Instr::new(MemorySize))
            }
            0x40 => {
                let b = self.decode_byte()?;
                if b != 0 {
                    return Err(DecodeError::ZeroFlagExpected);
                }
                Ok(Instr::new(MemoryGrow))
            }

            0x41 => Ok(Instr::new(ConstI32(self.decode_s32()? as u32))),
            0x42 => Ok(Instr::new(ConstI64(self.decode_s64()? as u64))),
            0x43 => Ok(Instr::new(ConstF32(F32Bytes::new(self.decode_f32()?)))),
            0x44 => Ok(Instr::new(ConstF64(F64Bytes::new(self.decode_f64()?)))),

            0x45 => Ok(Instr::new(TestopI32(TestopKind::Eqz))),
            0x46 => Ok(Instr::new(RelopI32(IRelopKind::Eq))),
            0x47 => Ok(Instr::new(RelopI32(IRelopKind::Ne))),
            0x48 => Ok(Instr::new(RelopI32(IRelopKind::LtS))),
            0x49 => Ok(Instr::new(RelopI32(IRelopKind::LtU))),
            0x4A => Ok(Instr::new(RelopI32(IRelopKind::GtS))),
            0x4B => Ok(Instr::new(RelopI32(IRelopKind::GtU))),
            0x4C => Ok(Instr::new(RelopI32(IRelopKind::LeS))),
            0x4D => Ok(Instr::new(RelopI32(IRelopKind::LeU))),
            0x4E => Ok(Instr::new(RelopI32(IRelopKind::GeS))),
            0x4F => Ok(Instr::new(RelopI32(IRelopKind::GeU))),

            0x50 => Ok(Instr::new(TestopI64(TestopKind::Eqz))),
            0x51 => Ok(Instr::new(RelopI64(IRelopKind::Eq))),
            0x52 => Ok(Instr::new(RelopI64(IRelopKind::Ne))),
            0x53 => Ok(Instr::new(RelopI64(IRelopKind::LtS))),
            0x54 => Ok(Instr::new(RelopI64(IRelopKind::LtU))),
            0x55 => Ok(Instr::new(RelopI64(IRelopKind::GtS))),
            0x56 => Ok(Instr::new(RelopI64(IRelopKind::GtU))),
            0x57 => Ok(Instr::new(RelopI64(IRelopKind::LeS))),
            0x58 => Ok(Instr::new(RelopI64(IRelopKind::LeU))),
            0x59 => Ok(Instr::new(RelopI64(IRelopKind::GeS))),
            0x5A => Ok(Instr::new(RelopI64(IRelopKind::GeU))),

            0x5B => Ok(Instr::new(RelopF32(FRelopKind::Eq))),
            0x5C => Ok(Instr::new(RelopF32(FRelopKind::Ne))),
            0x5D => Ok(Instr::new(RelopF32(FRelopKind::Lt))),
            0x5E => Ok(Instr::new(RelopF32(FRelopKind::Gt))),
            0x5F => Ok(Instr::new(RelopF32(FRelopKind::Le))),
            0x60 => Ok(Instr::new(RelopF32(FRelopKind::Ge))),

            0x61 => Ok(Instr::new(RelopF64(FRelopKind::Eq))),
            0x62 => Ok(Instr::new(RelopF64(FRelopKind::Ne))),
            0x63 => Ok(Instr::new(RelopF64(FRelopKind::Lt))),
            0x64 => Ok(Instr::new(RelopF64(FRelopKind::Gt))),
            0x65 => Ok(Instr::new(RelopF64(FRelopKind::Le))),
            0x66 => Ok(Instr::new(RelopF64(FRelopKind::Ge))),

            0x67 => Ok(Instr::new(UnopI32(IUnopKind::Clz))),
            0x68 => Ok(Instr::new(UnopI32(IUnopKind::Ctz))),
            0x69 => Ok(Instr::new(UnopI32(IUnopKind::Popcnt))),
            0x6A => Ok(Instr::new(BinopI32(IBinopKind::Add))),
            0x6B => Ok(Instr::new(BinopI32(IBinopKind::Sub))),
            0x6C => Ok(Instr::new(BinopI32(IBinopKind::Mul))),
            0x6D => Ok(Instr::new(BinopI32(IBinopKind::DivS))),
            0x6E => Ok(Instr::new(BinopI32(IBinopKind::DivU))),
            0x6F => Ok(Instr::new(BinopI32(IBinopKind::RemS))),
            0x70 => Ok(Instr::new(BinopI32(IBinopKind::RemU))),
            0x71 => Ok(Instr::new(BinopI32(IBinopKind::And))),
            0x72 => Ok(Instr::new(BinopI32(IBinopKind::Or))),
            0x73 => Ok(Instr::new(BinopI32(IBinopKind::Xor))),
            0x74 => Ok(Instr::new(BinopI32(IBinopKind::Shl))),
            0x75 => Ok(Instr::new(BinopI32(IBinopKind::ShrS))),
            0x76 => Ok(Instr::new(BinopI32(IBinopKind::ShrU))),
            0x77 => Ok(Instr::new(BinopI32(IBinopKind::Rotl))),
            0x78 => Ok(Instr::new(BinopI32(IBinopKind::Rotr))),

            0x79 => Ok(Instr::new(UnopI64(IUnopKind::Clz))),
            0x7A => Ok(Instr::new(UnopI64(IUnopKind::Ctz))),
            0x7B => Ok(Instr::new(UnopI64(IUnopKind::Popcnt))),
            0x7C => Ok(Instr::new(BinopI64(IBinopKind::Add))),
            0x7D => Ok(Instr::new(BinopI64(IBinopKind::Sub))),
            0x7E => Ok(Instr::new(BinopI64(IBinopKind::Mul))),
            0x7F => Ok(Instr::new(BinopI64(IBinopKind::DivS))),
            0x80 => Ok(Instr::new(BinopI64(IBinopKind::DivU))),
            0x81 => Ok(Instr::new(BinopI64(IBinopKind::RemS))),
            0x82 => Ok(Instr::new(BinopI64(IBinopKind::RemU))),
            0x83 => Ok(Instr::new(BinopI64(IBinopKind::And))),
            0x84 => Ok(Instr::new(BinopI64(IBinopKind::Or))),
            0x85 => Ok(Instr::new(BinopI64(IBinopKind::Xor))),
            0x86 => Ok(Instr::new(BinopI64(IBinopKind::Shl))),
            0x87 => Ok(Instr::new(BinopI64(IBinopKind::ShrS))),
            0x88 => Ok(Instr::new(BinopI64(IBinopKind::ShrU))),
            0x89 => Ok(Instr::new(BinopI64(IBinopKind::Rotl))),
            0x8A => Ok(Instr::new(BinopI64(IBinopKind::Rotr))),

            0x8B => Ok(Instr::new(UnopF32(FUnopKind::Abs))),
            0x8C => Ok(Instr::new(UnopF32(FUnopKind::Neg))),
            0x8D => Ok(Instr::new(UnopF32(FUnopKind::Ceil))),
            0x8E => Ok(Instr::new(UnopF32(FUnopKind::Floor))),
            0x8F => Ok(Instr::new(UnopF32(FUnopKind::Trunc))),
            0x90 => Ok(Instr::new(UnopF32(FUnopKind::Nearest))),
            0x91 => Ok(Instr::new(UnopF32(FUnopKind::Sqrt))),
            0x92 => Ok(Instr::new(BinopF32(FBinopKind::Add))),
            0x93 => Ok(Instr::new(BinopF32(FBinopKind::Sub))),
            0x94 => Ok(Instr::new(BinopF32(FBinopKind::Mul))),
            0x95 => Ok(Instr::new(BinopF32(FBinopKind::Div))),
            0x96 => Ok(Instr::new(BinopF32(FBinopKind::Min))),
            0x97 => Ok(Instr::new(BinopF32(FBinopKind::Max))),
            0x98 => Ok(Instr::new(BinopF32(FBinopKind::Copysign))),

            0x99 => Ok(Instr::new(UnopF64(FUnopKind::Abs))),
            0x9A => Ok(Instr::new(UnopF64(FUnopKind::Neg))),
            0x9B => Ok(Instr::new(UnopF64(FUnopKind::Ceil))),
            0x9C => Ok(Instr::new(UnopF64(FUnopKind::Floor))),
            0x9D => Ok(Instr::new(UnopF64(FUnopKind::Trunc))),
            0x9E => Ok(Instr::new(UnopF64(FUnopKind::Nearest))),
            0x9F => Ok(Instr::new(UnopF64(FUnopKind::Sqrt))),
            0xA0 => Ok(Instr::new(BinopF64(FBinopKind::Add))),
            0xA1 => Ok(Instr::new(BinopF64(FBinopKind::Sub))),
            0xA2 => Ok(Instr::new(BinopF64(FBinopKind::Mul))),
            0xA3 => Ok(Instr::new(BinopF64(FBinopKind::Div))),
            0xA4 => Ok(Instr::new(BinopF64(FBinopKind::Min))),
            0xA5 => Ok(Instr::new(BinopF64(FBinopKind::Max))),
            0xA6 => Ok(Instr::new(BinopF64(FBinopKind::Copysign))),

            0xA7 => Ok(Instr::new(Cvtop(CvtopKind::I32WrapI64))),
            0xA8 => Ok(Instr::new(Cvtop(CvtopKind::I32TruncF32S))),
            0xA9 => Ok(Instr::new(Cvtop(CvtopKind::I32TruncF32U))),
            0xAA => Ok(Instr::new(Cvtop(CvtopKind::I32TruncF64S))),
            0xAB => Ok(Instr::new(Cvtop(CvtopKind::I32TruncF64U))),
            0xAC => Ok(Instr::new(Cvtop(CvtopKind::I64ExtendI32S))),
            0xAD => Ok(Instr::new(Cvtop(CvtopKind::I64ExtendI32U))),
            0xAE => Ok(Instr::new(Cvtop(CvtopKind::I64TruncF32S))),
            0xAF => Ok(Instr::new(Cvtop(CvtopKind::I64TruncF32U))),
            0xB0 => Ok(Instr::new(Cvtop(CvtopKind::I64TruncF64S))),
            0xB1 => Ok(Instr::new(Cvtop(CvtopKind::I64TruncF64U))),
            0xB2 => Ok(Instr::new(Cvtop(CvtopKind::F32ConvertI32S))),
            0xB3 => Ok(Instr::new(Cvtop(CvtopKind::F32ConvertI32U))),
            0xB4 => Ok(Instr::new(Cvtop(CvtopKind::F32ConvertI64S))),
            0xB5 => Ok(Instr::new(Cvtop(CvtopKind::F32ConvertI64U))),
            0xB6 => Ok(Instr::new(Cvtop(CvtopKind::F32DemoteF64))),
            0xB7 => Ok(Instr::new(Cvtop(CvtopKind::F64ConvertI32S))),
            0xB8 => Ok(Instr::new(Cvtop(CvtopKind::F64ConvertI32U))),
            0xB9 => Ok(Instr::new(Cvtop(CvtopKind::F64ConvertI64S))),
            0xBA => Ok(Instr::new(Cvtop(CvtopKind::F64ConvertI64U))),
            0xBB => Ok(Instr::new(Cvtop(CvtopKind::F64PromoteF32))),
            0xBC => Ok(Instr::new(Cvtop(CvtopKind::I32ReinterpretF32))),
            0xBD => Ok(Instr::new(Cvtop(CvtopKind::I64ReinterpretF64))),
            0xBE => Ok(Instr::new(Cvtop(CvtopKind::F32ReinterpretI32))),
            0xBF => Ok(Instr::new(Cvtop(CvtopKind::F64ReinterpretI64))),

            0xC0 => Ok(Instr::new(Extend(ExtendKind::I32As8S))),
            0xC1 => Ok(Instr::new(Extend(ExtendKind::I32As16S))),
            0xC2 => Ok(Instr::new(Extend(ExtendKind::I64As8S))),
            0xC3 => Ok(Instr::new(Extend(ExtendKind::I64As16S))),
            0xC4 => Ok(Instr::new(Extend(ExtendKind::I64As32S))),

            0xFC => {
                let prefix = self.decode_u32()? as usize;
                let trunc_sat_kinds = [
                    CvtopKind::I32TruncSatF32S,
                    CvtopKind::I32TruncSatF32U,
                    CvtopKind::I32TruncSatF64S,
                    CvtopKind::I32TruncSatF64U,
                    CvtopKind::I64TruncSatF32S,
                    CvtopKind::I64TruncSatF32U,
                    CvtopKind::I64TruncSatF64S,
                    CvtopKind::I64TruncSatF64U,
                ];
                if prefix > trunc_sat_kinds.len() {
                    unimplemented!(); // @todo raise Error
                }
                Ok(Instr::new(Cvtop(trunc_sat_kinds[prefix])))
            }

            _ => panic!("unhandled opcode: 0x{:>02X}", b),
        }
    }

    fn decode_expr(&mut self) -> Result<Expr, DecodeError> {
        let instr_seq = self
            .decode_until([TerminatorKind::End].iter().cloned().collect())
            .map(|p| p.0)?;
        Ok(Expr::new(instr_seq))
    }

    fn decode_typeidx(&mut self) -> Result<Typeidx, DecodeError> {
        Ok(Typeidx::new(self.decode_u32()?))
    }

    fn decode_funcidx(&mut self) -> Result<Funcidx, DecodeError> {
        Ok(Funcidx::new(self.decode_u32()?))
    }

    fn decode_tableidx(&mut self) -> Result<Tableidx, DecodeError> {
        Ok(Tableidx::new(self.decode_u32()?))
    }

    fn decode_memidx(&mut self) -> Result<Memidx, DecodeError> {
        Ok(Memidx::new(self.decode_u32()?))
    }

    fn decode_globalidx(&mut self) -> Result<Globalidx, DecodeError> {
        Ok(Globalidx::new(self.decode_u32()?))
    }

    fn decode_localidx(&mut self) -> Result<Localidx, DecodeError> {
        Ok(Localidx::new(self.decode_u32()?))
    }

    fn decode_labelidx(&mut self) -> Result<Labelidx, DecodeError> {
        Ok(Labelidx::new(self.decode_u32()?))
    }

    fn decode_section_id(&mut self) -> Result<SectionId, DecodeError> {
        let n = self.decode_byte()?;
        match n {
            0 => Ok(SectionId::Custom),
            1 => Ok(SectionId::Type),
            2 => Ok(SectionId::Import),
            3 => Ok(SectionId::Function),
            4 => Ok(SectionId::Table),
            5 => Ok(SectionId::Memory),
            6 => Ok(SectionId::Global),
            7 => Ok(SectionId::Export),
            8 => Ok(SectionId::Start),
            9 => Ok(SectionId::Element),
            10 => Ok(SectionId::Code),
            11 => Ok(SectionId::Data),
            _ => Err(DecodeError::UnknownSectionId(n)),
        }
    }

    fn decode_customsec(&mut self, size: usize) -> Result<(Name, Vec<u8>), DecodeError> {
        let before_size = self.read_bytes;
        let name = self.decode_name()?;
        let after_size = self.read_bytes;
        let content_size = size - (after_size - before_size);
        let mut content = Vec::new();
        for _ in 0..content_size {
            content.push(self.decode_byte()?);
        }
        Ok((name, content))
    }

    fn decode_typesec(&mut self) -> Result<Vec<Functype>, DecodeError> {
        self.decode_vec(Self::decode_functype)
    }

    fn decode_importsec(&mut self) -> Result<Vec<Import>, DecodeError> {
        self.decode_vec(Self::decode_import)
    }

    fn decode_import(&mut self) -> Result<Import, DecodeError> {
        let module = self.decode_name()?;
        let name = self.decode_name()?;
        let desc = self.decode_importdesc()?;
        Ok(Import::new(module, name, desc))
    }

    fn decode_importdesc(&mut self) -> Result<Importdesc, DecodeError> {
        let b = self.decode_byte()?;
        match b {
            0x00 => Ok(Importdesc::Func(self.decode_typeidx()?)),
            0x01 => Ok(Importdesc::Table(self.decode_tabletype()?)),
            0x02 => Ok(Importdesc::Mem(self.decode_memtype()?)),
            0x03 => Ok(Importdesc::Global(self.decode_globaltype()?)),
            _ => Err(DecodeError::InvalidImportKind),
        }
    }

    fn decode_funcsec(&mut self) -> Result<Vec<Typeidx>, DecodeError> {
        self.decode_vec(Self::decode_typeidx)
    }

    fn decode_tablesec(&mut self) -> Result<Vec<Table>, DecodeError> {
        self.decode_vec(Self::decode_table)
    }

    fn decode_table(&mut self) -> Result<Table, DecodeError> {
        let typ = self.decode_tabletype()?;
        Ok(Table::new(typ))
    }

    fn decode_magic(&mut self) -> Result<(), DecodeError> {
        let mut buf = [0; 4];
        self.read(&mut buf)?;
        if buf == [0x00, 0x61, 0x73, 0x6D] {
            Ok(())
        } else {
            Err(DecodeError::MagicNumberMismatch)
        }
    }

    fn decode_memsec(&mut self) -> Result<Vec<Mem>, DecodeError> {
        self.decode_vec(Self::decode_mem)
    }

    fn decode_mem(&mut self) -> Result<Mem, DecodeError> {
        let typ = self.decode_memtype()?;
        Ok(Mem::new(typ))
    }

    fn decode_globalsec(&mut self) -> Result<Vec<Global>, DecodeError> {
        self.decode_vec(Self::decode_global)
    }

    fn decode_global(&mut self) -> Result<Global, DecodeError> {
        let typ = self.decode_globaltype()?;
        let init = self.decode_expr()?;
        Ok(Global::new(typ, init))
    }

    fn decode_exportsec(&mut self) -> Result<Vec<Export>, DecodeError> {
        self.decode_vec(Self::decode_export)
    }

    fn decode_export(&mut self) -> Result<Export, DecodeError> {
        let name = self.decode_name()?;
        let exportdesc = self.decode_exportdesc()?;
        Ok(Export::new(name, exportdesc))
    }

    fn decode_exportdesc(&mut self) -> Result<Exportdesc, DecodeError> {
        let b = self.decode_byte()?;
        match b {
            0x00 => Ok(Exportdesc::Func(self.decode_funcidx()?)),
            0x01 => Ok(Exportdesc::Table(self.decode_tableidx()?)),
            0x02 => Ok(Exportdesc::Mem(self.decode_memidx()?)),
            0x03 => Ok(Exportdesc::Global(self.decode_globalidx()?)),
            _ => Err(DecodeError::UnknownExportdesc(b)),
        }
    }

    fn decode_startsec(&mut self) -> Result<Funcidx, DecodeError> {
        self.decode_funcidx()
    }

    fn decode_elemsec(&mut self) -> Result<Vec<Elem>, DecodeError> {
        self.decode_vec(Self::decode_elem)
    }

    fn decode_elem(&mut self) -> Result<Elem, DecodeError> {
        let table = self.decode_tableidx()?;
        let offset = self.decode_expr()?;
        let init = self.decode_vec(Self::decode_funcidx)?;
        Ok(Elem::new(table, offset, init))
    }

    fn decode_codesec(&mut self) -> Result<Vec<FuncCode>, DecodeError> {
        self.decode_vec(Self::decode_code)
    }

    fn decode_code(&mut self) -> Result<FuncCode, DecodeError> {
        let _size = self.decode_u32()? as usize;
        self.decode_func()
    }

    fn decode_func(&mut self) -> Result<FuncCode, DecodeError> {
        let locals = self.decode_vec(Self::decode_local)?;
        let num_locals = locals.iter().map(|(_, n)| n).sum::<usize>();
        if num_locals > u32::MAX as usize {
            return Err(DecodeError::InvalidFunc(num_locals));
        }
        let mut locals_result = Vec::new();
        for (t, n) in locals {
            let mut local = iter::repeat(t).take(n as usize).collect();
            locals_result.append(&mut local);
        }
        let e = self.decode_expr()?;
        Ok(FuncCode {
            locals: locals_result,
            body: e,
        })
    }

    fn decode_local(&mut self) -> Result<(Valtype, usize), DecodeError> {
        let n = self.decode_u32()?;
        let t = self.decode_valtype()?;
        Ok((t, n as usize))
    }

    fn decode_datasec(&mut self) -> Result<Vec<Data>, DecodeError> {
        self.decode_vec(Self::decode_data)
    }

    fn decode_data(&mut self) -> Result<Data, DecodeError> {
        let data = self.decode_memidx()?;
        let offset = self.decode_expr()?;
        let init = self.decode_vec(Self::decode_byte)?;
        Ok(Data::new(data, offset, init))
    }

    fn decode_version(&mut self) -> Result<(), DecodeError> {
        let mut buf = [0; 4];
        self.read(&mut buf)?;
        if buf == [0x01, 0x00, 0x00, 0x00] {
            Ok(())
        } else {
            Err(DecodeError::VersionMismatch)
        }
    }

    fn decode_module(&mut self) -> Result<Module, DecodeError> {
        self.decode_magic()?;
        self.decode_version()?;

        let mut types = None;
        let mut imports = None;
        let mut func_declarations = None;
        let mut tables = None;
        let mut mems = None;
        let mut globals = None;
        let mut exports = None;
        let mut start = None;
        let mut elems = None;
        let mut code = None;
        let mut data = None;

        loop {
            use DecodeError::UnexpectedEnd;
            let section_id = match self.decode_section_id() {
                Ok(section_id) => section_id,
                Err(UnexpectedEnd) => break,
                Err(err) => return Err(err),
            };
            let size = self.decode_u32()?;
            let before_read_bytes = self.read_bytes;
            match section_id {
                SectionId::Custom => {
                    let (_name, _content) = self.decode_customsec(size as usize)?;
                }
                SectionId::Type => {
                    assert_eq!(types, None);
                    types = Some(self.decode_typesec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Import => {
                    assert_eq!(imports, None);
                    imports = Some(self.decode_importsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Function => {
                    assert_eq!(func_declarations, None);
                    func_declarations = Some(self.decode_funcsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Table => {
                    assert_eq!(tables, None);
                    tables = Some(self.decode_tablesec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Memory => {
                    assert_eq!(mems, None);
                    mems = Some(self.decode_memsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Global => {
                    assert_eq!(globals, None);
                    globals = Some(self.decode_globalsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Export => {
                    assert_eq!(exports, None);
                    exports = Some(self.decode_exportsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Start => {
                    if start.is_some() {
                        return Err(DecodeError::JunkAfterLastSection);
                    }
                    assert_eq!(start, None);
                    start = Some(self.decode_startsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Element => {
                    assert_eq!(elems, None);
                    elems = Some(self.decode_elemsec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Code => {
                    assert_eq!(code, None);
                    code = Some(self.decode_codesec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
                SectionId::Data => {
                    assert_eq!(data, None);
                    data = Some(self.decode_datasec().map_err(|err| {
                        if err == DecodeError::UnexpectedEnd {
                            DecodeError::UnexpectedSectionEnd
                        } else {
                            err
                        }
                    })?);
                }
            }
            let after_read_bytes = self.read_bytes;
            if after_read_bytes - before_read_bytes != size as usize {
                return Err(DecodeError::SectionSizeMismatch);
            }
        }

        let funcs = match (func_declarations, code) {
            (Some(func_declarations), Some(code)) if func_declarations.len() == code.len() => Some(
                func_declarations
                    .into_iter()
                    .zip(code.into_iter())
                    .map(|(typ, c)| Func::new(typ, c.locals, c.body))
                    .collect(),
            ),
            (Some(func_declarations), None) if func_declarations.is_empty() => None,
            (None, Some(code)) if code.is_empty() => None,
            (None, None) => None,
            _ => {
                return Err(DecodeError::FunctionDeclarationAndDefinitionLengthMismatch);
            }
        };

        Ok(Module::new(
            types.unwrap_or_default(),
            imports.unwrap_or_default(),
            funcs.unwrap_or_default(),
            tables.unwrap_or_default(),
            mems.unwrap_or_default(),
            globals.unwrap_or_default(),
            exports.unwrap_or_default(),
            start,
            elems.unwrap_or_default(),
            data.unwrap_or_default(),
        ))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum DecodeError {
    MagicNumberMismatch,
    VersionMismatch,
    UnexpectedEnd,
    UnexpectedSectionEnd,
    SectionSizeMismatch,
    UnknownSectionId(u8),
    FunctionDeclarationAndDefinitionLengthMismatch,
    InvalidIntegerRange,
    InvalidIntegerRepresentation,
    UnknownValtype(u8),
    UnknownFunctype(u8),
    UnknownMut(u8),
    UnknownExportdesc(u8),
    UnknownElemtype(u8),
    InvalidUtf8Sequence(String),
    ZeroFlagExpected,
    InvalidFunc(usize),
    InvalidImportKind,
    JunkAfterLastSection,
    InvalidHeaderFormat(String),
    DecoderStateInconsistency(String),
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use DecodeError::*;
        match self {
            MagicNumberMismatch => write!(f, "MagicNumberMismatch:"),
            VersionMismatch => write!(f, "VersionMismatch:"),
            UnexpectedEnd => write!(f, "UnexpectedEnd:"),
            UnexpectedSectionEnd => write!(f, "UnexpectedSectionEnd:"),
            SectionSizeMismatch => write!(f, "SectionSizeMismatch:"),
            UnknownSectionId(x) => write!(f, "UnknownSectionId: {}", x),
            FunctionDeclarationAndDefinitionLengthMismatch => {
                write!(f, "FunctionDeclarationAndDefinitionLengthMismatch")
            }
            InvalidIntegerRange => write!(f, "InvalidIntegerRange:"),
            InvalidIntegerRepresentation => write!(f, "InvalidIntegerRepresentation:"),
            UnknownValtype(x) => write!(f, "UnknownValtype: {}", x),
            UnknownFunctype(x) => write!(f, "UnknownFunctype: {}", x),
            UnknownMut(x) => write!(f, "UnknownMut: {}", x),
            UnknownExportdesc(x) => write!(f, "UnknownExportdesc: {}", x),
            UnknownElemtype(x) => write!(f, "UnknownElemtype: {}", x),
            InvalidUtf8Sequence(detail) => write!(f, "InvalidUtf8Sequence: {}", detail),
            ZeroFlagExpected => write!(f, "ZeroFlagExpected:"),
            InvalidFunc(x) => write!(f, "InvalidFunc: {}", x),
            InvalidImportKind => write!(f, "InvalidImportKind:"),
            JunkAfterLastSection => write!(f, "JunkAfterLastSection:"),
            InvalidHeaderFormat(detail) => write!(f, "InvalidHeaderFormat: {}", detail),
            DecoderStateInconsistency(detail) => write!(f, "DecoderStateInconsistency: {}", detail),
        }
    }
}
