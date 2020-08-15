use std::collections::HashSet;
use std::fmt;
use std::io::Read;
use std::iter;

use crate::instr::*;
use crate::module::*;
use crate::types::*;

fn decode_vec<R: Read, E>(
    reader: &mut R,
    elem_decoder: fn(&mut R) -> Result<E, DecodeError>,
) -> Result<Vec<E>, DecodeError> {
    let num = decode_u32(reader)?;
    let mut result = Vec::with_capacity(num as usize);
    for _ in 0..num {
        let elem = elem_decoder(reader)?;
        result.push(elem);
    }
    Ok(result)
}

fn decode_byte_with_size<R: Read>(reader: &mut R) -> Result<(u8, usize), DecodeError> {
    let mut buf = [0; 1];
    reader
        .read_exact(&mut buf)
        .map_err(|e| DecodeError::ReadFailure(e.to_string()))?;
    Ok((buf[0], 1))
}

fn decode_byte<R: Read>(reader: &mut R) -> Result<u8, DecodeError> {
    decode_byte_with_size(reader).map(|(v, _)| v)
}

fn decode_u32_with_size<R: Read>(reader: &mut R) -> Result<(u32, usize), DecodeError> {
    let mut read_size = 0;
    let mut result = 0u64;
    for i in 0..5 {
        let mut buf = [0; 1];
        reader
            .read_exact(&mut buf)
            .map_err(|e| DecodeError::ReadFailure(e.to_string()))?;
        read_size += 1;
        let b = buf[0] as u64;
        result |= (b & 0x7F) << (i * 7);
        if result > (u32::MAX as u64) {
            return Err(DecodeError::OutOfRangeValue(Valtype::I32));
        }
        if (b & 0x80) == 0 {
            break;
        }
    }
    Ok((result as u32, read_size))
}

fn decode_u32<R: Read>(reader: &mut R) -> Result<u32, DecodeError> {
    decode_u32_with_size(reader).map(|(v, _)| v)
}

fn decode_u64<R: Read>(reader: &mut R) -> Result<u64, DecodeError> {
    let mut result = 0u128;
    for i in 0..10 {
        let mut buf = [0; 1];
        reader
            .read_exact(&mut buf)
            .map_err(|e| DecodeError::ReadFailure(e.to_string()))?;
        let b = buf[0] as u128;
        result |= (b & 0x7F) << (i * 7);
        if result > (u64::MAX as u128) {
            return Err(DecodeError::OutOfRangeValue(Valtype::I64));
        }
        if (b & 0x80) == 0 {
            break;
        }
    }
    Ok(result as u64)
}

fn decode_name<R: Read>(reader: &mut R) -> Result<Name, DecodeError> {
    let bytes = decode_vec(reader, decode_byte)?;
    let name = String::from_utf8(bytes).map_err(|e| DecodeError::InvalidName(e.to_string()))?;
    Ok(Name::new(name))
}

fn decode_valtype<R: Read>(reader: &mut R) -> Result<Valtype, DecodeError> {
    let b = decode_byte(reader)?;
    match b {
        0x7F => Ok(Valtype::I32),
        0x7E => Ok(Valtype::I64),
        0x7D => unimplemented!(),
        0x7C => unimplemented!(),
        _ => Err(DecodeError::UnknownValtype(b)),
    }
}

fn decode_resulttype<R: Read>(reader: &mut R) -> Result<Resulttype, DecodeError> {
    Ok(Resulttype::new(decode_vec(reader, decode_valtype)?))
}

fn decode_functype<R: Read>(reader: &mut R) -> Result<Functype, DecodeError> {
    let b = decode_byte(reader)?;
    if b != 0x60 {
        return Err(DecodeError::UnknownFunctype(b));
    }
    let rt1 = decode_resulttype(reader)?;
    let rt2 = decode_resulttype(reader)?;
    Ok(Functype::new(rt1, rt2))
}

fn decode_limit<R: Read>(reader: &mut R) -> Result<Limit, DecodeError> {
    let b = decode_byte(reader)?;
    let (min, max) = match b {
        0 => (decode_u32(reader)?, None),
        1 => {
            let n = decode_u32(reader)?;
            let m = decode_u32(reader)?;
            (n, Some(m))
        }
        _ => {
            return Err(DecodeError::UnknownLimit(b));
        }
    };
    Ok(Limit::new(min, max))
}

fn decode_memtype<R: Read>(reader: &mut R) -> Result<Memtype, DecodeError> {
    let limit = decode_limit(reader)?;
    Ok(Memtype::new(limit))
}

fn decode_tabletype<R: Read>(reader: &mut R) -> Result<Tabletype, DecodeError> {
    let elemtype = decode_elemtype(reader)?;
    let limit = decode_limit(reader)?;
    Ok(Tabletype::new(limit, elemtype))
}

fn decode_elemtype<R: Read>(reader: &mut R) -> Result<Elemtype, DecodeError> {
    let b = decode_byte(reader)?;
    match b {
        0x70 => Ok(Elemtype::Funcref),
        _ => Err(DecodeError::UnknownElemtype(b)),
    }
}

fn decode_globaltype<R: Read>(reader: &mut R) -> Result<Globaltype, DecodeError> {
    let valtype = decode_valtype(reader)?;
    let mutability = decode_mut(reader)?;
    Ok(Globaltype::new(valtype, mutability))
}

fn decode_mut<R: Read>(reader: &mut R) -> Result<Mutability, DecodeError> {
    let b = decode_byte(reader)?;
    match b {
        0x00 => Ok(Mutability::Const),
        0x01 => Ok(Mutability::Var),
        _ => Err(DecodeError::UnknownMut(b)),
    }
}

fn decode_until<R: Read>(
    reader: &mut R,
    terminator_set: HashSet<TerminatorKind>,
) -> Result<(InstrSeq, TerminatorKind), DecodeError> {
    let mut instrs = Vec::new();
    loop {
        let instr = decode_instr(reader)?;
        if let InstrKind::Terminator(terminator_kind) = instr.kind {
            if terminator_set.contains(&terminator_kind) {
                return Ok((InstrSeq::new(instrs), terminator_kind));
            }
        }
        instrs.push(instr);
    }
}

fn decode_blocktype<R: Read>(reader: &mut R) -> Result<Blocktype, DecodeError> {
    // @todo support S33
    let b = decode_byte(reader)?;
    let blocktype = match b {
        0x40 => Blocktype::Empty,
        0x7F => Blocktype::Valtype(Valtype::I32),
        0x7E => Blocktype::Valtype(Valtype::I64),
        0x7D => unimplemented!(),
        0x7C => unimplemented!(),
        _ => Blocktype::S33(Typeidx::new(b.into())),
    };
    Ok(blocktype)
}

fn decode_memarg<R: Read>(reader: &mut R) -> Result<Memarg, DecodeError> {
    let align = decode_u32(reader)?;
    let offset = decode_u32(reader)?;
    Ok(Memarg::new(align, offset))
}

fn decode_instr<R: Read>(reader: &mut R) -> Result<Instr, DecodeError> {
    let b = decode_byte(reader)?;
    use InstrKind::*;
    match b {
        0x00 => Ok(Instr::new(Unreachable)),
        0x01 => Ok(Instr::new(Nop)),
        0x02 => {
            let blocktype = decode_blocktype(reader)?;
            let instr_seq =
                decode_until(reader, [TerminatorKind::End].iter().cloned().collect())?.0;
            Ok(Instr::new(Block(blocktype, instr_seq)))
        }
        0x03 => {
            let blocktype = decode_blocktype(reader)?;
            let instr_seq =
                decode_until(reader, [TerminatorKind::End].iter().cloned().collect())?.0;
            Ok(Instr::new(Loop(blocktype, instr_seq)))
        }
        0x04 => {
            let blocktype = decode_blocktype(reader)?;
            let (then_instr_seq, terminator_kind) = decode_until(
                reader,
                [TerminatorKind::End, TerminatorKind::Else]
                    .iter()
                    .cloned()
                    .collect(),
            )?;
            let else_instr_seq = match terminator_kind {
                TerminatorKind::End => InstrSeq::new_empty(),
                TerminatorKind::Else => {
                    decode_until(reader, [TerminatorKind::End].iter().cloned().collect())?.0
                }
            };
            Ok(Instr::new(If(blocktype, then_instr_seq, else_instr_seq)))
        }
        0x05 => Ok(Instr::new(Terminator(TerminatorKind::Else))),
        0x0B => Ok(Instr::new(Terminator(TerminatorKind::End))),
        0x0C => Ok(Instr::new(Br(decode_labelidx(reader)?))),
        0x0D => Ok(Instr::new(BrIf(decode_labelidx(reader)?))),
        0x0E => {
            let labelidxes = decode_vec(reader, decode_labelidx)?;
            let default_labelidx = decode_labelidx(reader)?;
            Ok(Instr::new(BrTable(labelidxes, default_labelidx)))
        }
        0x0F => Ok(Instr::new(Return)),
        0x10 => Ok(Instr::new(Call(decode_funcidx(reader)?))),
        0x11 => {
            let typeidx = decode_typeidx(reader)?;
            let b = decode_byte(reader)?;
            if b != 0 {
                return Err(DecodeError::InvalidInstr(format!(
                    "invalid delimiter ({}) of call_indirect instr",
                    b
                )));
            }
            Ok(Instr::new(CallIndirect(typeidx)))
        }

        0x1A => Ok(Instr::new(Drop)),
        0x1B => Ok(Instr::new(Select)),

        0x20 => Ok(Instr::new(GetLocal(decode_localidx(reader)?))),
        0x21 => Ok(Instr::new(SetLocal(decode_localidx(reader)?))),

        0x36 => Ok(Instr::new(StoreI32(decode_memarg(reader)?))),

        0x41 => Ok(Instr::new(ConstI32(decode_u32(reader)?))), // @todo read_i32に直す
        0x42 => Ok(Instr::new(ConstI64(decode_u64(reader)?))), // @todo read_i64に直す

        0x45 => Ok(Instr::new(TestopI32(TestopKind::Eqz))),
        0x46 => Ok(Instr::new(RelopI32(RelopKind::Eq))),

        0x68 => Ok(Instr::new(UnopI32(UnopKind::Ctz))),
        0x6A => Ok(Instr::new(BinopI32(BinopKind::Add))),
        0x6B => Ok(Instr::new(BinopI32(BinopKind::Sub))),
        0x6C => Ok(Instr::new(BinopI32(BinopKind::Mul))),
        0x6E => Ok(Instr::new(BinopI32(BinopKind::UDiv))),

        0x7A => Ok(Instr::new(UnopI64(UnopKind::Ctz))),

        _ => panic!("unhandled opcode: {}", b),
    }
}

fn decode_expr<R: Read>(reader: &mut R) -> Result<Expr, DecodeError> {
    let instr_seq =
        decode_until(reader, [TerminatorKind::End].iter().cloned().collect()).map(|p| p.0)?;
    Ok(Expr::new(instr_seq))
}

fn decode_typeidx<R: Read>(reader: &mut R) -> Result<Typeidx, DecodeError> {
    Ok(Typeidx::new(decode_u32(reader)?))
}

fn decode_funcidx<R: Read>(reader: &mut R) -> Result<Funcidx, DecodeError> {
    Ok(Funcidx::new(decode_u32(reader)?))
}

fn decode_tableidx<R: Read>(reader: &mut R) -> Result<Tableidx, DecodeError> {
    Ok(Tableidx::new(decode_u32(reader)?))
}

fn decode_localidx<R: Read>(reader: &mut R) -> Result<Localidx, DecodeError> {
    Ok(Localidx::new(decode_u32(reader)?))
}

fn decode_labelidx<R: Read>(reader: &mut R) -> Result<Labelidx, DecodeError> {
    Ok(Labelidx::new(decode_u32(reader)?))
}

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

static U8_TO_SECTION_ID_TABLE: &'static [SectionId] = &[
    SectionId::Custom,
    SectionId::Type,
    SectionId::Import,
    SectionId::Function,
    SectionId::Table,
    SectionId::Memory,
    SectionId::Global,
    SectionId::Export,
    SectionId::Start,
    SectionId::Element,
    SectionId::Code,
    SectionId::Data,
];

#[derive(Debug)]
struct Section {
    id: SectionId,
    size: u32,
    contents: Vec<u8>,
}

fn decode_section<R: Read>(reader: &mut R) -> Result<(Section, usize), DecodeError> {
    let mut read_size = 0;

    let (b, n) = decode_byte_with_size(reader)?;
    if (b as usize) >= U8_TO_SECTION_ID_TABLE.len() {
        return Err(DecodeError::UnknownSectionId(b));
    }
    let id = U8_TO_SECTION_ID_TABLE[b as usize];
    read_size += n;

    let (size, n) = decode_u32_with_size(reader)?;
    read_size += n;

    let mut contents = vec![0; size as usize];
    reader
        .read_exact(&mut contents)
        .map_err(|e| DecodeError::ReadFailure(e.to_string()))?;
    read_size += size as usize;
    Ok((Section { id, size, contents }, read_size))
}

fn decode_typesec(section: &Section) -> Result<Vec<Functype>, DecodeError> {
    if section.id != SectionId::Type {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be type section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_functype)
}

fn decode_funcsec(section: &Section) -> Result<Vec<Typeidx>, DecodeError> {
    if section.id != SectionId::Function {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be func section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_typeidx)
}

fn decode_tablesec(section: &Section) -> Result<Vec<Table>, DecodeError> {
    if section.id != SectionId::Table {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be table section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_table)
}

fn decode_table<R: Read>(reader: &mut R) -> Result<Table, DecodeError> {
    let typ = decode_tabletype(reader)?;
    Ok(Table::new(typ))
}

fn decode_memsec(section: &Section) -> Result<Vec<Mem>, DecodeError> {
    if section.id != SectionId::Memory {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be memory section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_mem)
}

fn decode_mem<R: Read>(reader: &mut R) -> Result<Mem, DecodeError> {
    let typ = decode_memtype(reader)?;
    Ok(Mem::new(typ))
}

fn decode_globalsec(section: &Section) -> Result<Vec<Global>, DecodeError> {
    if section.id != SectionId::Global {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be global section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_global)
}

fn decode_global<R: Read>(reader: &mut R) -> Result<Global, DecodeError> {
    let typ = decode_globaltype(reader)?;
    let init = decode_expr(reader)?;
    Ok(Global::new(typ, init))
}

fn decode_exportsec(section: &Section) -> Result<Vec<Export>, DecodeError> {
    if section.id != SectionId::Export {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be export section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_export)
}

fn decode_export<R: Read>(reader: &mut R) -> Result<Export, DecodeError> {
    let name = decode_name(reader)?;
    let exportdesc = decode_exportdesc(reader)?;
    Ok(Export::new(name, exportdesc))
}

fn decode_exportdesc<R: Read>(reader: &mut R) -> Result<Exportdesc, DecodeError> {
    let b = decode_byte(reader)?;
    match b {
        0x00 => {
            let x = decode_funcidx(reader)?;
            Ok(Exportdesc::Funcidx(x))
        }
        _ => Err(DecodeError::UnknownExportdesc(b)),
    }
}

fn decode_elemsec(section: &Section) -> Result<Vec<Elem>, DecodeError> {
    if section.id != SectionId::Element {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be element section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_elem)
}

fn decode_elem<R: Read>(reader: &mut R) -> Result<Elem, DecodeError> {
    let table = decode_tableidx(reader)?;
    let offset = decode_expr(reader)?;
    let init = decode_vec(reader, decode_funcidx)?;
    Ok(Elem::new(table, offset, init))
}

#[derive(Debug, PartialEq, Eq)]
struct FuncCode {
    locals: Vec<Valtype>,
    body: Expr,
}

fn decode_codesec(section: &Section) -> Result<Vec<FuncCode>, DecodeError> {
    if section.id != SectionId::Code {
        return Err(DecodeError::DecoderStateInconsistency(format!(
            "must be code section, but id is {:?}",
            section.id
        )));
    }
    let mut reader = &section.contents[..];
    decode_vec(&mut reader, decode_code)
}

fn decode_code<R: Read>(reader: &mut R) -> Result<FuncCode, DecodeError> {
    let size = decode_u32(reader)? as usize;
    let mut buf = vec![0; size];
    reader
        .read_exact(&mut buf)
        .map_err(|e| DecodeError::ReadFailure(e.to_string()))?;
    let mut reader = &buf[..];
    decode_func(&mut reader)
}

fn decode_func<R: Read>(reader: &mut R) -> Result<FuncCode, DecodeError> {
    let locals = decode_vec(reader, decode_local)?;
    let mut locals_result = Vec::new();
    for mut local in locals.into_iter() {
        locals_result.append(&mut local);
    }
    if locals_result.len() > u32::MAX as usize {
        return Err(DecodeError::InvalidFunc(locals_result.len()));
    }
    let e = decode_expr(reader)?;
    Ok(FuncCode {
        locals: locals_result,
        body: e,
    })
}

fn decode_local<R: Read>(reader: &mut R) -> Result<Vec<Valtype>, DecodeError> {
    let n = decode_u32(reader)?;
    let t = decode_valtype(reader)?;
    Ok(iter::repeat(t).take(n as usize).collect())
}

fn decode_magic<R: Read>(reader: &mut R) -> Result<(), DecodeError> {
    let magic = [0x00, 0x61, 0x73, 0x6D];
    for code in magic.iter() {
        let b = decode_byte(reader)?;
        if b != *code {
            return Err(DecodeError::MagicNumberMismatch);
        }
    }
    Ok(())
}

fn decode_version<R: Read>(reader: &mut R) -> Result<(), DecodeError> {
    let version = [0x01, 0x00, 0x00, 0x00];
    for code in version.iter() {
        let b = decode_byte(reader)?;
        if b != *code {
            return Err(DecodeError::VersionMismatch);
        }
    }
    Ok(())
}

fn decode_module<R: Read>(reader: &mut R) -> Result<Module, DecodeError> {
    decode_magic(reader)?;
    decode_version(reader)?;

    let mut buf = Vec::new();
    let read_bytes = reader
        .read_to_end(&mut buf)
        .map_err(|e| DecodeError::ReadFailure(e.to_string()))?;
    let mut reader = &buf[..];

    let mut sections = Vec::new();
    let mut processed_bytes = 0;
    while processed_bytes < read_bytes {
        let (section, read_size) = decode_section(&mut reader)?;
        sections.push(section);
        processed_bytes += read_size;
    }
    if processed_bytes > read_bytes {
        return Err(DecodeError::InvalidHeaderFormat(format!(
            "header size ({}) is broken, processed {} bytes",
            read_bytes, processed_bytes
        )));
    }

    sections.reverse();

    // @todo handle Custom Sections correctly
    loop {
        match sections.last() {
            Some(section) if section.id == SectionId::Custom => {
                return Err(DecodeError::InvalidHeaderFormat(
                    "custom section is not supported".to_string(),
                ));
            }
            _ => break,
        }
    }

    let types = match sections.last() {
        Some(section) if section.id == SectionId::Type => {
            let section = sections.pop().unwrap();
            Some(decode_typesec(&section)?)
        }
        _ => None,
    };

    let func_declarations = match sections.last() {
        Some(section) if section.id == SectionId::Function => {
            let section = sections.pop().unwrap();
            Some(decode_funcsec(&section)?)
        }
        _ => None,
    };

    let tables = match sections.last() {
        Some(section) if section.id == SectionId::Table => {
            let section = sections.pop().unwrap();
            Some(decode_tablesec(&section)?)
        }
        _ => None,
    };

    let mems = match sections.last() {
        Some(section) if section.id == SectionId::Memory => {
            let section = sections.pop().unwrap();
            Some(decode_memsec(&section)?)
        }
        _ => None,
    };

    let globals = match sections.last() {
        Some(section) if section.id == SectionId::Global => {
            let section = sections.pop().unwrap();
            Some(decode_globalsec(&section)?)
        }
        _ => None,
    };

    let exports = match sections.last() {
        Some(section) if section.id == SectionId::Export => {
            let section = sections.pop().unwrap();
            Some(decode_exportsec(&section)?)
        }
        _ => None,
    };

    let elems = match sections.last() {
        Some(section) if section.id == SectionId::Element => {
            let section = sections.pop().unwrap();
            Some(decode_elemsec(&section)?)
        }
        _ => None,
    };

    let code = match sections.last() {
        Some(section) if section.id == SectionId::Code => {
            let section = sections.pop().unwrap();
            Some(decode_codesec(&section)?)
        }
        _ => None,
    };

    if sections
        .iter()
        .any(|section| section.id != SectionId::Custom)
    {
        return Err(DecodeError::InvalidHeaderFormat(format!(
            "remain unprocessed sections ({:?})",
            sections
        )));
    }

    let funcs = match (func_declarations, code) {
        (Some(func_declarations), Some(code)) => {
            if func_declarations.len() != code.len() {
                return Err(DecodeError::InvalidHeaderFormat(format!("mismatches number of function declarations ({}) and actual function definitions ({})",func_declarations.len() , code.len())));
            }
            Some(
                func_declarations
                    .into_iter()
                    .zip(code.into_iter())
                    .map(|(typ, c)| Func::new(typ, c.locals, c.body))
                    .collect(),
            )
        }
        (None, None) => None,
        _ => {
            return Err(DecodeError::InvalidHeaderFormat(
                "mismatches function declarations and definitions".to_string(),
            ))
        }
    };

    Ok(Module::new(
        types.unwrap_or_default(),
        funcs.unwrap_or_default(),
        tables.unwrap_or_default(),
        mems.unwrap_or_default(),
        globals.unwrap_or_default(),
        exports.unwrap_or_default(),
        elems.unwrap_or_default(),
    ))
}

pub struct Decoder<'a, R: Read> {
    reader: &'a mut R,
}

impl<'a, R: Read> Decoder<'a, R> {
    pub fn new(reader: &'a mut R) -> Self {
        Self { reader }
    }

    pub fn run(&mut self) -> Result<Module, DecodeError> {
        decode_module(self.reader)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum DecodeError {
    MagicNumberMismatch,
    VersionMismatch,
    UnknownSectionId(u8),
    ReadFailure(String),
    OutOfRangeValue(Valtype),
    UnknownValtype(u8),
    UnknownFunctype(u8),
    UnknownLimit(u8),
    UnknownMut(u8),
    UnknownExportdesc(u8),
    UnknownElemtype(u8),
    InvalidName(String),
    InvalidInstr(String),
    InvalidFunc(usize),
    InvalidHeaderFormat(String),
    DecoderStateInconsistency(String),
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use DecodeError::*;
        match self {
            MagicNumberMismatch => write!(f, "MagicNumberMismatch:"),
            VersionMismatch => write!(f, "VersionMismatch:"),
            UnknownSectionId(x) => write!(f, "UnknownSectionId: {}", x),
            ReadFailure(detail) => write!(f, "ReadFailure: {}", detail.to_string()),
            OutOfRangeValue(typ) => {
                write!(f, "OutOfRangeValue: can represent in range of {:?}", typ)
            }
            UnknownValtype(x) => write!(f, "UnknownValtype: {}", x),
            UnknownFunctype(x) => write!(f, "UnknownFunctype: {}", x),
            UnknownLimit(x) => write!(f, "UnknownLimit: {}", x),
            UnknownMut(x) => write!(f, "UnknownMut: {}", x),
            UnknownExportdesc(x) => write!(f, "UnknownExportdesc: {}", x),
            UnknownElemtype(x) => write!(f, "UnknownElemtype: {}", x),
            InvalidName(detail) => write!(f, "InvalidName: {}", detail),
            InvalidInstr(detail) => write!(f, "InvalidInstr: {}", detail),
            InvalidFunc(x) => write!(f, "InvalidFunc: {}", x),
            InvalidHeaderFormat(detail) => write!(f, "InvalidHeaderFormat: {}", detail),
            DecoderStateInconsistency(detail) => write!(f, "DecoderStateInconsistency: {}", detail),
        }
    }
}
