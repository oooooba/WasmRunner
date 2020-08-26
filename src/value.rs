use crate::types::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct F32Bytes {
    bytes: [u8; 4],
}

impl F32Bytes {
    pub fn new(n: f32) -> Self {
        Self {
            bytes: n.to_le_bytes(),
        }
    }

    pub fn to_f32(self) -> f32 {
        f32::from_le_bytes(self.bytes)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueKind {
    I32(u32),
    I64(u64),
    F32(F32Bytes),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    kind: ValueKind,
}

impl Value {
    pub fn new(kind: ValueKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> ValueKind {
        self.kind
    }

    pub fn typ(&self) -> Valtype {
        match self.kind {
            ValueKind::I32(_) => Valtype::I32,
            ValueKind::I64(_) => Valtype::I64,
            ValueKind::F32(_) => Valtype::F32,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum WasmRunnerResult {
    Values(Vec<Value>),
}
