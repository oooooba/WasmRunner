use crate::types::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueKind {
    I32(u32),
    I64(u64),
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
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum WasmRunnerResult {
    Values(Vec<Value>),
    Trap,
}
