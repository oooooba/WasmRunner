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

    pub fn to_absolute_value(self) -> Self {
        let mut bytes = self.bytes;
        bytes[3] &= 0x7F;
        Self { bytes }
    }

    pub fn to_negated_value(self) -> Self {
        let mut bytes = self.bytes;
        bytes[3] ^= 0x80;
        Self { bytes }
    }

    pub fn is_positive(self) -> bool {
        self.bytes[3] & 0x80 == 0
    }

    pub fn is_negative(self) -> bool {
        self.bytes[3] & 0x80 != 0
    }

    pub fn is_positive_zero(self) -> bool {
        self.bytes[0] == 0 && self.bytes[1] == 0 && self.bytes[2] == 0 && self.bytes[3] == 0
    }

    pub fn is_negative_zero(self) -> bool {
        self.bytes[0] == 0 && self.bytes[1] == 0 && self.bytes[2] == 0 && self.bytes[3] == 0x80
    }

    pub fn is_nan(self) -> bool {
        self.to_f32().is_nan()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct F64Bytes {
    bytes: [u8; 8],
}

impl F64Bytes {
    pub fn new(n: f64) -> Self {
        Self {
            bytes: n.to_le_bytes(),
        }
    }

    pub fn to_f64(self) -> f64 {
        f64::from_le_bytes(self.bytes)
    }

    pub fn to_absolute_value(self) -> Self {
        let mut bytes = self.bytes;
        bytes[7] &= 0x7F;
        Self { bytes }
    }

    pub fn to_negated_value(self) -> Self {
        let mut bytes = self.bytes;
        bytes[7] ^= 0x80;
        Self { bytes }
    }

    pub fn is_positive(self) -> bool {
        self.bytes[7] & 0x80 == 0
    }

    pub fn is_negative(self) -> bool {
        self.bytes[7] & 0x80 != 0
    }

    pub fn is_positive_zero(self) -> bool {
        for i in 0..8 {
            if self.bytes[i] != 0 {
                return false;
            }
        }
        true
    }

    pub fn is_negative_zero(self) -> bool {
        for i in 0..7 {
            if self.bytes[i] != 0 {
                return false;
            }
        }
        self.bytes[7] == 0x80
    }

    pub fn is_nan(self) -> bool {
        self.to_f64().is_nan()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueKind {
    I32(u32),
    I64(u64),
    F32(F32Bytes),
    F64(F64Bytes),
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
            ValueKind::F64(_) => Valtype::F64,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum WasmRunnerResult {
    Values(Vec<Value>),
}
