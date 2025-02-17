use std::ops::Deref;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Valtype {
    I32,
    I64,
    F32,
    F64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resulttype(Vec<Valtype>);

impl Resulttype {
    pub fn new(valtypes: Vec<Valtype>) -> Self {
        Self(valtypes)
    }
}

impl Deref for Resulttype {
    type Target = Vec<Valtype>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, PartialEq, Eq)]
struct FunctypeInner {
    param_type: Resulttype,
    return_type: Resulttype,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Functype(Rc<FunctypeInner>);

impl Functype {
    pub fn new(param_type: Resulttype, return_type: Resulttype) -> Self {
        Self(Rc::new(FunctypeInner {
            param_type,
            return_type,
        }))
    }

    pub fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }

    pub fn param_type(&self) -> &Resulttype {
        &self.0.param_type
    }

    pub fn return_type(&self) -> &Resulttype {
        &self.0.return_type
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Limit {
    min: u32,
    max: Option<u32>,
}

impl Limit {
    pub fn new(min: u32, max: Option<u32>) -> Self {
        Self { min, max }
    }

    pub fn min(&self) -> u32 {
        self.min
    }

    pub fn max(&self) -> &Option<u32> {
        &self.max
    }

    pub fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (Limit { min: n1, .. }, Limit { min: n2, max: None }) if n1 >= n2 => true,
            (
                Limit {
                    min: n1,
                    max: Some(m1),
                },
                Limit {
                    min: n2,
                    max: Some(m2),
                },
            ) if n1 >= n2 && m1 <= m2 => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Memtype {
    limit: Limit,
}

impl Memtype {
    pub fn new(limit: Limit) -> Self {
        Self { limit }
    }

    pub fn limit(&self) -> &Limit {
        &self.limit
    }

    pub fn matches(&self, other: &Self) -> bool {
        self.limit.matches(other.limit())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tabletype {
    limit: Limit,
    elemtype: Elemtype,
}

impl Tabletype {
    pub fn new(limit: Limit, elemtype: Elemtype) -> Self {
        Self { limit, elemtype }
    }

    pub fn limit(&self) -> &Limit {
        &self.limit
    }

    pub fn elemtype(&self) -> &Elemtype {
        &self.elemtype
    }

    pub fn matches(&self, other: &Self) -> bool {
        self.limit.matches(other.limit()) && self.elemtype.matches(other.elemtype())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elemtype {
    Funcref,
}

impl Elemtype {
    pub fn matches(&self, other: &Self) -> bool {
        self == other
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Globaltype {
    typ: Valtype,
    mutability: Mutability,
}

impl Globaltype {
    pub fn new(typ: Valtype, mutability: Mutability) -> Self {
        Self { typ, mutability }
    }

    pub fn typ(&self) -> &Valtype {
        &self.typ
    }

    pub fn mutability(&self) -> &Mutability {
        &self.mutability
    }

    pub fn matches(&self, other: &Self) -> bool {
        self == other
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mutability {
    Const,
    Var,
}
