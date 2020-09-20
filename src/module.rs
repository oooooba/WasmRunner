use std::rc::Rc;

use crate::instr::*;
use crate::types::*;

#[derive(Debug, PartialEq, Eq)]
pub struct Module {
    types: Vec<Functype>,
    funcs: Vec<Func>,
    tables: Vec<Table>,
    mems: Vec<Mem>,
    globals: Vec<Global>,
    exports: Vec<Export>,
    start: Option<Funcidx>,
    elems: Vec<Elem>,
    data: Vec<Data>,
}

impl Module {
    pub fn new(
        types: Vec<Functype>,
        funcs: Vec<Func>,
        tables: Vec<Table>,
        mems: Vec<Mem>,
        globals: Vec<Global>,
        exports: Vec<Export>,
        start: Option<Funcidx>,
        elems: Vec<Elem>,
        data: Vec<Data>,
    ) -> Self {
        Self {
            types,
            funcs,
            tables,
            mems,
            globals,
            exports,
            start,
            elems,
            data,
        }
    }

    pub fn types(&self) -> &Vec<Functype> {
        &self.types
    }

    pub fn funcs(&self) -> &Vec<Func> {
        &self.funcs
    }

    pub fn tables(&self) -> &Vec<Table> {
        &self.tables
    }

    pub fn mems(&self) -> &Vec<Mem> {
        &self.mems
    }

    pub fn globals(&self) -> &Vec<Global> {
        &self.globals
    }

    pub fn exports(&self) -> &Vec<Export> {
        &self.exports
    }

    pub fn elems(&self) -> &Vec<Elem> {
        &self.elems
    }

    pub fn data(&self) -> &Vec<Data> {
        &self.data
    }
}

#[allow(unused_macros)]
macro_rules! generate_idx {
    ($target:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $target(u32);

        impl $target {
            #[allow(dead_code)] // @todo remove
            pub fn new(i: u32) -> Self {
                $target(i)
            }

            #[allow(dead_code)] // @todo remove
            pub fn to_usize(self) -> usize {
                self.0 as usize
            }
        }
    };
}

generate_idx!(Localidx);
generate_idx!(Funcidx);
generate_idx!(Tableidx);
generate_idx!(Typeidx);
generate_idx!(Memidx);
generate_idx!(Globalidx);
generate_idx!(Labelidx);

#[derive(Debug, PartialEq, Eq)]
struct FuncInner {
    typ: Typeidx,
    locals: Vec<Valtype>,
    body: Expr,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Func(Rc<FuncInner>);

impl Func {
    pub fn new(typ: Typeidx, locals: Vec<Valtype>, body: Expr) -> Self {
        Self(Rc::new(FuncInner { typ, locals, body }))
    }

    pub fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }

    pub fn typ(&self) -> Typeidx {
        self.0.typ
    }

    pub fn locals(&self) -> &Vec<Valtype> {
        &self.0.locals
    }

    pub fn body(&self) -> &Expr {
        &self.0.body
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Table {
    typ: Tabletype,
}

impl Table {
    pub fn new(typ: Tabletype) -> Self {
        Self { typ }
    }

    pub fn typ(&self) -> &Tabletype {
        &self.typ
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Mem {
    typ: Memtype,
}

impl Mem {
    pub fn new(typ: Memtype) -> Self {
        Self { typ }
    }

    pub fn typ(&self) -> &Memtype {
        &self.typ
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Global {
    typ: Globaltype,
    init: Expr,
}

impl Global {
    pub fn new(typ: Globaltype, init: Expr) -> Self {
        Self { typ, init }
    }

    pub fn typ(&self) -> &Globaltype {
        &self.typ
    }

    pub fn init(&self) -> &Expr {
        &self.init
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Data {
    data: Memidx,
    offset: Expr,
    init: Vec<u8>,
}

impl Data {
    pub fn new(data: Memidx, offset: Expr, init: Vec<u8>) -> Self {
        Self { data, offset, init }
    }

    pub fn data(&self) -> Memidx {
        self.data
    }

    pub fn offset(&self) -> &Expr {
        &self.offset
    }

    pub fn init(&self) -> &Vec<u8> {
        &self.init
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Export {
    name: Name,
    desc: Exportdesc,
}

impl Export {
    pub fn new(name: Name, desc: Exportdesc) -> Self {
        Self { name, desc }
    }

    pub fn name(&self) -> &Name {
        &self.name
    }

    pub fn desc(&self) -> &Exportdesc {
        &self.desc
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Exportdesc {
    Funcidx(Funcidx),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Elem {
    table: Tableidx,
    offset: Expr,
    init: Vec<Funcidx>,
}

impl Elem {
    pub fn new(table: Tableidx, offset: Expr, init: Vec<Funcidx>) -> Self {
        Self {
            table,
            offset,
            init,
        }
    }

    pub fn table(&self) -> Tableidx {
        self.table
    }

    pub fn offset(&self) -> &Expr {
        &self.offset
    }

    pub fn init(&self) -> &Vec<Funcidx> {
        &self.init
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Name(Rc<String>);

impl Name {
    pub fn new(s: String) -> Self {
        Self(Rc::new(s))
    }

    pub fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}
