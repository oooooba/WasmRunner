use std::cell::RefCell;
use std::rc::Rc;

use crate::executor::*;
use crate::module::*;
use crate::types::*;
use crate::value::*;

#[derive(Debug, PartialEq, Eq)]
pub struct Store {
    funcs: Vec<Funcinst>,
    tables: Vec<Tableinst>,
    mems: Vec<Meminst>,
    globals: Vec<Globalinst>,
}

impl Store {
    pub fn new() -> Self {
        Self {
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
        }
    }

    pub fn instantiate(
        &mut self,
        module: &Module,
        initial_global_values: Vec<Value>,
    ) -> Result<Moduleinst, ExecutionError> {
        self.allocmodule(module, initial_global_values)
    }

    pub fn funcs(&self) -> &Vec<Funcinst> {
        &self.funcs
    }

    pub fn tables(&self) -> &Vec<Tableinst> {
        &self.tables
    }

    pub fn tables_mut(&mut self) -> &mut Vec<Tableinst> {
        &mut self.tables
    }

    pub fn mems_mut(&mut self) -> &mut Vec<Meminst> {
        &mut self.mems
    }

    pub fn globals(&self) -> &Vec<Globalinst> {
        &self.globals
    }

    fn allocfunc(
        &mut self,
        func: Func,
        moduleinst: Moduleinst,
        module: &Module,
    ) -> Result<Funcaddr, ExecutionError> {
        let addr = Funcaddr(Address(self.funcs.len()));
        let index = func.typ().to_usize();
        if index >= module.types().len() {
            return Err(ExecutionError::InstantiationFailure(format!(
                "invalid type index {}",
                index
            )));
        }
        let typ = module.types()[index].make_clone();
        let funcinst = Funcinst::new(typ, func, moduleinst);
        self.funcs.push(funcinst);
        Ok(addr)
    }

    fn alloctable(&mut self, tabletype: &Tabletype) -> Result<Tableaddr, ExecutionError> {
        let addr = Tableaddr(Address(self.tables.len()));
        let elem = vec![None; tabletype.limit().min() as usize];
        let tableinst = Tableinst::new(elem, tabletype.limit().max().clone());
        self.tables.push(tableinst);
        Ok(addr)
    }

    fn allocmem(&mut self, memtype: &Memtype) -> Result<Memaddr, ExecutionError> {
        let addr = Memaddr(Address(self.mems.len()));
        let n = memtype.limit().min() as usize;
        let m = memtype.limit().max().clone();
        let data = vec![0u8; n * PAGE_SIZE];
        let meminst = Meminst::new(data, m);
        self.mems.push(meminst);
        Ok(addr)
    }

    fn allocglobal(
        &mut self,
        globaltype: &Globaltype,
        val: Value,
    ) -> Result<Globaladdr, ExecutionError> {
        let addr = Globaladdr(Address(self.globals.len()));
        let mutability = globaltype.mutability().clone();
        let globalinst = Globalinst::new(val, mutability);
        self.globals.push(globalinst);
        Ok(addr)
    }

    fn allocmodule(
        &mut self,
        module: &Module,
        initial_global_values: Vec<Value>,
    ) -> Result<Moduleinst, ExecutionError> {
        let mut moduleinst = Moduleinst::new();

        let types = module.types().iter().map(|t| t.make_clone()).collect();

        let mut funcaddrs = Vec::new();
        for func in module.funcs() {
            let addr = self.allocfunc(func.make_clone(), moduleinst.make_clone(), module)?;
            funcaddrs.push(addr);
        }

        let mut tableaddrs = Vec::new();
        for table in module.tables() {
            let addr = self.alloctable(table.typ())?;
            tableaddrs.push(addr);
        }

        let mut memaddrs = Vec::new();
        for mem in module.mems() {
            let addr = self.allocmem(mem.typ())?;
            memaddrs.push(addr);
        }

        let mut globaladdrs = Vec::new();
        for (i, global) in module.globals().iter().enumerate() {
            let addr = self.allocglobal(global.typ(), initial_global_values[i])?;
            globaladdrs.push(addr);
        }

        let funcaddrs_mod = funcaddrs; // @todo concatenate with externals

        let tableaddrs_mod = tableaddrs; // @todo concatenate with externals

        let memaddrs_mod = memaddrs; // @todo concatenate with externals

        let globaladdrs_mod = globaladdrs; // @todo concatenate with externals

        let mut exports = Vec::new();
        for export in module.exports() {
            use Exportdesc::*;
            let value = match export.desc() {
                Funcidx(funcidx) => Extarnval::Func(funcaddrs_mod[funcidx.to_usize()].clone()),
            };
            let name = export.name().make_clone();
            let exportinst = Exportinst::new(name, value);
            exports.push(exportinst);
        }

        moduleinst.update_types(types);
        moduleinst.update_funcaddrs(funcaddrs_mod);
        moduleinst.update_tableaddrs(tableaddrs_mod);
        moduleinst.update_memaddrs(memaddrs_mod);
        moduleinst.update_globaladdrs(globaladdrs_mod);
        moduleinst.update_exports(exports);

        Ok(moduleinst)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Address(usize);

#[allow(unused_macros)]
macro_rules! generate_addr {
    ($target:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $target(Address);

        impl $target {
            #[allow(dead_code)] // @todo remove
            pub fn new(a: Address) -> Self {
                $target(a)
            }

            #[allow(dead_code)] // @todo remove
            pub fn to_usize(self) -> usize {
                (self.0).0
            }
        }
    };
}

generate_addr!(Funcaddr);
generate_addr!(Tableaddr);
generate_addr!(Memaddr);
generate_addr!(Globaladdr);

#[derive(Debug, PartialEq, Eq)]
struct ModuleinstInner {
    types: Vec<Functype>,
    funcaddrs: Vec<Funcaddr>,
    tableaddrs: Vec<Tableaddr>,
    memaddrs: Vec<Memaddr>,
    globaladdrs: Vec<Globaladdr>,
    exports: Vec<Exportinst>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Moduleinst(Rc<RefCell<ModuleinstInner>>);

impl Moduleinst {
    fn new() -> Self {
        Self(Rc::new(RefCell::new(ModuleinstInner {
            types: Vec::new(),
            funcaddrs: Vec::new(),
            tableaddrs: Vec::new(),
            memaddrs: Vec::new(),
            globaladdrs: Vec::new(),
            exports: Vec::new(),
        })))
    }

    pub fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }

    fn update_types(&mut self, types: Vec<Functype>) {
        self.0.borrow_mut().types = types;
    }

    fn update_funcaddrs(&mut self, funcaddrs: Vec<Funcaddr>) {
        self.0.borrow_mut().funcaddrs = funcaddrs;
    }

    fn update_tableaddrs(&mut self, tableaddrs: Vec<Tableaddr>) {
        self.0.borrow_mut().tableaddrs = tableaddrs;
    }

    fn update_memaddrs(&mut self, memaddrs: Vec<Memaddr>) {
        self.0.borrow_mut().memaddrs = memaddrs;
    }

    fn update_globaladdrs(&mut self, globaladdrs: Vec<Globaladdr>) {
        self.0.borrow_mut().globaladdrs = globaladdrs;
    }

    fn update_exports(&mut self, exports: Vec<Exportinst>) {
        self.0.borrow_mut().exports = exports;
    }

    pub fn resolve_funcaddr(&self, funcidx: Funcidx) -> Result<Funcaddr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().funcaddrs[funcidx.to_usize()].clone())
    }

    pub fn resolve_tableaddr(&self, tableidx: Tableidx) -> Result<Tableaddr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().tableaddrs[tableidx.to_usize()].clone())
    }

    pub fn resolve_memaddr(&self, memidx: Memidx) -> Result<Memaddr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().memaddrs[memidx.to_usize()].clone())
    }

    pub fn resolve_globaladdr(&self, globalidx: Globalidx) -> Result<Globaladdr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().globaladdrs[globalidx.to_usize()].clone())
    }

    pub fn resolve_type(&self, typeidx: Typeidx) -> Result<Functype, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().types[typeidx.to_usize()].make_clone())
    }

    pub fn find_funcaddr(&self, name: &Name) -> Option<Funcaddr> {
        for export in self.0.borrow().exports.iter() {
            match export.value() {
                Extarnval::Func(funcaddr) => {
                    if export.name() == name {
                        return Some(*funcaddr);
                    }
                }
            }
        }
        None
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Funcinst {
    typ: Functype,
    module: Moduleinst,
    code: Func,
}

impl Funcinst {
    fn new(typ: Functype, code: Func, module: Moduleinst) -> Self {
        Self { typ, module, code }
    }

    pub fn typ(&self) -> &Functype {
        &self.typ
    }

    pub fn module(&self) -> &Moduleinst {
        &self.module
    }

    pub fn code(&self) -> &Func {
        &self.code
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Tableinst {
    elem: Vec<Option<Funcaddr>>,
    max: Option<u32>,
}

impl Tableinst {
    pub fn new(elem: Vec<Option<Funcaddr>>, max: Option<u32>) -> Self {
        Self { elem, max }
    }

    pub fn elem(&self) -> &Vec<Option<Funcaddr>> {
        &self.elem
    }

    pub fn elem_mut(&mut self) -> &mut Vec<Option<Funcaddr>> {
        &mut self.elem
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Meminst {
    data: Vec<u8>,
    max: Option<u32>,
}

impl Meminst {
    pub fn new(data: Vec<u8>, max: Option<u32>) -> Self {
        Self { data, max }
    }

    pub fn write_i32(&mut self, index: usize, value: u32) -> Result<(), ExecutionError> {
        let bs = value.to_le_bytes();
        if index + bs.len() > self.data.len() {
            unimplemented!() // @todo raise Error
        }
        for (i, &b) in bs.iter().enumerate() {
            self.data[index + i] = b;
        }
        Ok(())
    }

    pub fn grow(&mut self, page_size: usize) -> Result<Option<u32>, ExecutionError> {
        if self.data.len() % PAGE_SIZE != 0 {
            unimplemented!() // @todo raise Error
        }
        let sz = self.data.len() / PAGE_SIZE;
        let len = sz + page_size;
        if len > 2usize.pow(16) {
            return Ok(None);
        }
        if let Some(max) = self.max {
            if (max as usize) < len {
                return Ok(None);
            }
        }
        for _ in 0..(PAGE_SIZE * len) {
            self.data.push(0);
        }
        Ok(Some(sz as u32))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Globalinst {
    value: Value,
    mutability: Mutability,
}

impl Globalinst {
    pub fn new(value: Value, mutability: Mutability) -> Self {
        Self { value, mutability }
    }

    pub fn value(&self) -> Value {
        self.value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Exportinst {
    name: Name,
    value: Extarnval,
}

impl Exportinst {
    fn new(name: Name, value: Extarnval) -> Self {
        Self { name, value }
    }

    pub fn name(&self) -> &Name {
        &self.name
    }

    pub fn value(&self) -> &Extarnval {
        &self.value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Extarnval {
    Func(Funcaddr),
}
