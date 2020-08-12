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

    pub fn instantiate(&mut self, module: &Module) -> Result<Moduleinst, ExecutionError> {
        self.allocmodule(module)
    }

    pub fn funcs(&self) -> &Vec<Funcinst> {
        &self.funcs
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
        let elem = vec![None; tabletype.limit().min()];
        let tableinst = Tableinst::new(elem, tabletype.limit().max().clone());
        self.tables.push(tableinst);
        Ok(addr)
    }

    fn allocmodule(&mut self, module: &Module) -> Result<Moduleinst, ExecutionError> {
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

        let funcaddrs_mod = funcaddrs; // @todo concatenate with externals

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

    fn update_exports(&mut self, exports: Vec<Exportinst>) {
        self.0.borrow_mut().exports = exports;
    }

    pub fn resolve_funcaddr(&self, funcidx: Funcidx) -> Result<Funcaddr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().funcaddrs[funcidx.to_usize()].clone())
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
    max: Option<usize>,
}

impl Tableinst {
    pub fn new(elem: Vec<Option<Funcaddr>>, max: Option<usize>) -> Self {
        Self { elem, max }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Meminst {
    data: Vec<u8>,
    max: Option<u32>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Globalinst {
    value: Value,
    mutability: Mutability,
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
