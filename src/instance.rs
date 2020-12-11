use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::executor::*;
use crate::module::*;
use crate::types::*;
use crate::value::*;

#[derive(Debug)]
struct NameTable {
    table: HashMap<(Option<Name>, Name), Extarnval>,
}

impl NameTable {
    fn new() -> Self {
        Self {
            table: HashMap::new(),
        }
    }

    fn add(
        &mut self,
        module_name: Option<Name>,
        content_name: Name,
        content: Extarnval,
    ) -> Option<Extarnval> {
        // @todo fix to return old values pair
        if let Some(_) = module_name {
            self.table
                .insert((None, content_name.make_clone()), content.clone());
        }
        self.table.insert((module_name, content_name), content)
    }

    fn resolve(&self, module_name: Option<&Name>, content_name: &Name) -> Option<&Extarnval> {
        let result = self.table.get(&(
            module_name.map(|name| name.make_clone()),
            content_name.make_clone(),
        ));
        if result.is_some() || module_name.is_none() {
            return result;
        }
        self.table.get(&(None, content_name.make_clone()))
    }
}

#[derive(Debug)]
pub struct Store {
    funcs: Vec<Funcinst>,
    tables: Vec<Tableinst>,
    mems: Vec<Meminst>,
    globals: Vec<Globalinst>,
    name_table: NameTable,
}

impl Store {
    pub fn new() -> Self {
        Self {
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            name_table: NameTable::new(),
        }
    }

    pub fn instantiate(
        &mut self,
        module: &Module,
        initial_global_values: Vec<Value>,
    ) -> Result<Moduleinst, ExecutionError> {
        let moduleinst = self.allocmodule(module, initial_global_values)?;
        moduleinst.update_name_table(
            module.name().map(|name| name.make_clone()),
            &mut self.name_table,
        );
        Ok(moduleinst)
    }

    pub fn instantiate_with_imported_globals(
        &mut self,
        module: &Module,
    ) -> Result<Moduleinst, ExecutionError> {
        let mut moduleinst = Moduleinst::new();
        let mut imported_globals = Vec::new();
        for import in module.imports() {
            let content = self
                .name_table
                .resolve(Some(import.module()), import.name())
                .unwrap(); // @todo
            match (content, import.desc()) {
                (Extarnval::Func(_), Importdesc::Func(_)) => (),
                (Extarnval::Table(_), Importdesc::Table(_)) => (),
                (Extarnval::Mem(_), Importdesc::Mem(_)) => (),
                (Extarnval::Global(addr), Importdesc::Global(_)) => imported_globals.push(*addr),
                _ => unimplemented!(),
            }
        }
        moduleinst.update_globaladdrs(imported_globals);
        Ok(moduleinst)
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

    pub fn mems(&self) -> &Vec<Meminst> {
        &self.mems
    }

    pub fn mems_mut(&mut self) -> &mut Vec<Meminst> {
        &mut self.mems
    }

    pub fn globals(&self) -> &Vec<Globalinst> {
        &self.globals
    }

    pub fn globals_mut(&mut self) -> &mut Vec<Globalinst> {
        &mut self.globals
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
        let funcinst = Funcinst::UserDefined {
            typ,
            module: moduleinst,
            code: func,
        };
        self.funcs.push(funcinst);
        Ok(addr)
    }

    pub fn allochostfunc(
        &mut self,
        functype: Functype,
        hostfunc: Hostfunc,
    ) -> Result<Funcaddr, ExecutionError> {
        let addr = Funcaddr(Address(self.funcs.len()));
        let funcinst = Funcinst::Host {
            typ: functype,
            hostcode: hostfunc,
        };
        self.funcs.push(funcinst);
        Ok(addr)
    }

    pub fn alloctable(&mut self, tabletype: &Tabletype) -> Result<Tableaddr, ExecutionError> {
        let addr = Tableaddr(Address(self.tables.len()));
        let elem = vec![None; tabletype.limit().min() as usize];
        let tableinst = Tableinst::new(elem, *tabletype.limit().max());
        self.tables.push(tableinst);
        Ok(addr)
    }

    pub fn allocmem(&mut self, memtype: &Memtype) -> Result<Memaddr, ExecutionError> {
        let addr = Memaddr(Address(self.mems.len()));
        let n = memtype.limit().min() as usize;
        let m = *memtype.limit().max();
        let data = vec![0u8; n * PAGE_SIZE];
        let meminst = Meminst::new(data, m);
        self.mems.push(meminst);
        Ok(addr)
    }

    pub fn allocglobal(
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

        let mut funcaddrs_mod = Vec::new();
        let mut tableaddrs_mod = Vec::new();
        let mut memaddrs_mod = Vec::new();
        let mut globaladdrs_mod = Vec::new();
        for import in module.imports() {
            let content = self
                .name_table
                .resolve(Some(import.module()), import.name())
                .unwrap(); // @todo
            match (content, import.desc()) {
                (Extarnval::Func(addr), Importdesc::Func(_)) => funcaddrs_mod.push(*addr),
                (Extarnval::Table(addr), Importdesc::Table(_)) => tableaddrs_mod.push(*addr),
                (Extarnval::Mem(addr), Importdesc::Mem(_)) => memaddrs_mod.push(*addr),
                (Extarnval::Global(addr), Importdesc::Global(_)) => globaladdrs_mod.push(*addr),
                _ => unimplemented!(),
            }
        }

        funcaddrs_mod.append(&mut funcaddrs);
        tableaddrs_mod.append(&mut tableaddrs);
        memaddrs_mod.append(&mut memaddrs);
        globaladdrs_mod.append(&mut globaladdrs);

        let mut exports = Vec::new();
        for export in module.exports() {
            use Exportdesc::*;
            let value = match export.desc() {
                Func(funcidx) => Extarnval::Func(funcaddrs_mod[funcidx.to_usize()]),
                Table(tableidx) => Extarnval::Table(tableaddrs_mod[tableidx.to_usize()]),
                Mem(memidx) => Extarnval::Mem(memaddrs_mod[memidx.to_usize()]),
                Global(globalidx) => Extarnval::Global(globaladdrs_mod[globalidx.to_usize()]),
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

    pub fn resolve(&self, module_name: Option<&Name>, content_name: &Name) -> Option<&Extarnval> {
        self.name_table.resolve(module_name, content_name)
    }

    pub fn register_content(
        &mut self,
        module_name: Option<Name>,
        content_name: Name,
        content: Extarnval,
    ) -> Option<Extarnval> {
        self.name_table.add(module_name, content_name, content)
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
        Ok(self.0.borrow().funcaddrs[funcidx.to_usize()])
    }

    pub fn resolve_tableaddr(&self, tableidx: Tableidx) -> Result<Tableaddr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().tableaddrs[tableidx.to_usize()])
    }

    pub fn resolve_memaddr(&self, memidx: Memidx) -> Result<Memaddr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().memaddrs[memidx.to_usize()])
    }

    pub fn resolve_globaladdr(&self, globalidx: Globalidx) -> Result<Globaladdr, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().globaladdrs[globalidx.to_usize()])
    }

    pub fn resolve_type(&self, typeidx: Typeidx) -> Result<Functype, ExecutionError> {
        // @todo check index
        Ok(self.0.borrow().types[typeidx.to_usize()].make_clone())
    }

    fn update_name_table(&self, module_name: Option<Name>, name_table: &mut NameTable) {
        for exportinst in self.0.borrow().exports.iter() {
            name_table.add(
                module_name.as_ref().map(|name| name.make_clone()),
                exportinst.name().make_clone(),
                exportinst.value().clone(),
            );
        }
    }

    pub fn extract_exported_contents(&self) -> Vec<(Name, Extarnval)> {
        self.0
            .borrow()
            .exports
            .iter()
            .map(|exportinst| (exportinst.name().make_clone(), exportinst.value().clone()))
            .collect()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Hostfunc {
    code: fn(Vec<Value>) -> Result<WasmRunnerResult, ExecutionError>,
}

impl Hostfunc {
    pub fn new(code: fn(Vec<Value>) -> Result<WasmRunnerResult, ExecutionError>) -> Self {
        Self { code }
    }

    pub fn code(&self) -> fn(Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
        self.code
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Funcinst {
    UserDefined {
        typ: Functype,
        module: Moduleinst,
        code: Func,
    },
    Host {
        typ: Functype,
        hostcode: Hostfunc,
    },
}

impl Funcinst {
    pub fn typ(&self) -> &Functype {
        match self {
            Self::UserDefined { typ, .. } => &typ,
            Self::Host { typ, .. } => &typ,
        }
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

    pub fn size(&self) -> usize {
        self.data.len()
    }

    pub fn size_in_page(&self) -> usize {
        let len = self.data.len();
        assert!(len % PAGE_SIZE == 0);
        len / PAGE_SIZE
    }

    fn read_n(&self, buf: &mut [u8], buflen: usize, index: usize) -> Result<(), ExecutionError> {
        if index + buflen > self.data.len() {
            return Err(ExecutionError::OutOfBoundsMemoryAccess);
        }
        buf[..buflen].clone_from_slice(&self.data[index..(index + buflen)]);
        Ok(())
    }

    fn write_n(&mut self, index: usize, buf: &[u8], buflen: usize) -> Result<(), ExecutionError> {
        if index + buflen > self.data.len() {
            return Err(ExecutionError::OutOfBoundsMemoryAccess);
        }
        for (i, &b) in buf.iter().enumerate() {
            self.data[index + i] = b;
        }
        Ok(())
    }

    fn read1(&self, index: usize) -> Result<[u8; 1], ExecutionError> {
        let mut bytes = [0u8; 1];
        self.read_n(&mut bytes, 1, index)?;
        Ok(bytes)
    }

    fn write1(&mut self, index: usize, bytes: [u8; 1]) -> Result<(), ExecutionError> {
        self.write_n(index, &bytes, 1)
    }

    fn read2(&self, index: usize) -> Result<[u8; 2], ExecutionError> {
        let mut bytes = [0u8; 2];
        self.read_n(&mut bytes, 2, index)?;
        Ok(bytes)
    }

    fn write2(&mut self, index: usize, bytes: [u8; 2]) -> Result<(), ExecutionError> {
        self.write_n(index, &bytes, 2)
    }

    fn read4(&self, index: usize) -> Result<[u8; 4], ExecutionError> {
        let mut bytes = [0u8; 4];
        self.read_n(&mut bytes, 4, index)?;
        Ok(bytes)
    }

    fn write4(&mut self, index: usize, bytes: [u8; 4]) -> Result<(), ExecutionError> {
        self.write_n(index, &bytes, 4)
    }

    fn read8(&self, index: usize) -> Result<[u8; 8], ExecutionError> {
        let mut bytes = [0u8; 8];
        self.read_n(&mut bytes, 8, index)?;
        Ok(bytes)
    }

    fn write8(&mut self, index: usize, bytes: [u8; 8]) -> Result<(), ExecutionError> {
        self.write_n(index, &bytes, 8)
    }

    pub fn read_i8(&self, index: usize) -> Result<u8, ExecutionError> {
        Ok(u8::from_le_bytes(self.read1(index)?))
    }

    pub fn write_i8(&mut self, index: usize, value: u8) -> Result<(), ExecutionError> {
        self.write1(index, value.to_le_bytes())
    }

    pub fn read_i16(&self, index: usize) -> Result<u16, ExecutionError> {
        Ok(u16::from_le_bytes(self.read2(index)?))
    }

    pub fn write_i16(&mut self, index: usize, value: u16) -> Result<(), ExecutionError> {
        self.write2(index, value.to_le_bytes())
    }

    pub fn read_i32(&self, index: usize) -> Result<u32, ExecutionError> {
        Ok(u32::from_le_bytes(self.read4(index)?))
    }

    pub fn write_i32(&mut self, index: usize, value: u32) -> Result<(), ExecutionError> {
        self.write4(index, value.to_le_bytes())
    }

    pub fn read_i64(&self, index: usize) -> Result<u64, ExecutionError> {
        Ok(u64::from_le_bytes(self.read8(index)?))
    }

    pub fn write_i64(&mut self, index: usize, value: u64) -> Result<(), ExecutionError> {
        self.write8(index, value.to_le_bytes())
    }

    pub fn read_f32(&self, index: usize) -> Result<F32Bytes, ExecutionError> {
        Ok(F32Bytes::from_bytes(self.read4(index)?))
    }

    pub fn write_f32(&mut self, index: usize, value: F32Bytes) -> Result<(), ExecutionError> {
        self.write4(index, value.to_bytes())
    }

    pub fn read_f64(&self, index: usize) -> Result<F64Bytes, ExecutionError> {
        Ok(F64Bytes::from_bytes(self.read8(index)?))
    }

    pub fn write_f64(&mut self, index: usize, value: F64Bytes) -> Result<(), ExecutionError> {
        self.write8(index, value.to_bytes())
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
        self.data.resize(self.data.len() + PAGE_SIZE * page_size, 0);
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

    pub fn update_value(&mut self, value: Value) {
        self.value = value
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Extarnval {
    Func(Funcaddr),
    Table(Tableaddr),
    Mem(Memaddr),
    Global(Globaladdr),
}
