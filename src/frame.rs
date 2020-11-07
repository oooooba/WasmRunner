use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use crate::executor::*;
use crate::instance::*;
use crate::instr::*;
use crate::module::*;
use crate::types::*;
use crate::value::*;

struct FrameInner {
    locals: Vec<Value>,
    module: Option<Moduleinst>,
    num_result: usize,
}

pub struct Frame(Rc<RefCell<FrameInner>>);

impl Frame {
    pub fn new(locals: Vec<Value>, num_result: usize, module: Option<Moduleinst>) -> Self {
        Self(Rc::new(RefCell::new(FrameInner {
            locals,
            module,
            num_result,
        })))
    }

    pub fn resolve_funcaddr(&self, funcidx: Funcidx) -> Result<Funcaddr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_funcaddr(funcidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_tableaddr(&self, tableidx: Tableidx) -> Result<Tableaddr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_tableaddr(tableidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_memaddr(&self, memidx: Memidx) -> Result<Memaddr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_memaddr(memidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_globaladdr(&self, globalidx: Globalidx) -> Result<Globaladdr, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_globaladdr(globalidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn resolve_type(&self, typeidx: Typeidx) -> Result<Functype, ExecutionError> {
        match self.0.borrow().module.as_ref() {
            Some(moduleinst) => moduleinst.resolve_type(typeidx),
            None => Err(ExecutionError::ExecutorStateInconsistency(
                "module instance is not created",
            )),
        }
    }

    pub fn num_result(&self) -> usize {
        self.0.borrow().num_result
    }

    pub fn make_clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }

    pub fn get(&self, idx: Localidx) -> Result<Value, ExecutionError> {
        let idx = idx.to_usize();
        let locals = &self.0.borrow().locals;
        if idx < locals.len() {
            Ok(locals[idx])
        } else {
            Err(ExecutionError::OutOfRangeAccess {
                size: locals.len(),
                index: idx,
                detail: "Local/Get",
            })
        }
    }

    pub fn set(&mut self, idx: Localidx, val: Value) -> Result<(), ExecutionError> {
        let idx = idx.to_usize();
        let locals = &mut self.0.borrow_mut().locals;
        if idx < locals.len() {
            locals[idx] = val;
            Ok(())
        } else {
            Err(ExecutionError::OutOfRangeAccess {
                size: locals.len(),
                index: idx,
                detail: "Local/Set",
            })
        }
    }

    pub fn expand_blocktype(&self, blocktype: &Blocktype) -> Result<Functype, ExecutionError> {
        use Blocktype::*;
        match blocktype {
            Empty => Ok(Functype::new(
                Resulttype::new(vec![]),
                Resulttype::new(vec![]),
            )),
            Valtype(valtype) => Ok(Functype::new(
                Resulttype::new(vec![]),
                Resulttype::new(vec![valtype.clone()]),
            )),
            S33(x) => self.0.borrow().module.as_ref().unwrap().resolve_type(*x),
        }
    }
}

impl fmt::Debug for Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Frame [{:p}]", self.0)
    }
}

impl PartialEq for Frame {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Frame {}
