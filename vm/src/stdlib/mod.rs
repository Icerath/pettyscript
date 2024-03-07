pub mod print;

use crate::prelude::*;

#[derive(Debug, Clone)]
pub enum StdObject {}

impl Object for StdObject {}

pub fn init(vm: &Vm) {
    let mut vars = vm.variables.borrow_mut();
    vars.insert(ptystr!("print"), PettyObject::RawFunc(print::print));
}
