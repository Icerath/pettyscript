use crate::ast::node::Block;
use crate::prelude::*;
use crate::run::ControlFlow;

#[derive(Debug, Clone)]
pub struct Func {
    pub params: Box<[PtyStr]>,
    pub body: Block,
}

impl Object for Rc<Func> {
    fn call(&self, vm: &Vm, args: FnArgs) -> PettyObject {
        for (name, val) in self.params.iter().zip(args.slice) {
            vm.variables.borrow_mut().insert(name.clone(), val.clone());
        }
        match &self.body {
            Block::Multi(nodes) => vm.exec_many(nodes),
            Block::Single(expr) => _ = vm.eval(expr),
        }
        match vm.control_flow.borrow_mut().take() {
            Some(ControlFlow::Return(obj)) => obj,
            _ => PettyObject::NULL,
        }
    }
}
