use crate::ast::node::Block;
use crate::prelude::*;

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
        PettyObject::NULL
    }
}
