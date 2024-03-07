use crate::prelude::*;

pub type RawFunc = fn(&Vm, FnArgs) -> PettyObject;

impl Object for RawFunc {
    fn call(&self, vm: &Vm, args: FnArgs) -> PettyObject {
        self(vm, args)
    }
}
