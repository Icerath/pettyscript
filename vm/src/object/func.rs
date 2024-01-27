use crate::prelude::*;

pub type RawFunc = fn(FnArgs) -> PettyObject;

impl Object for RawFunc {
    fn call(&self, args: FnArgs) -> PettyObject {
        self(args)
    }
}
