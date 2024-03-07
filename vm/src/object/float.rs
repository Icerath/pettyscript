use crate::prelude::*;

pub type Float = f64;

impl Object for Float {
    fn get(&self, _: &Vm, key: &str) -> PettyObject {
        match key {
            "__repr__" => PettyObject::RawFunc(__repr__),
            _ => unimplemented!("{key:?}"),
        }
    }
}

#[pettyfunc]
fn __repr__(this: Float) -> PtyStr {
    this.to_string().into()
}
