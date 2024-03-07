use crate::prelude::*;

pub type Bool = bool;

impl Object for Bool {
    fn get(&self, _: &Vm, key: &str) -> PettyObject {
        match key {
            "__bool__" => PettyObject::RawFunc(__bool__),
            "__repr__" => PettyObject::RawFunc(__repr__),
            _ => unimplemented!(),
        }
    }
}

#[pettyfunc]
pub fn __bool__(this: Bool) -> Bool {
    *this
}

#[pettyfunc]
pub fn __repr__(this: Bool) -> PtyStr {
    match this {
        true => ptystr!("true"),
        false => ptystr!("false"),
    }
}
