use std::collections::HashMap;

pub use crate::prelude::*;

#[derive(Debug, Clone)]
pub struct CustomObject {
    inner: Rc<RefCell<HashMap<PtyStr, PettyObject>>>,
}

impl Object for CustomObject {
    fn type_id(&self) -> TypeId {
        todo!("custom objects need to have unique type ids")
    }

    fn get(&self, _vm: &Vm, key: &str) -> PettyObject {
        self.inner.borrow().get(key).unwrap_or(&NULL).clone()
    }

    fn set(&self, _vm: &Vm, key: PtyStr, val: PettyObject) {
        self.inner.borrow_mut().insert(key, val);
    }
}
