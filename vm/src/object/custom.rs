pub use crate::prelude::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct CustomObject {
    inner: Rc<Mutex<HashMap<PtyStr, PettyObject>>>,
}

impl Object for CustomObject {
    fn type_id(&self) -> TypeId {
        todo!("custom objects need to have unique type ids")
    }
    fn get(&self, key: &str) -> PettyObject {
        let lock = self.inner.lock().unwrap();
        lock.get(key).unwrap_or(NULL).clone()
    }
    fn set(&self, key: PtyStr, val: PettyObject) {
        let mut lock = self.inner.lock().unwrap();
        lock.insert(key, val);
    }
}
