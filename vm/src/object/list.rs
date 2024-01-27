use crate::prelude::*;

#[derive(Debug, Clone)]
pub struct List {
    pub inner: Rc<Mutex<Vec<PettyObject>>>,
}

impl Object for List {}
