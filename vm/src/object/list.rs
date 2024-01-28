use crate::prelude::*;

#[derive(Debug, Clone)]
pub struct List {
    pub inner: Arc<Mutex<Vec<PettyObject>>>,
}

impl Object for List {}
