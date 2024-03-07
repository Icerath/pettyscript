use core::fmt;

use crate::prelude::*;

#[derive(Debug, Clone)]
pub struct List {
    pub inner: Rc<RefCell<Vec<PettyObject>>>,
}

impl List {
    #[must_use]
    pub fn new(vals: Vec<PettyObject>) -> Self {
        Self { inner: Rc::new(RefCell::new(vals)) }
    }
}

impl Object for List {
    fn get(&self, _: &Vm, key: &str) -> PettyObject {
        match key {
            "__repr__" => PettyObject::RawFunc(__repr__),
            _ => unimplemented!("{key:?}"),
        }
    }
}

#[pettyfunc]
pub fn __repr__(this: List) -> PtyStr {
    // Hack to Vec's debug impl
    struct Repr(PtyStr);
    impl fmt::Debug for Repr {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }
    let reprs = this
        .inner
        .borrow()
        .iter()
        .collect::<Vec<_>>()
        .into_iter()
        .map(|elem| elem.get(vm, "__repr__").call(vm, FnArgs::new(&[elem.clone()])))
        .map(|repr| match repr {
            PettyObject::PtyStr(str) => str,
            _ => unreachable!("__repr__ Should always return a str"),
        })
        .map(Repr)
        .collect::<Vec<_>>();

    format!("{reprs:?}").into()
}
