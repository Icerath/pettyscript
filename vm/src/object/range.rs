use std::ops;

use crate::prelude::*;

pub type Range = Rc<RefCell<ops::Range<Int>>>;
pub type RangeInclusive = Rc<RefCell<ops::RangeInclusive<Int>>>;

impl From<ops::Range<Int>> for PettyObject {
    fn from(value: ops::Range<Int>) -> Self {
        Rc::new(RefCell::new(value)).into()
    }
}

impl From<ops::RangeInclusive<Int>> for PettyObject {
    fn from(value: ops::RangeInclusive<Int>) -> Self {
        Rc::new(RefCell::new(value)).into()
    }
}

impl Object for Range {
    fn get(&self, _vm: &Vm, key: &str) -> PettyObject {
        match key {
            "__iter__" => self.clone().into(),
            "__next__" => self.borrow_mut().next().map_or(NULL, Into::into),
            _ => todo!("{key:?}"),
        }
    }
}

impl Object for RangeInclusive {
    fn get(&self, _vm: &Vm, key: &str) -> PettyObject {
        match key {
            "__iter__" => self.clone().into(),
            "__next__" => self.borrow_mut().next().map_or(NULL, Into::into),
            _ => todo!(),
        }
    }
}
