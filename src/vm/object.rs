use std::{any::Any, fmt, ops::Deref};

use crate::slim_rc::Rc;

use super::{core::Vm, function_args::FuncArgs};

pub trait PettyObjectType: fmt::Display {
    fn get_item(&self, vm: &mut Vm, this: PettyObject, str: &str) -> PettyObject;
    fn call(&self, vm: &mut Vm, this: PettyObject, args: FuncArgs) -> PettyObject;
    fn as_any(&self) -> &dyn Any;
}
/// An actually petty object.
#[derive(Clone)]
pub struct PettyObject(Rc<dyn PettyObjectType>);
impl PettyObject {
    pub fn new<Pty: PettyObjectType + 'static>(object: Pty) -> Self {
        Self(Rc::new(object))
    }
    pub fn call_method(&self, vm: &mut Vm, func: &str, mut args: FuncArgs) -> PettyObject {
        args.0.push(self.clone());
        let function = self.get_item(vm, self.clone(), func);
        function.call(vm, function.clone(), args)
    }
}
impl<Pty: PettyObjectType + 'static> From<Pty> for PettyObject {
    fn from(value: Pty) -> Self {
        Self::new(value)
    }
}

impl fmt::Display for PettyObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for PettyObject {
    type Target = Rc<dyn PettyObjectType>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
