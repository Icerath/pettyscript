use crate::prelude::*;

/// Provides convenient functions without any performance guarantees.
/// Mostly useful for tests.
pub trait ObjectExt: Object {
    fn call_method(&self, vm: &Vm, key: &str, args: &[PettyObject]) -> PettyObject
    where
        Self: Into<PettyObject>,
    {
        let args: Box<[PettyObject]> =
            std::iter::once(&self.clone().into()).chain(args).cloned().collect();

        self.get(vm, key).call(vm, FnArgs::new(&args))
    }
}

impl<T> ObjectExt for T where T: Object {}
