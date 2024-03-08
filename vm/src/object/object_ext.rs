use crate::prelude::*;

/// Provides convenient functions without any performance guarantees.
/// Mostly useful for tests.
pub trait ObjectExt: Object + Into<PettyObject> {
    fn call_method(&self, vm: &Vm, key: &str, args: &[PettyObject]) -> PettyObject {
        let mut new_args = Vec::with_capacity(args.len() + 1);
        new_args.push(self.clone().into());
        new_args.extend_from_slice(args);
        self.get(vm, key).call(vm, FnArgs::new(&new_args))
    }
}

impl<T> ObjectExt for T where T: Object + Into<PettyObject> {}
