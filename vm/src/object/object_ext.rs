use crate::prelude::*;

/// Provides convenient functions without any performance guarantees.
/// Mostly useful for tests.
pub trait ObjectExt: Object {
    fn call_method(&self, key: &str, args: &[PettyObject]) -> PettyObject
    where
        Self: Into<PettyObject>,
    {
        let args: Box<[PettyObject]> =
            [&self.clone().into()].into_iter().chain(args).cloned().collect();

        self.get(key).call(FnArgs::new(&args))
    }
}

impl<T> ObjectExt for T where T: Object {}
