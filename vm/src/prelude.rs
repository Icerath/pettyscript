pub use crate::fn_args::FnArgs;
pub use crate::object::ObjectExt;
pub use crate::object::{CustomObject, Object, PettyObject};
pub use crate::object::{Float, Int, Null, PtyStr, RawFunc};
pub use crate::stdlib::StdObject;

// Allow me to change the type globally
pub use std::any::TypeId;
pub use std::rc::Rc;
pub use std::sync::Mutex;

pub use arcstr::literal as ptystr;

pub const NULL: &PettyObject = &PettyObject::Null(Null);

// Convenience
pub use macros::pettyfunc;
pub use std::fmt::Debug;
