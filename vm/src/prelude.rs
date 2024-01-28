pub use crate::fn_args::FnArgs;
pub use crate::object::{CustomObject, Object, ObjectExt, PettyObject};
pub use crate::object::{Float, Int, Null, PtyStr, RawFunc};
pub use crate::stdlib::StdObject;

pub use arcstr::literal as ptystr;

pub const NULL: &PettyObject = &PettyObject::Null(Null);

pub use macros::pettyfunc;
pub use std::any::TypeId;
pub use std::fmt::Debug;
pub use std::sync::{Arc, Mutex};
