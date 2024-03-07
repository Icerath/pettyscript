pub use arcstr::literal as ptystr;

pub use crate::fn_args::FnArgs;
pub use crate::object::{Bool, Float, Func, Int, Null, PtyStr, RawFunc};
pub use crate::object::{CustomObject, Object, ObjectExt, PettyObject};
pub use crate::run::Vm;
pub use crate::stdlib::StdObject;

pub const NULL: PettyObject = PettyObject::NULL;

pub use std::any::TypeId;
pub use std::cell::RefCell;
pub use std::fmt::Debug;
pub use std::rc::Rc;

pub use macros::pettyfunc;
