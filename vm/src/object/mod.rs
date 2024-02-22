pub mod custom;
pub mod float;
pub mod func;
pub mod int;
pub mod list;
pub mod null;
pub mod object_ext;
pub mod string;

pub use custom::CustomObject;
use enum_dispatch::enum_dispatch;
pub use float::Float;
pub use func::RawFunc;
pub use int::Int;
pub use list::List;
pub use null::Null;
pub use object_ext::ObjectExt;
pub use string::PtyStr;

use crate::prelude::*;

#[enum_dispatch]
pub trait Object: Clone + 'static {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
    fn call(&self, args: FnArgs) -> PettyObject {
        _ = args;
        unimplemented!()
    }
    fn get(&self, key: &str) -> PettyObject {
        _ = key;
        unimplemented!()
    }
    fn set(&self, key: PtyStr, val: PettyObject) {
        _ = key;
        _ = val;
        unimplemented!()
    }
}

#[enum_dispatch(Object)]
#[derive(Debug, Clone)]
pub enum PettyObject {
    Int,
    Float,
    PtyStr,
    List,

    RawFunc,

    Null,

    StdObject,
    CustomObject,
}
