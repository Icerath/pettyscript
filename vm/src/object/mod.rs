pub mod custom;
pub mod float;
pub mod func;
pub mod int;
pub mod list;
pub mod null;
pub mod string;

pub use custom::CustomObject;

use crate::prelude::*;
use enum_dispatch::enum_dispatch;

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

#[derive(Debug, Clone)]
#[enum_dispatch(Object)]
pub enum PettyObject {
    Int(int::Int),
    Float(float::Float),
    Str(string::PtyStr),
    List(list::List),

    RawFunc(func::RawFunc),

    Null(Null),

    Std(StdObject),
    Custom(CustomObject),
}
