pub mod bool;
pub mod custom;
pub mod float;
pub mod func;
pub mod int;
pub mod list;
pub mod null;
pub mod object_ext;
pub mod range;
pub mod raw_func;
pub mod string;

pub use bool::Bool;
pub use custom::CustomObject;
use enum_dispatch::enum_dispatch;
pub use float::Float;
pub use func::Func;
pub use int::Int;
pub use list::List;
pub use null::Null;
pub use object_ext::ObjectExt;
pub use range::{Range, RangeInclusive};
pub use raw_func::RawFunc;
pub use string::PtyStr;

use crate::{prelude::*, run::Vm};

#[enum_dispatch]
pub trait Object: Clone + 'static + Debug {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
    fn call(&self, vm: &Vm, args: FnArgs) -> PettyObject {
        _ = vm;
        _ = args;
        let ty = std::any::type_name_of_val(self);
        unimplemented!("{ty:?}")
    }
    fn get(&self, vm: &Vm, key: &str) -> PettyObject {
        _ = vm;
        let ty = std::any::type_name_of_val(self);
        unimplemented!("{ty:?}: {key:?}")
    }
    fn set(&self, vm: &Vm, key: PtyStr, val: PettyObject) {
        _ = vm;
        let ty = std::any::type_name_of_val(self);
        unimplemented!("{ty:?}: {key:?} = {val:?}")
    }
}

#[enum_dispatch(Object)]
#[derive(Debug, Clone)]
pub enum PettyObject {
    Bool,
    Int,
    Float,
    PtyStr,
    List,

    RawFunc,
    Func(Rc<Func>),

    RangeInclusive,
    Range,

    Null,

    StdObject,
    CustomObject,
}

impl PettyObject {
    pub const NULL: Self = Self::Null(Null);

    #[must_use]
    pub const fn is_null(&self) -> bool {
        matches!(self, Self::Null(_))
    }
}
