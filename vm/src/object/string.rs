use crate::prelude::*;

pub use arcstr::ArcStr as PtyStr;

impl Object for PtyStr {
    fn get(&self, key: &str) -> PettyObject {
        match key {
            "trim" => PettyObject::RawFunc(trim),
            _ => unimplemented!(),
        }
    }
}

fn trim(args: FnArgs) -> PettyObject {
    args.assert_len(1..=2);
    let PettyObject::Str(self_) = &args.slice[0] else {
        todo!()
    };
    PtyStr::from(self_.trim()).into()
}
