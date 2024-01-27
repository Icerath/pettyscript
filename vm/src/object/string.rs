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

#[pettyfunc]
fn trim(self_: PtyStr, pat: PtyStr) -> PtyStr {
    let pat = pat.as_str();
    let trimmed = self_.trim_start_matches(pat).trim_end_matches(pat);
    trimmed.into()
}

#[pettyfunc]
fn trim_start(self_: PtyStr, pat: PtyStr) -> PtyStr {
    self_.trim_start_matches(pat.as_str()).into()
}

#[pettyfunc]
fn trim_end(self_: PtyStr, pat: PtyStr) -> PtyStr {
    self_.trim_end_matches(pat.as_str()).into()
}
