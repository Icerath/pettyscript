pub use arcstr::ArcStr as PtyStr;

use crate::prelude::*;

impl Object for PtyStr {
    fn get(&self, key: &str) -> PettyObject {
        match key {
            "trim" => PettyObject::RawFunc(trim),
            "trim_start" => PettyObject::RawFunc(trim_start),
            "trim_end" => PettyObject::RawFunc(trim_end),
            _ => unimplemented!(),
        }
    }
}

#[pettyfunc]
fn trim(self_: PtyStr, #[option] pat: PtyStr) -> PtyStr {
    match pat {
        Some(pat) => self_.trim_start_matches(pat.as_str()).trim_end_matches(pat.as_str()),
        None => self_.trim(),
    }
    .into()
}

#[pettyfunc]
fn trim_start(self_: PtyStr, #[option] pat: PtyStr) -> PtyStr {
    match pat {
        Some(pat) => self_.trim_start_matches(pat.as_str()),
        None => self_.trim_start(),
    }
    .into()
}

#[pettyfunc]
fn trim_end(self_: PtyStr, #[option] pat: PtyStr) -> PtyStr {
    match pat {
        Some(pat) => self_.trim_end_matches(pat.as_str()),
        None => self_.trim_end(),
    }
    .into()
}

#[test]
fn test_trim() {
    let input = ptystr!("   \nHello, World!\t   ");
    let object = PettyObject::from(input.clone());

    assert!(
        matches!(object.call_method("trim", &[]), PettyObject::PtyStr(str) if str == input.trim())
    );
    assert!(
        matches!(object.call_method("trim_start", &[]), PettyObject::PtyStr(str) if str == input.trim_start())
    );
    assert!(
        matches!(object.call_method("trim_end", &[]), PettyObject::PtyStr(str) if str == input.trim_end())
    );
    assert!(
        matches!(object.call_method("trim", &[ptystr!(" ").into()]), PettyObject::PtyStr(str) if str == input.trim_matches(' '))
    );
}
