pub use arcstr::ArcStr as PtyStr;

use crate::prelude::*;

impl Object for PtyStr {
    fn get(&self, _vm: &Vm, key: &str) -> PettyObject {
        match key {
            "trim" => PettyObject::RawFunc(trim),
            "trim_start" => PettyObject::RawFunc(trim_start),
            "trim_end" => PettyObject::RawFunc(trim_end),
            "__repr__" => PettyObject::RawFunc(__repr__),
            _ => unimplemented!("{key:?}"),
        }
    }
}

#[pettyfunc]
fn __repr__(this: PtyStr) -> PtyStr {
    this.clone()
}

#[pettyfunc]
fn trim(this: PtyStr, #[option] pat: PtyStr) -> PtyStr {
    match pat {
        Some(pat) => this.trim_start_matches(pat.as_str()).trim_end_matches(pat.as_str()),
        None => this.trim(),
    }
    .into()
}

#[pettyfunc]
fn trim_start(this: PtyStr, #[option] pat: PtyStr) -> PtyStr {
    match pat {
        Some(pat) => this.trim_start_matches(pat.as_str()),
        None => this.trim_start(),
    }
    .into()
}

#[pettyfunc]
fn trim_end(this: PtyStr, #[option] pat: PtyStr) -> PtyStr {
    match pat {
        Some(pat) => this.trim_end_matches(pat.as_str()),
        None => this.trim_end(),
    }
    .into()
}

#[test]
fn test_trim() {
    let input = ptystr!("   \nHello, World!\t   ");
    let object = PettyObject::from(input.clone());
    let vm = &Vm::new();

    assert!(matches!(object.call_method(vm, "trim", &[]), PettyObject::PtyStr(str) if str == input.trim()));
    assert!(matches!(object.call_method(vm, "trim_start", &[]), PettyObject::PtyStr(str) if str == input.trim_start()));
    assert!(matches!(object.call_method(vm, "trim_end", &[]), PettyObject::PtyStr(str) if str == input.trim_end()));
    assert!(
        matches!(object.call_method(vm, "trim", &[ptystr!(" ").into()]), PettyObject::PtyStr(str) if str == input.trim_matches(' '))
    );
}
