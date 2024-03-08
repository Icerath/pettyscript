use std::cmp::Ordering;

use crate::prelude::*;

pub type Int = i64;

impl Object for Int {
    fn get(&self, _: &Vm, key: &str) -> PettyObject {
        match key {
            "__mod__" => PettyObject::RawFunc(__mod__),
            "__eq__" => PettyObject::RawFunc(__eq__),
            "__repr__" => PettyObject::RawFunc(__repr__),
            "__add__" => PettyObject::RawFunc(__add__),
            "__sub__" => PettyObject::RawFunc(__sub__),
            "__cmp__" => PettyObject::RawFunc(__cmp__),
            _ => unimplemented!("{key}"),
        }
    }
}

#[pettyfunc]
pub fn __mod__(this: Int, other: Int) -> Int {
    this % other
}

#[pettyfunc]
pub fn __eq__(this: Int, other: Int) -> bool {
    this == other
}

#[pettyfunc]
fn __repr__(this: Int) -> PtyStr {
    this.to_string().into()
}

#[pettyfunc]
fn __add__(this: Int, other: Int) -> Int {
    this + other
}

#[pettyfunc]
fn __sub__(this: Int, other: Int) -> Int {
    this - other
}

#[pettyfunc]
fn __cmp__(this: Int, other: Int) -> Int {
    match this.cmp(other) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}
