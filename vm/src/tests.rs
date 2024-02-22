use std::mem::size_of;

use crate::prelude::*;

#[test]
fn sizeof_obj() {
    assert_eq!(size_of::<PettyObject>(), size_of::<usize>() * 2);
    assert_eq!(size_of::<Option<PettyObject>>(), size_of::<usize>() * 2);
}
