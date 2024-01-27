use std::ops::RangeInclusive;

use crate::prelude::*;

#[derive(Debug, Clone, Copy)]
pub struct FnArgs<'a> {
    pub slice: &'a [PettyObject],
}

impl<'a> FnArgs<'a> {
    pub fn new(slice: &'a [PettyObject]) -> Self {
        Self { slice }
    }
    pub fn assert_len(self, range: RangeInclusive<usize>) {
        assert!(
            range.contains(&self.slice.len()),
            "Expected {range:?} arguments got {}",
            self.slice.len()
        );
    }
}
