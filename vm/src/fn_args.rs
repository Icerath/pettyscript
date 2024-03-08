use std::ops::RangeInclusive;

use crate::prelude::*;

#[derive(Debug, Clone, Copy)]
pub struct FnArgs<'a> {
    pub slice: &'a [PettyObject],
}

impl<'a> FnArgs<'a> {
    #[must_use]
    pub const fn new(slice: &'a [PettyObject]) -> Self {
        Self { slice }
    }

    /// # Panics
    pub fn assert_len(self, range: RangeInclusive<usize>) {
        assert!(range.contains(&self.slice.len()), "Expected {range:?} arguments got {}", self.slice.len());
    }
}
