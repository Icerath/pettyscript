use std::hint::unreachable_unchecked;

use super::Value;

macro_rules! ptr {
    ($stack: ident) => {
        *$stack.ptrs.last().unwrap_unchecked()
    };
}

#[derive(Default)]
pub struct VariableStack<'src> {
    inner: Vec<Value<'src>>,
    ptrs: Vec<usize>,
}

impl<'src> VariableStack<'src> {
    pub unsafe fn first(&mut self) -> &mut [Value<'src>] {
        &mut self.inner
    }

    pub unsafe fn last(&mut self) -> &mut [Value<'src>] {
        self.inner.get_unchecked_mut(ptr!(self)..)
    }

    pub unsafe fn pop(&mut self) {
        self.inner.resize_with(ptr!(self), || unreachable_unchecked());
        self.ptrs.pop().unwrap_unchecked();
    }

    pub fn extend_new<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Value<'src>>,
    {
        self.ptrs.push(self.inner.len());
        self.inner.extend(iter);
    }
}
