use miette::LabeledSpan;

use crate::parser::{Ident, Spanned};

#[cold]
#[inline(never)]
pub fn unknown_ident(src: impl Into<String>, ident: Spanned<Ident>) -> miette::Report {
    let span = LabeledSpan::at(ident.span.clone(), "not found in this scope");
    miette::miette!(labels = vec![span], "cannot find value `{}` in this scope", ident.inner)
        .with_source_code(src.into())
}
