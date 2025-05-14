use std::ops::Range;

pub type Span = Range<usize>;

pub type Spanned<T> = (T, Span);

pub trait Spannable : Sized {
    fn spanned(self, span: Span) -> Spanned<Self> {
        (self, span)
    }
}
impl<T> Spannable for T {}

pub fn spanned<T>(span: Span, value: T) -> Spanned<T> {
    (value, span)
}
pub fn spanned_ok<T, E>(span: Span, value: T) -> Result<Spanned<T>, E> {
    Ok((value, span))
}
