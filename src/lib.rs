//! This crate features utilities for finding the start, end, and range of lines
//! from a byte index.
//! Further also being able to find the next and previous line, from an arbitrary byte index.
//!
//! **Current Line:**
//!
//! - [`find_line_start`](fn.find_line_start.html) to find the start of the current line.
//! - [`find_line_end`](fn.find_line_end.html) to find the end of the current line.
//! - [`find_line_range`](fn.find_line_range.html) to find the start and end current line.
//!
//! **Next Line:**
//!
//! - [`find_next_line_start`](fn.find_next_line_start.html) to find the start of the next line.
//! - [`find_next_line_end`](fn.find_next_line_end.html) to find the end of the next line.
//! - [`find_next_line_range`](fn.find_next_line_range.html) to find the start and end of the next line.
//!
//! **Previous Line:**
//!
//! - [`find_prev_line_start`](fn.find_prev_line_start.html) to find the start of the previous line.
//! - [`find_prev_line_end`](fn.find_prev_line_end.html) to find the end of the previous line.
//! - [`find_prev_line_range`](fn.find_prev_line_range.html) to find both start and end of the previous line.
//!
//! # [`LineSpan`] and [`LineSpanIter`]
//!
//! The crate includes the [`LineSpanIter`] iterator. It is functionally equivalent to [`str::lines`],
//! with the addition that it includes the ability to get the start and end byte indices of each line.
//!
//! An [`LineSpanIter`] can be created by calling [`line_spans`](trait.LineSpans.html#tymethod.line_spans),
//! implemented in the [`LineSpans`] trait.
//! The crate implements the [`LineSpans`] trait for [`str`] and [`String`].
//!
//! Note, [`LineSpan`] implements [`Deref`] to [`&str`], so in general,
//! swapping [`lines`] to [`line_spans`] would not cause many issues.
//!
//! ```no_run
//! use line_span::LineSpans;
//!
//! let text = "foo\nbar\r\nbaz";
//!
//! for span in text.line_spans() {
//!     println!("{:>2?}: {:?}", span.range(), span.as_str());
//! }
//! ```
//!
//! This will output the following:
//!
//! ```text
//!  0.. 3: "foo"
//!  4.. 7: "bar"
//!  9..12: "baz"
//! ```
//!
//! [`LineSpan`]: struct.LineSpan.html
//! [`LineSpanIter`]: struct.LineSpanIter.html
//! [`LineSpans`]: trait.LineSpans.html
//! [`line_spans`]: trait.LineSpans.html#tymethod.line_spans
//! [`Deref`]: https://doc.rust-lang.org/stable/std/ops/trait.Deref.html
//! [`&str`]: https://doc.rust-lang.org/stable/std/primitive.str.html
//! [`lines`]: https://doc.rust-lang.org/stable/std/primitive.str.html#method.lines
//! [`str::lines`]: https://doc.rust-lang.org/stable/std/primitive.str.html#method.lines
//!
//! [`str`]: https://doc.rust-lang.org/stable/std/primitive.str.html
//! [`String`]: https://doc.rust-lang.org/stable/std/string/struct.String.html
//!
//! # Current Line, Previous Line, and Next Line
//!
//! ```
//! use line_span::{find_line_range, find_next_line_range, find_prev_line_range};
//!
//! let text = "foo\nbar\r\nbaz";
//! //                ^
//! let i = 5; // 'a' in "bar"
//!
//! let curr_range = find_line_range(text, i);
//! let next_range = find_next_line_range(text, i).unwrap();
//! let prev_range = find_prev_line_range(text, i).unwrap();
//!
//! assert_eq!(curr_range, 4..7);
//! assert_eq!(&text[curr_range], "bar");
//!
//! assert_eq!(prev_range, 0..3);
//! assert_eq!(&text[prev_range], "foo");
//!
//! assert_eq!(next_range, 9..12);
//! assert_eq!(&text[next_range], "baz");
//! ```

#![forbid(unsafe_code)]
#![deny(missing_docs)]
// #![deny(missing_doc_code_examples)]
#![deny(missing_debug_implementations)]
#![warn(clippy::all)]

use std::fmt;
use std::iter::FusedIterator;
use std::ops::{Deref, Range};

/// Find the start (byte index) of the line, which `index` is within.
///
/// ## See also
///
/// - [`find_line_range`](fn.find_line_range.html) to find both start and end of a line.
/// - [`find_line_end`](fn.find_line_end.html) to find the end of the line.
/// - [`find_next_line_start`](fn.find_next_line_start.html) to find the start of the next line.
/// - [`find_prev_line_start`](fn.find_prev_line_start.html) to find the start of the previous line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 5; // 'a'
///
/// let start = line_span::find_line_start(text, i);
///
/// assert_eq!(start, 4);
/// assert_eq!(&text[start..], "bar\nbaz");
/// ```
#[inline]
pub fn find_line_start(text: &str, index: usize) -> usize {
    text[..index].rfind('\n').map_or(0, |i| i + 1)
}

/// Find the end (byte index) of the line, which `index` is within.
///
/// Note the end is the last character, excluding `\n` and `\r\n`.
///
/// ## See also
///
/// - [`find_line_range`](fn.find_line_range.html) to find both start and end of a line.
/// - [`find_line_start`](fn.find_line_start.html) to find the start of the line.
/// - [`find_next_line_end`](fn.find_next_line_end.html) to find the end of the next line.
/// - [`find_prev_line_end`](fn.find_prev_line_end.html) to find the end of the previous line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 5; // 'a'
///
/// let end = line_span::find_line_end(text, i);
///
/// assert_eq!(end, 7);
/// assert_eq!(&text[..end], "foo\nbar");
/// ```
pub fn find_line_end(text: &str, index: usize) -> usize {
    let end = text[index..]
        .find('\n')
        .map_or_else(|| text.len(), |i| index + i);

    if (end > 0) && (text.as_bytes()[end - 1] == b'\r') {
        end - 1
    } else {
        end
    }
}

/// Find the start and end (byte index) of the line, which `index` is within.
///
/// Note the end is the last character, excluding `\n` and `\r\n`.
///
/// ## See also
///
/// - [`find_line_start`](fn.find_line_start.html) to find only the start of the line.
/// - [`find_line_end`](fn.find_line_end.html) to find only the end of the line.
/// - [`find_next_line_range`](fn.find_next_line_range.html) to find the start and end of the next line.
/// - [`find_prev_line_range`](fn.find_prev_line_range.html) to find the start and end of the previous line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 5; // 'a'
///
/// let range = line_span::find_line_range(text, i);
/// assert_eq!(range, 4..7);
///
/// let line = &text[range];
/// assert_eq!(line, "bar");
/// ```
#[inline]
pub fn find_line_range(text: &str, index: usize) -> Range<usize> {
    find_line_start(text, index)..find_line_end(text, index)
}

/// Find the start (byte index) of the next line, the line after the one which `index` is within.
///
/// Returns [`None`] if there is no next line.
///
/// [`None`]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
///
/// ## See also
///
/// - [`find_next_line_range`](fn.find_next_line_range.html) to find both start and end of the next line.
/// - [`find_next_line_end`](fn.find_next_line_end.html) to find the end of the next line.
/// - [`find_line_start`](fn.find_line_start.html) to find the start of the current line.
/// - [`find_prev_line_start`](fn.find_prev_line_start.html) to find the start of the previous line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 1; // 'o'
///
/// let start = line_span::find_next_line_start(text, i).unwrap();
///
/// assert_eq!(start, 4);
/// assert_eq!(&text[start..], "bar\nbaz");
/// ```
#[inline]
pub fn find_next_line_start(text: &str, index: usize) -> Option<usize> {
    text[index..].find('\n').map(|i| index + i + 1)
}

/// Find the end (byte index) of the next line, the line after the one which `index` is within.
///
/// Note the end is the last character, excluding `\n` and `\r\n`.
///
/// Returns [`None`] if there is no next line.
///
/// [`None`]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
///
/// ## See also
///
/// - [`find_next_line_range`](fn.find_next_line_range.html) to find both start and end of the next line.
/// - [`find_next_line_start`](fn.find_next_line_start.html) to find the start of the next line.
/// - [`find_line_start`](fn.find_line_start.html) to find the start of the current line.
/// - [`find_prev_line_start`](fn.find_prev_line_start.html) to find the start of the previous line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 1; // 'o'
///
/// let end = line_span::find_next_line_end(text, i).unwrap();
///
/// assert_eq!(end, 7);
/// assert_eq!(&text[..end], "foo\nbar");
/// ```
#[inline]
pub fn find_next_line_end(text: &str, index: usize) -> Option<usize> {
    find_next_line_start(text, index).map(|i| find_line_end(text, i))
}

/// Find the start and end (byte index) of the next line, the line after the one which `index` is within.
///
/// Note the end is the last character, excluding `\n` and `\r\n`.
///
/// Returns [`None`] if there is no next line.
///
/// [`None`]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
///
/// ## See also
///
/// - [`find_next_line_start`](fn.find_next_line_start.html) to find only the start of the next line.
/// - [`find_next_line_end`](fn.find_line_end.html) to find only the end of the next line.
/// - [`find_line_range`](fn.find_next_line_range.html) to find the start and end of the current line.
/// - [`find_prev_line_range`](fn.find_prev_line_range.html) to find the start and end of the previous line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 1; // 'o'
///
/// let range = line_span::find_next_line_range(text, i).unwrap();
/// assert_eq!(range, 4..7);
///
/// let line = &text[range];
/// assert_eq!(line, "bar");
/// ```
#[inline]
pub fn find_next_line_range(text: &str, index: usize) -> Option<Range<usize>> {
    find_next_line_start(text, index).map(|start| start..find_line_end(text, start))
}

/// Find the start (byte index) of the previous line, the line before the one which `index` is within.
///
/// Returns [`None`] if there is no previous line.
///
/// [`None`]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
///
/// ## See also
///
/// - [`find_prev_line_range`](fn.find_prev_line_range.html) to find both start and end of the previous line.
/// - [`find_prev_line_end`](fn.find_prev_line_end.html) to find the end of the previous line.
/// - [`find_line_start`](fn.find_line_start.html) to find the start of the current line.
/// - [`find_next_line_start`](fn.find_next_line_start.html) to find the start of the next line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 9; // 'a'
///
/// let start = line_span::find_prev_line_start(text, i).unwrap();
///
/// assert_eq!(start, 4);
/// assert_eq!(&text[start..], "bar\nbaz");
/// ```
#[inline]
pub fn find_prev_line_start(text: &str, index: usize) -> Option<usize> {
    find_prev_line_end(text, index).map(|i| find_line_start(text, i))
}

/// Find the end (byte index) of the previous line, the line before the one which `index` is within.
///
/// Note the end is the last character, excluding `\n` and `\r\n`.
///
/// Returns [`None`] if there is no previous line.
///
/// [`None`]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
///
/// ## See also
///
/// - [`find_prev_line_range`](fn.find_prev_line_range.html) to find both start and end of the previous line.
/// - [`find_prev_line_start`](fn.find_prev_line_start.html) to find the start of the previous line.
/// - [`find_line_start`](fn.find_line_start.html) to find the start of the current line.
/// - [`find_next_line_start`](fn.find_prev_line_start.html) to find the start of the next line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 9; // 'a'
///
/// let end = line_span::find_prev_line_end(text, i).unwrap();
///
/// assert_eq!(end, 7);
/// assert_eq!(&text[..end], "foo\nbar");
/// ```
#[inline]
pub fn find_prev_line_end(text: &str, index: usize) -> Option<usize> {
    text[..index].rfind('\n').map(|end| {
        if (end > 0) && (text.as_bytes()[end - 1] == b'\r') {
            end - 1
        } else {
            end
        }
    })
}

/// Find the start and end (byte index) of the previous line, the line before the one which `index` is within.
///
/// Note the end is the last character, excluding `\n` and `\r\n`.
///
/// Returns [`None`] if there is no previous line.
///
/// [`None`]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
///
/// ## See also
///
/// - [`find_prev_line_start`](fn.find_prev_line_start.html) to find only the start of the previous line.
/// - [`find_prev_line_end`](fn.find_line_end.html) to find only the end of the previous line.
/// - [`find_line_range`](fn.find_next_line_range.html) to find the start and end of the current line.
/// - [`find_next_line_range`](fn.find_prev_line_range.html) to find the start and end of the next line.
///
/// # Panics
///
/// Panics if `index` is out of bounds.
///
/// # Example
///
/// ```
/// let text = "foo\nbar\nbaz";
/// let i = 9; // 'a'
///
/// let range = line_span::find_prev_line_range(text, i).unwrap();
/// assert_eq!(range, 4..7);
///
/// let line = &text[range];
/// assert_eq!(line, "bar");
/// ```
#[inline]
pub fn find_prev_line_range(text: &str, index: usize) -> Option<Range<usize>> {
    find_prev_line_end(text, index).map(|end| find_line_start(text, end)..end)
}

/// [`LineSpan`] represents a single line, excluding `\n` and `\r\n`.
///
/// [`LineSpan`]: struct.LineSpan.html
///
/// ```no_run
/// use line_span::LineSpans;
///
/// let text = "foo\nbar\r\nbaz";
///
/// for span in text.line_spans() {
///     println!("{:>2?}: {:?}", span.range(), span.as_str());
/// }
/// ```
///
/// This will output the following:
///
/// ```text
///  0.. 3: "foo"
///  4.. 7: "bar"
///  9..12: "baz"
/// ```
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct LineSpan<'a> {
    text: &'a str,
    start: usize,
    end: usize,
}

impl<'a> LineSpan<'a> {
    /// Returns the byte index of the start of the line.
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns the byte index of the end of the line.
    #[inline]
    pub fn end(&self) -> usize {
        self.end
    }

    /// Returns the byte index range of the start and end of the line.
    #[inline]
    pub fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    /// Returns `&str` of the line, excluding `\n` and `\r\n`.
    #[inline]
    pub fn as_str(&self) -> &'a str {
        &self.text[self.range()]
    }
}

impl<'a> Deref for LineSpan<'a> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<'a> From<LineSpan<'a>> for &'a str {
    #[inline]
    fn from(span: LineSpan<'a>) -> &'a str {
        span.as_str()
    }
}

impl<'a> From<LineSpan<'a>> for Range<usize> {
    #[inline]
    fn from(span: LineSpan<'a>) -> Range<usize> {
        span.range()
    }
}

impl<'a> fmt::Debug for LineSpan<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("LineSpan")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("line", &self.as_str())
            .finish()
    }
}

impl<'a> fmt::Display for LineSpan<'a> {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(fmt)
    }
}

/// An iterator over `LineSpan`s.
///
/// This struct is created with the [`line_spans`] method in the [`LineSpans`] trait.
/// See its documentation for more.
///
/// [`LineSpan`]: struct.LineSpan.html
/// [`LineSpans`]: trait.LineSpans.html
/// [`line_spans`]: trait.LineSpans.html#tymethod.line_spans
///
/// [`lines`]: ../../std/primitive.str.html#method.lines
/// [`str`]: ../../std/primitive.str.html
#[allow(missing_debug_implementations)]
pub struct LineSpanIter<'a> {
    text: &'a str,
    index: Option<usize>,
}

impl<'a> LineSpanIter<'a> {
    #[inline]
    fn from(text: &'a str) -> Self {
        Self {
            text,
            index: Some(0),
        }
    }
}

impl<'a> Iterator for LineSpanIter<'a> {
    type Item = LineSpan<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(start) = self.index {
            let end = find_line_end(self.text, start);

            self.index = find_next_line_start(self.text, end);

            Some(LineSpan {
                text: self.text,
                start,
                end,
            })
        } else {
            None
        }
    }
}

impl<'a> FusedIterator for LineSpanIter<'a> {}

/// Trait which implements [`line_spans`](trait.LineSpans.html#tymethod.line_spans)
/// to get a [`LineSpanIter`](struct.LineSpanIter.html).
///
/// ```no_run
/// use line_span::LineSpans;
///
/// let text = "foo\nbar\r\nbaz";
///
/// for span in text.line_spans() {
///     println!("{:>2?}: {:?}", span.range(), span.as_str());
/// }
/// ```
///
/// This will output the following:
///
/// ```text
///  0.. 3: "foo"
///  4.. 7: "bar"
///  9..12: "baz"
/// ```
pub trait LineSpans {
    /// Creates a [`LineSpanIter`](struct.LineSpanIter.html).
    fn line_spans(&self) -> LineSpanIter;
}

impl LineSpans for str {
    #[inline]
    fn line_spans(&self) -> LineSpanIter {
        LineSpanIter::from(self)
    }
}

impl LineSpans for String {
    #[inline]
    fn line_spans(&self) -> LineSpanIter {
        LineSpanIter::from(self.as_str())
    }
}

#[test]
fn test_line_spans() {
    let text = "\r\nfoo\nbar\r\nbaz\nqux\r\n\r";

    let mut it = text.line_spans();
    assert_eq!(Some(""), it.next().as_deref());
    assert_eq!(Some("foo"), it.next().as_deref());
    assert_eq!(Some("bar"), it.next().as_deref());
    assert_eq!(Some("baz"), it.next().as_deref());
    assert_eq!(Some("qux"), it.next().as_deref());
    assert_eq!(Some(""), it.next().as_deref());
    assert_eq!(None, it.next().as_deref());

    let mut it = text.line_spans().map(|span| span.range());
    assert_eq!(Some(0..0), it.next());
    assert_eq!(Some(2..5), it.next());
    assert_eq!(Some(6..9), it.next());
    assert_eq!(Some(11..14), it.next());
    assert_eq!(Some(15..18), it.next());
    assert_eq!(Some(20..20), it.next());
    assert_eq!(None, it.next());
}

#[test]
fn test_line_spans_vs_lines() {
    let text = "\r\nfoo\nbar\r\nbaz\nqux\r\n\r";

    for (span, line) in text.line_spans().zip(text.lines()) {
        assert_eq!(span.as_str(), line);
    }
}
