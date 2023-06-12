//! This crate features utilities for finding the start, end, and range of
//! lines from a byte index. Further also being able to find the next and
//! previous line, from an arbitrary byte index.
//!
//! This is provided via the <code>trait [LineSpanExt]</code>, which is
//! implemented for [`str`], and provides the following methods:
//!
//! **Current Line:**
//!
//! - [`find_line_start()`](LineSpanExt::find_line_start) to find the start of the current line.
//! - [`find_line_end()`](LineSpanExt::find_line_end) to find the end of the current line.
//! - [`find_line_range()`](LineSpanExt::find_line_range) to find the start and end current line.
//!
//! **Next Line:**
//!
//! - [`find_next_line_start()`](LineSpanExt::find_next_line_start) to find the start of the next line.
//! - [`find_next_line_end()`](LineSpanExt::find_next_line_end) to find the end of the next line.
//! - [`find_next_line_range()`](LineSpanExt::find_next_line_range) to find the start and end of the next line.
//!
//! **Previous Line:**
//!
//! - [`find_prev_line_start()`](LineSpanExt::find_prev_line_start) to find the start of the previous line.
//! - [`find_prev_line_end()`](LineSpanExt::find_prev_line_end) to find the end of the previous line.
//! - [`find_prev_line_range()`](LineSpanExt::find_prev_line_range) to find both start and end of the previous line.
//!
//! **Iterator:**
//!
//! - [`line_spans()`](LineSpanExt::line_spans) an iterator over [`LineSpan`]s, i.e. [`str::lines()`] but including the
//! start and end byte indicies (in the form of a [`Range<usize>`]).
//!
//! **Utilities:**
//!
//! - [`str_to_range()`] to get the range of a substring in a string.
//! - [`str_to_range_unchecked()`] unchecked version of [`str_to_range()`].
//!
//! # [`LineSpan`] and [`LineSpanIter`]
//!
//! The crate includes the [`LineSpanIter`] iterator. It is functionally equivalent to [`str::lines()`],
//! with the addition that it includes the ability to get the start and end byte indices of each line.
//! Additionally, it also includes the ability to get the end including and excluding the line ending (`\n` or `\r\n`).
//!
//! An [`LineSpanIter`] can be created by calling [`line_spans()`](LineSpans::line_spans),
//! implemented in the [`LineSpans`] trait.
//! The crate implements the [`LineSpans`] trait for [`str`] and [`String`].
//!
//! Note, [`LineSpan`] implements [`Deref`] to [`&str`], so in general,
//! swapping [`lines()`] to [`line_spans()`](LineSpans::line_spans) would not cause many issues.
//!
//! ```rust
//! use line_span::LineSpanExt;
//!
//! let text = "foo\nbar\r\nbaz";
//!
//! for span in text.line_spans() {
//!     println!(
//!         "{:>2?}: {:?} {:?} {:?}",
//!         span.range(),
//!         span.as_str(),
//!         span.as_str_with_ending(),
//!         span.ending_str(),
//!     );
//! }
//! ```
//!
//! This will output the following:
//!
//! _(Manually aligned for better readability)_
//!
//! ```text
//! 0.. 3: "foo" "foo\n"   "\n"
//! 4.. 7: "bar" "bar\r\n" "\r\n"
//! 9..12: "baz" "baz"     ""
//! ```
//!
//! # Current Line, Previous Line, and Next Line
//!
//! ```rust
//! use line_span::LineSpanExt;
//!
//! let text = "foo\nbar\r\nbaz";
//! //                ^
//! let i = 5; // 'a' in "bar"
//!
//! let curr_range = text.find_line_range(i);
//! let next_range = text.find_next_line_range(i).unwrap();
//! let prev_range = text.find_prev_line_range(i).unwrap();
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
//!
//! # Range of Substring in String
//!
//! Use [`str_to_range`] (or [`str_to_range_unchecked`]) to get the
//! range of a substring in a string.
//!
//! ```rust
//! # use line_span::str_to_range;
//! let string1 = "Foo Bar Baz";
//! let string2 = "Hello World";
//!
//! let substring = &string1[4..7]; // "Bar"
//! # assert_eq!(substring, "Bar");
//!
//! // Returns `Some` as `substring` is a part of `string1`
//! assert_eq!(str_to_range(string1, substring), Some(4..7));
//!
//! // Returns `None` as `substring` is not a part of `string2`
//! assert_eq!(str_to_range(string2, substring), None);
//! ```
//!
//! [`Deref`]: core::ops::Deref
//! [`&str`]: core::str
//! [`lines()`]: str::lines
//! [`str::lines()`]: str::lines
//! [`String`]: https://doc.rust-lang.org/std/string/struct.String.html

#![forbid(unsafe_code)]
#![forbid(elided_lifetimes_in_paths)]
#![deny(missing_docs)]
// #![deny(missing_doc_code_examples)]
#![deny(missing_debug_implementations)]
#![warn(clippy::all)]
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::fmt;
use core::iter::FusedIterator;
use core::ops::{Deref, Range};
use core::str::Lines;

/// Trait implementing utility methods for finding the start, end, and range of
/// lines from a byte index. Further also being able to find the next and
/// previous line, from an arbitrary byte index.
pub trait LineSpanExt {
    /// Creates a [`LineSpanIter`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use line_span::LineSpanExt;
    ///
    /// let text = "foo\nbar\r\nbaz";
    ///
    /// for span in text.line_spans() {
    ///     println!(
    ///         "{:>2?}: {:?} {:?} {:?}",
    ///         span.range(),
    ///         span.as_str(),
    ///         span.as_str_with_ending(),
    ///         span.ending_str(),
    ///     );
    /// }
    /// # let mut spans = text.line_spans();
    /// # assert!(matches!(spans.next(), Some(span) if span.range() == (0..3)));
    /// # assert!(matches!(spans.next(), Some(span) if span.range() == (4..7)));
    /// # assert!(matches!(spans.next(), Some(span) if span.range() == (9..12)));
    /// # assert_eq!(spans.next(), None);
    /// ```
    ///
    /// This will output the following:
    ///
    /// _(Manually aligned for better readability)_
    ///
    /// ```text
    /// 0.. 3: "foo" "foo\n"   "\n"
    /// 4.. 7: "bar" "bar\r\n" "\r\n"
    /// 9..12: "baz" "baz"     ""
    /// ```
    fn line_spans(&self) -> LineSpanIter<'_>;

    /// Find the start (byte index) of the line, which `index` is within.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// let i = 5; // 'a'
    ///
    /// let start = text.find_line_start(i);
    ///
    /// assert_eq!(start, 4);
    /// assert_eq!(&text[start..], "bar\nbaz");
    /// ```
    fn find_line_start(&self, index: usize) -> usize;

    /// Find the end (byte index) of the line, which `index` is within.
    ///
    /// Note the end is the last character, excluding `\n` and `\r\n`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// let i = 5; // 'a'
    ///
    /// let end = text.find_line_end(i);
    ///
    /// assert_eq!(end, 7);
    /// assert_eq!(&text[..end], "foo\nbar");
    /// ```
    fn find_line_end(&self, index: usize) -> usize;

    /// Find the start and end (byte index) of the line, which `index` is within.
    ///
    /// Note the end is the last character, excluding `\n` and `\r\n`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //                ^
    /// let i = 5; // 'a'
    ///
    /// let range = text.find_line_range(i);
    /// assert_eq!(range, 4..7);
    ///
    /// let line = &text[range];
    /// assert_eq!(line, "bar");
    /// ```
    fn find_line_range(&self, index: usize) -> Range<usize>;

    /// Find the start (byte index) of the next line, the line after the one which `index` is within.
    ///
    /// Returns [`None`] if there is no next line.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //           ^
    /// let i = 1; // 'o'
    ///
    /// let start = text.find_next_line_start(i).unwrap();
    ///
    /// assert_eq!(start, 4);
    /// assert_eq!(&text[start..], "bar\nbaz");
    /// ```
    fn find_next_line_start(&self, index: usize) -> Option<usize>;

    /// Find the end (byte index) of the next line, the line after the one which `index` is within.
    ///
    /// Note the end is the last character, excluding `\n` and `\r\n`.
    ///
    /// Returns [`None`] if there is no next line.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //           ^
    /// let i = 1; // 'o'
    ///
    /// let end = text.find_next_line_end(i).unwrap();
    ///
    /// assert_eq!(end, 7);
    /// assert_eq!(&text[..end], "foo\nbar");
    /// ```
    fn find_next_line_end(&self, index: usize) -> Option<usize>;

    /// Find the start and end (byte index) of the next line, the line after the one which `index` is within.
    ///
    /// Note the end is the last character, excluding `\n` and `\r\n`.
    ///
    /// Returns [`None`] if there is no next line.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //           ^
    /// let i = 1; // 'o'
    ///
    /// let range = text.find_next_line_range(i).unwrap();
    /// assert_eq!(range, 4..7);
    ///
    /// let line = &text[range];
    /// assert_eq!(line, "bar");
    /// ```
    fn find_next_line_range(&self, index: usize) -> Option<Range<usize>>;

    /// Find the start (byte index) of the previous line, the line before the one which `index` is within.
    ///
    /// Returns [`None`] if there is no previous line.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //                     ^
    /// let i = 9; // 'a'
    ///
    /// let start = text.find_prev_line_start(i).unwrap();
    ///
    /// assert_eq!(start, 4);
    /// assert_eq!(&text[start..], "bar\nbaz");
    /// ```
    fn find_prev_line_start(&self, index: usize) -> Option<usize>;

    /// Find the end (byte index) of the previous line, the line before the one which `index` is within.
    ///
    /// Note the end is the last character, excluding `\n` and `\r\n`.
    ///
    /// Returns [`None`] if there is no previous line.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //                     ^
    /// let i = 9; // 'a'
    ///
    /// let end = text.find_prev_line_end(i).unwrap();
    ///
    /// assert_eq!(end, 7);
    /// assert_eq!(&text[..end], "foo\nbar");
    /// ```
    fn find_prev_line_end(&self, index: usize) -> Option<usize>;

    /// Find the start and end (byte index) of the previous line, the line before the one which `index` is within.
    ///
    /// Note the end is the last character, excluding `\n` and `\r\n`.
    ///
    /// Returns [`None`] if there is no previous line.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use line_span::LineSpanExt;
    /// let text = "foo\nbar\nbaz";
    /// //                     ^
    /// let i = 9; // 'a'
    ///
    /// let range = text.find_prev_line_range(i).unwrap();
    /// assert_eq!(range, 4..7);
    ///
    /// let line = &text[range];
    /// assert_eq!(line, "bar");
    /// ```
    fn find_prev_line_range(&self, index: usize) -> Option<Range<usize>>;
}

impl LineSpanExt for str {
    #[inline]
    fn line_spans(&self) -> LineSpanIter<'_> {
        LineSpanIter::from(self)
    }

    #[inline]
    fn find_line_start(&self, index: usize) -> usize {
        self[..index].rfind('\n').map_or(0, |i| i + 1)
    }

    #[inline]
    fn find_line_end(&self, index: usize) -> usize {
        let end: usize = self[index..]
            .find('\n')
            .map_or_else(|| self.len(), |i| index + i);
        if (end > 0) && (self.as_bytes()[end - 1] == b'\r') {
            end - 1
        } else {
            end
        }
    }

    #[inline]
    fn find_line_range(&self, index: usize) -> Range<usize> {
        let start = self.find_line_start(index);
        let end = self.find_line_end(index);
        start..end
    }

    #[inline]
    fn find_next_line_start(&self, index: usize) -> Option<usize> {
        let i = self[index..].find('\n')?;
        Some(index + i + 1)
    }

    #[inline]
    fn find_next_line_end(&self, index: usize) -> Option<usize> {
        let index = self.find_next_line_start(index)?;
        let index = self.find_line_end(index);
        Some(index)
    }

    #[inline]
    fn find_next_line_range(&self, index: usize) -> Option<Range<usize>> {
        let start = self.find_next_line_start(index)?;
        let end = self.find_line_end(start);
        Some(start..end)
    }

    #[inline]
    fn find_prev_line_start(&self, index: usize) -> Option<usize> {
        let index = self.find_prev_line_end(index)?;
        let index = self.find_line_start(index);
        Some(index)
    }

    #[inline]
    fn find_prev_line_end(&self, index: usize) -> Option<usize> {
        let mut end: usize = self[..index].rfind('\n')?;
        if (end > 0) && (self.as_bytes()[end - 1] == b'\r') {
            end -= 1;
        }
        Some(end)
    }

    #[inline]
    fn find_prev_line_range(&self, index: usize) -> Option<Range<usize>> {
        let end = self.find_prev_line_end(index)?;
        let start = self.find_line_start(end);
        Some(start..end)
    }
}

/// Use [`LineSpanExt::find_line_start()`] instead.
#[inline]
pub fn find_line_start(text: &str, index: usize) -> usize {
    text.find_line_start(index)
}

/// Use [`LineSpanExt::find_line_end()`] instead.
pub fn find_line_end(text: &str, index: usize) -> usize {
    text.find_line_end(index)
}

/// Use [`LineSpanExt::find_line_range()`] instead.
#[inline]
pub fn find_line_range(text: &str, index: usize) -> Range<usize> {
    text.find_line_range(index)
}

/// Use [`LineSpanExt::find_next_line_start()`] instead.
#[inline]
pub fn find_next_line_start(text: &str, index: usize) -> Option<usize> {
    text.find_next_line_start(index)
}

/// Use [`LineSpanExt::find_next_line_end()`] instead.
#[inline]
pub fn find_next_line_end(text: &str, index: usize) -> Option<usize> {
    text.find_next_line_end(index)
}

/// Use [`LineSpanExt::find_next_line_range()`] instead.
#[inline]
pub fn find_next_line_range(text: &str, index: usize) -> Option<Range<usize>> {
    text.find_next_line_range(index)
}

/// Use [`LineSpanExt::find_prev_line_start()`] instead.
#[inline]
pub fn find_prev_line_start(text: &str, index: usize) -> Option<usize> {
    text.find_prev_line_start(index)
}

/// Use [`LineSpanExt::find_prev_line_end()`] instead.
#[inline]
pub fn find_prev_line_end(text: &str, index: usize) -> Option<usize> {
    text.find_prev_line_end(index)
}

/// Use [`LineSpanExt::find_prev_line_range()`] instead.
#[inline]
pub fn find_prev_line_range(text: &str, index: usize) -> Option<Range<usize>> {
    text.find_prev_line_range(index)
}

/// Get the start and end (byte index) range (`Range<usize>`), where `substring`
/// is located in `string`.
/// The returned range is relative to `string`.
///
/// Returns `Some` if `substring` is a part of `string`, otherwise `None`.
///
/// *For an unchecked version, check out [`str_to_range_unchecked()`].*
///
/// # Example
///
/// ```rust
/// # use line_span::str_to_range;
/// let string1 = "Foo Bar Baz";
/// let string2 = "Hello World";
///
/// let substring = &string1[4..7]; // "Bar"
/// # assert_eq!(substring, "Bar");
///
/// // Returns `Some` as `substring` is a part of `string1`
/// assert_eq!(str_to_range(string1, substring), Some(4..7));
///
/// // Returns `None` as `substring` is not a part of `string2`
/// assert_eq!(str_to_range(string2, substring), None);
/// ```
///
/// # Example - Substring of Substring
///
/// Since the resulting range is relative to `string`, that implies
/// `substring` can be a substring of a substring of a substring of ...
/// and so on.
///
/// ```rust
/// # use line_span::str_to_range;
/// let s1 = "Foo Bar Baz";
///
/// // Substring of `s1`
/// let s2 = &s1[4..11]; // "Bar Baz"
///
/// // Substring of `s1`
/// let s3 = &s1[4..7]; // "Bar"
///
/// // Substring of `s2`, which is a substring of `s1`
/// let s4 = &s2[0..3]; // "Bar"
///
/// // Get the range of `s2` relative to `s1`
/// assert_eq!(str_to_range(s1, s2), Some(4..11));
///
/// // Get the range of `s3` relative to `s1`
/// assert_eq!(str_to_range(s1, s3), Some(4..7));
///
/// // Get the range of `s4` relative to `s1`
/// assert_eq!(str_to_range(s1, s4), Some(4..7));
///
/// // Get the range of `s4` relative to `s2`
/// assert_eq!(str_to_range(s2, s4), Some(0..3));
/// ```
#[inline]
pub fn str_to_range(string: &str, substring: &str) -> Option<Range<usize>> {
    let str_start = string.as_ptr() as usize;
    let sub_start = substring.as_ptr() as usize;

    if str_start <= sub_start {
        let start = sub_start - str_start;
        let end = start + substring.len();

        if (sub_start + substring.len()) <= (str_start + string.len()) {
            return Some(start..end);
        }
    }

    None
}

/// Get the start and end (byte index) range (`Range<usize>`), where `substring`
/// is located in `string`.
/// The returned range is relative to `string`.
///
/// If `substring` is not a part of `string`, it either panics or returns an
/// invalid range.
///
/// *For a safe version, check out [`str_to_range()`].*
///
/// # Panics
///
/// Panics if `substring` is not a substring of `string`. \*
///
/// \* Panicking depends on where the strings are located in memory. It might
/// not panic but instead return an invalid range.
///
/// # Example
///
/// ```
/// # use line_span::str_to_range_unchecked;
/// let string = "Foo Bar Baz";
///
/// let substring = &string[4..7]; // "Bar"
/// # assert_eq!(substring, "Bar");
///
/// assert_eq!(str_to_range_unchecked(string, substring), 4..7);
/// ```
///
/// # Example - Substring of Substring
///
/// Since the resulting range is relative to `string`, that implies
/// `substring` can be a substring of a substring of a substring of ...
/// and so on.
///
/// ```
/// # use line_span::str_to_range_unchecked;
/// let s1 = "Foo Bar Baz";
///
/// // Substring of `s1`
/// let s2 = &s1[4..11]; // "Bar Baz"
///
/// // Substring of `s1`
/// let s3 = &s1[4..7]; // "Bar"
///
/// // Substring of `s2`, which is a substring of `s1`
/// let s4 = &s2[0..3]; // "Bar"
///
/// // Get the range of `s2` relative to `s1`
/// assert_eq!(str_to_range_unchecked(s1, s2), 4..11);
///
/// // Get the range of `s3` relative to `s1`
/// assert_eq!(str_to_range_unchecked(s1, s3), 4..7);
///
/// // Get the range of `s4` relative to `s1`
/// assert_eq!(str_to_range_unchecked(s1, s4), 4..7);
///
/// // Get the range of `s4` relative to `s2`
/// assert_eq!(str_to_range_unchecked(s2, s4), 0..3);
/// ```
#[inline]
pub fn str_to_range_unchecked(string: &str, substring: &str) -> Range<usize> {
    let start = (substring.as_ptr() as usize) - (string.as_ptr() as usize);
    let end = start + substring.len();
    start..end
}

/// `LineSpan` represents a single line. It is possible to
/// get a `&str` of the line both including and excluding
/// `\n` and `\r\n`.
///
/// ```no_run
/// use line_span::LineSpans;
///
/// let text = "foo\nbar\r\nbaz";
///
/// for span in text.line_spans() {
///     println!(
///         "{:>2?}: {:?} {:?}",
///         span.range(),
///         span.as_str(),
///         span.as_str_with_ending(),
///     );
/// }
/// ```
///
/// This will output the following:
///
/// ```text
/// 0.. 3: "foo" "foo\n"
/// 4.. 7: "bar" "bar\r\n"
/// 9..12: "baz" "baz"
/// ```
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct LineSpan<'a> {
    text: &'a str,
    start: usize,
    end: usize,
    ending: usize,
}

impl<'a> LineSpan<'a> {
    /// Returns the byte index of the start of the line.
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns the byte index of the end of the line,
    /// excluding the line ending part `\n` or `\r\n`.
    ///
    /// To include the line ending part, then use [`ending()`].
    ///
    /// [`ending()`]: Self::ending
    #[inline]
    pub fn end(&self) -> usize {
        self.end
    }

    /// Returns the byte index of the end of the line,
    /// including the line ending part `\n` or `\r\n`.
    ///
    /// To exclude the line ending part, then use [`end()`].
    ///
    /// [`end()`]: Self::end
    #[inline]
    pub fn ending(&self) -> usize {
        self.ending
    }

    /// Returns the byte index range of the start and
    /// end of the line, excluding the line ending
    /// part `\n` or `\r\n`.
    ///
    /// To include the line ending part, then use [`range_with_ending()`].
    ///
    /// [`range_with_ending()`]: Self::range_with_ending
    #[inline]
    pub fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    /// Returns the byte index range of the start and
    /// end of the line, including the line ending
    /// part `\n` or `\r\n`.
    ///
    /// To exclude the line ending part, then use [`range()`].
    ///
    /// [`range()`]: Self::range
    #[inline]
    pub fn range_with_ending(&self) -> Range<usize> {
        self.start..self.ending
    }

    /// Returns the start and end byte index range of
    /// the ending part of the line, i.e. just the
    /// `\n` or `\r\n` part.
    #[inline]
    pub fn ending_range(&self) -> Range<usize> {
        self.end..self.ending
    }

    /// Returns `&str` of the line, excluding `\n` and `\r\n`.
    ///
    /// To include the line ending part, then use [`as_str_with_ending()`].
    ///
    /// [`as_str_with_ending()`]: Self::as_str_with_ending
    #[inline]
    pub fn as_str(&self) -> &'a str {
        &self.text[self.range()]
    }

    /// Returns `&str` of the line, including `\n` and `\r\n`.
    ///
    /// To exclude the line ending part, then use [`as_str()`].
    ///
    /// [`as_str()`]: Self::as_str
    #[inline]
    pub fn as_str_with_ending(&self) -> &'a str {
        &self.text[self.range_with_ending()]
    }

    /// Returns the string slice of the line ending, i.e.
    /// just the `"\n"` or `"\r\n"` part or nothing, if
    /// there is no line ending.
    #[inline]
    pub fn ending_str(&self) -> &'a str {
        &self.text[self.ending_range()]
    }
}

impl<'a> Deref for LineSpan<'a> {
    type Target = str;

    /// Returns [`as_str()`].
    ///
    /// [`as_str()`]: Self::as_str
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<'a> From<LineSpan<'a>> for &'a str {
    /// Returns [`as_str()`].
    ///
    /// [`as_str()`]: LineSpan::as_str
    #[inline]
    fn from(span: LineSpan<'a>) -> &'a str {
        span.as_str()
    }
}

impl<'a> From<LineSpan<'a>> for Range<usize> {
    /// Returns [`range()`].
    ///
    /// [`range()`]: LineSpan::range
    #[inline]
    fn from(span: LineSpan<'a>) -> Range<usize> {
        span.range()
    }
}

impl<'a> fmt::Debug for LineSpan<'a> {
    /// Renders [`start()`], [`end()`], and [`ending()`]
    /// of [`LineSpan`] and [`as_str()`] as `"line"`.
    ///
    /// [`start()`]: Self::start
    /// [`end()`]: Self::end
    /// [`ending()`]: Self::ending
    /// [`as_str()`]: Self::as_str
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("LineSpan")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("ending", &self.ending)
            .field("line", &self.as_str())
            .finish()
    }
}

impl<'a> fmt::Display for LineSpan<'a> {
    /// Renders [`as_str`].
    ///
    /// [`as_str`]: struct.LineSpan.html#method.as_str
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(fmt)
    }
}

/// An iterator over [`LineSpan`]s.
///
/// This struct is created with the [`line_spans()`] method in the [`LineSpans`] trait.
/// See its documentation for more.
///
/// [`line_spans()`]: LineSpans::line_spans
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct LineSpanIter<'a> {
    text: &'a str,
    iter: Lines<'a>,
}

impl<'a> LineSpanIter<'a> {
    #[inline]
    fn from(text: &'a str) -> Self {
        Self {
            text,
            iter: text.lines(),
        }
    }
}

impl<'a> Iterator for LineSpanIter<'a> {
    type Item = LineSpan<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(line) = self.iter.next() {
            let Range { start, end } = str_to_range_unchecked(self.text, line);
            let ending = find_next_line_start(self.text, end).unwrap_or(self.text.len());

            Some(LineSpan {
                text: self.text,
                start,
                end,
                ending,
            })
        } else {
            None
        }
    }
}

impl<'a> FusedIterator for LineSpanIter<'a> {}

/// Trait which implements [`line_spans()`] to get a [`LineSpanIter`].
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
///
/// [`line_spans()`]: LineSpans::line_spans
pub trait LineSpans {
    /// Creates a [`LineSpanIter`].
    fn line_spans(&self) -> LineSpanIter<'_>;
}

impl LineSpans for str {
    #[inline]
    fn line_spans(&self) -> LineSpanIter<'_> {
        LineSpanIter::from(self)
    }
}

#[cfg(feature = "alloc")]
impl LineSpans for alloc::string::String {
    #[inline]
    fn line_spans(&self) -> LineSpanIter<'_> {
        LineSpanIter::from(self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::{LineSpan, LineSpanExt};

    #[test]
    fn test_line_spans() {
        let text = "\r\nfoo\nbar\r\nbaz\nqux\r\n\r";

        let mut it = text.line_spans();
        assert_eq!(Some(""), it.next().as_deref());
        assert_eq!(Some("foo"), it.next().as_deref());
        assert_eq!(Some("bar"), it.next().as_deref());
        assert_eq!(Some("baz"), it.next().as_deref());
        assert_eq!(Some("qux"), it.next().as_deref());
        assert_eq!(Some("\r"), it.next().as_deref());
        assert_eq!(None, it.next().as_deref());

        let mut it = text.line_spans().map(|span| span.range());
        assert_eq!(Some(0..0), it.next());
        assert_eq!(Some(2..5), it.next());
        assert_eq!(Some(6..9), it.next());
        assert_eq!(Some(11..14), it.next());
        assert_eq!(Some(15..18), it.next());
        assert_eq!(Some(20..21), it.next());
        assert_eq!(None, it.next());
    }

    #[test]
    fn test_line_spans_vs_lines() {
        let text = "\r\nfoo\nbar\r\nbaz\nqux\r\n\r";

        let mut iter_spans = text.line_spans();
        let mut iter_lines = text.lines();

        loop {
            let span = iter_spans.next();
            let line = iter_lines.next();

            assert_eq!(span.map(|s| s.as_str()), line);

            if span.is_none() {
                break;
            }
        }
    }

    #[test]
    fn test_line_span_ending() {
        let text = "\r\nfoo\nbar\r\nbaz\nqux\r\n\r";

        let lines = [
            ("", "\r\n"),
            ("foo", "foo\n"),
            ("bar", "bar\r\n"),
            ("baz", "baz\n"),
            ("qux", "qux\r\n"),
            ("\r", "\r"),
        ];

        let mut iter = text.line_spans();

        for &expected in lines.iter() {
            let actual = iter.next();
            let actual = actual.map(|span| (span.as_str(), span.as_str_with_ending()));

            assert_eq!(Some(expected), actual);
        }

        assert_eq!(None, iter.next());
    }

    #[test]
    fn lib_example() {
        // If this example is changed, then update both the
        // code and the output in lib.rs and README.md.

        let text = "foo\nbar\r\nbaz";

        let spans = [
            LineSpan {
                text,
                start: 0,
                end: 3,
                ending: 4,
            },
            LineSpan {
                text,
                start: 4,
                end: 7,
                ending: 9,
            },
            LineSpan {
                text,
                start: 9,
                end: 12,
                ending: 12,
            },
        ];

        #[rustfmt::skip]
        let lines = [
            ("foo", "foo\n"),
            ("bar", "bar\r\n"),
            ("baz", "baz"),
        ];

        assert_eq!(spans.len(), lines.len());

        let mut iter = text.line_spans();

        for (expected, (line_end, line_ending)) in spans.iter().zip(&lines) {
            let actual = iter.next();
            assert_eq!(Some(*expected), actual);

            let actual = actual.unwrap();
            assert_eq!(*line_end, actual.as_str());
            assert_eq!(*line_ending, actual.as_str_with_ending());
        }

        assert_eq!(None, iter.next());
    }
}
