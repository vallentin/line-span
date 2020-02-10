# line-span

[![Build Status](https://travis-ci.org/vallentin/line-span.svg?branch=master)](https://travis-ci.org/vallentin/line-span)
[![Latest Version](https://img.shields.io/crates/v/line-span.svg)](https://crates.io/crates/line-span)
[![Docs](https://docs.rs/line-span/badge.svg)](https://docs.rs/line-span)
[![License](https://img.shields.io/github/license/vallentin/line-span.svg)](https://github.com/vallentin/line-span)

This crate features utilities for finding the start, end, and range of lines
from a byte index.
Further also being able to find the next and previous line, from an arbitrary byte index.

**Current Line:**

- [`find_line_start`](https://docs.rs/line-span/*/line_span/fn.find_line_start.html) to find the start of the current line.
- [`find_line_end`](https://docs.rs/line-span/*/line_span/fn.find_line_end.html) to find the end of the current line.
- [`find_line_range`](https://docs.rs/line-span/*/line_span/fn.find_line_range.html) to find the start and end current line.

**Next Line:**

- [`find_next_line_start`](https://docs.rs/line-span/*/line_span/fn.find_next_line_start.html) to find the start of the next line.
- [`find_next_line_end`](https://docs.rs/line-span/*/line_span/fn.find_next_line_end.html) to find the end of the next line.
- [`find_next_line_range`](https://docs.rs/line-span/*/line_span/fn.find_next_line_range.html) to find the start and end of the next line.

**Previous Line:**

- [`find_prev_line_start`](https://docs.rs/line-span/*/line_span/fn.find_prev_line_start.html) to find the start of the previous line.
- [`find_prev_line_end`](https://docs.rs/line-span/*/line_span/fn.find_prev_line_end.html) to find the end of the previous line.
- [`find_prev_line_range`](https://docs.rs/line-span/*/line_span/fn.find_prev_line_range.html) to find both start and end of the previous line.

# [`LineSpan`] and [`LineSpanIter`]

The crate includes the [`LineSpanIter`] iterator. It is functionally equivalent to [`str::lines`],
with the addition that it includes the ability to get the start and end byte indices of each line.

An [`LineSpanIter`] can be created by calling [`line_spans`](https://docs.rs/line-span/*/line_span/trait.LineSpans.html#tymethod.line_spans), implemented in the [`LineSpans`] trait. The crate implements the [`LineSpans`] trait for [`str`] and [`String`].

Note, [`LineSpan`] implements [`Deref`] to [`&str`], so in general,
swapping [`lines`] to [`line_spans`] would not cause many issues.

```rust
use line_span::LineSpans;

let text = "foo\nbar\r\nbaz";

for span in text.line_spans() {
    println!("{:>2?}: {:?}", span.range(), span.as_str());
}
```

This will output the following:

```text
 0.. 3: "foo"
 4.. 7: "bar"
 9..12: "baz"
```

[`LineSpan`]: https://docs.rs/line-span/*/line_span/struct.LineSpan.html
[`LineSpanIter`]: https://docs.rs/line-span/*/line_span/struct.LineSpanIter.html
[`LineSpans`]: https://docs.rs/line-span/*/line_span/trait.LineSpans.html
[`line_spans`]: https://docs.rs/line-span/*/line_span/trait.LineSpans.html#tymethod.line_spans
[`Deref`]: https://doc.rust-lang.org/stable/std/ops/trait.Deref.html
[`&str`]: https://doc.rust-lang.org/stable/std/primitive.str.html
[`lines`]: https://doc.rust-lang.org/stable/std/primitive.str.html#method.lines
[`str::lines`]: https://doc.rust-lang.org/stable/std/primitive.str.html#method.lines

[`str`]: https://doc.rust-lang.org/stable/std/primitive.str.html
[`String`]: https://doc.rust-lang.org/stable/std/string/struct.String.html

# Current Line, Previous Line, and Next Line

```rust
use line_span::{find_line_range, find_next_line_range, find_prev_line_range};

let text = "foo\nbar\r\nbaz";
//                ^
let i = 5; // 'a' in "bar"

let curr_range = find_line_range(text, i);
let next_range = find_next_line_range(text, i).unwrap();
let prev_range = find_prev_line_range(text, i).unwrap();

assert_eq!(curr_range, 4..7);
assert_eq!(&text[curr_range], "bar");

assert_eq!(prev_range, 0..3);
assert_eq!(&text[prev_range], "foo");

assert_eq!(next_range, 9..12);
assert_eq!(&text[next_range], "baz");
```
