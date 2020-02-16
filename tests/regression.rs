// Keeping the old `LineSpanIter` implementation in here,
// to make sure that any future changes comply with the
// original implementation.

use std::ops::Range;

use line_span::{find_line_end, find_next_line_start, LineSpans};

struct OldLineSpanIter<'a> {
    text: &'a str,
    index: Option<usize>,
}

impl<'a> OldLineSpanIter<'a> {
    #[inline]
    fn from(text: &'a str) -> Self {
        Self {
            text,
            index: Some(0),
        }
    }
}

impl<'a> Iterator for OldLineSpanIter<'a> {
    type Item = (&'a str, Range<usize>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(start) = self.index {
            let end = find_line_end(self.text, start);

            self.index = find_next_line_start(self.text, end);

            Some((&self.text[start..end], start..end))
        } else {
            None
        }
    }
}

#[test]
fn test_correctness() {
    let text = "\r\nfoo\nbar\r\nbaz\nqux\r\n\r";

    let mut iter1 = OldLineSpanIter::from(text);
    let mut iter2 = text.line_spans();

    loop {
        let (span1, span2) = (iter1.next(), iter2.next());

        assert_eq!(
            span1.as_ref().map(|s| s.0),
            span2.as_ref().map(|s| s.as_str())
        );

        assert_eq!(
            span1.as_ref().map(|s| s.1.clone()),
            span2.as_ref().map(|s| s.range())
        );

        if span1.is_none() {
            break;
        }
    }
}
