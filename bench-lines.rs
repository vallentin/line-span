// Benchmarks show a faster run-time performance, at the cost
// of a bit of memory.
//
// The old `LineSpanIter` had a smaller memory footprint of 32 bytes,
// while the new one using `lines()` requires 88 bytes.

#![feature(test)]
extern crate test;

use std::ops::Range;

use test::Bencher;

use line_span::{find_line_end, find_next_line_start, str_to_range_unchecked};

const TEXT: &str = "Foo\nBar\nBaz\n";
const N: usize = 1000;

#[allow(dead_code)]
struct LineSpan<'a> {
    text: &'a str,
    start: usize,
    end: usize,
}

#[bench]
fn bench_line_span_iter_before(b: &mut Bencher) {
    let text = TEXT.repeat(N);
    let text = text.as_str();

    b.iter(|| {
        let mut start = 0;

        loop {
            let end = find_line_end(text, start);

            if let Some(next_start) = find_next_line_start(text, end) {
                test::black_box(LineSpan { text, start, end });

                start = next_start;
            } else {
                break;
            }
        }
    });
}

#[bench]
fn bench_line_span_iter_after(b: &mut Bencher) {
    let text = TEXT.repeat(N);
    let text = text.as_str();

    b.iter(|| {
        let it = text.lines().map(|line| {
            let Range { start, end } = str_to_range_unchecked(text, line);
            LineSpan { text, start, end }
        });

        for span in it {
            test::black_box(span);
        }
    });
}
