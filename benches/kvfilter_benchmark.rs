#[macro_use]
extern crate criterion;
#[macro_use]
extern crate slog;
extern crate slog_kvfilter;

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use criterion::Criterion;
use slog::{Drain, Logger, Never, Record, OwnedKVList, Level};
use slog_kvfilter::{EvaluationOrder, FilterSpec, KVFilter};

#[derive(Debug, Clone)]
pub struct CountingDrain {
    count: Arc<AtomicUsize>
}

impl Drain for CountingDrain {
    type Ok = ();
    type Err = Never;

    fn log(&self, _: &Record, _: &OwnedKVList) -> Result<(), Never> {
        self.count.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    #[inline]
    fn is_enabled(&self, _: Level) -> bool {
        true
    }
}

struct Tester {
    log: Logger,
    count: Arc<AtomicUsize>,
}

impl Tester {
    fn assert_count(&self, expected_count: usize) {
        let actual_count = self.count.load(Ordering::Relaxed);
        assert_eq!(expected_count, actual_count)
    }
}

fn new_tester(spec: FilterSpec, evaluation_order: EvaluationOrder) -> Tester {
    let count = Arc::new(AtomicUsize::new(0));
    let drain = KVFilter::new(
        CountingDrain { count: Arc::clone(&count) },
        spec,
        evaluation_order,
    );
    Tester {
        log: Logger::root(drain.fuse(), o!("key_foo" => "value_foo")),
        count,
    }
}


// simple AND use_case - useful for comparison with original KVFilter in simple cases
fn simple_and_benchmark(c: &mut Criterion) {
    let tester = {
        let match_kv = FilterSpec::match_kv;

        let filter_spec = FilterSpec::all_of(&[
            match_kv("some_key", "some_value"),
            match_kv("another_key", "another_value"),
        ]);

        new_tester(filter_spec, EvaluationOrder::LoggerAndMessage)
    };

    let mut first_iteration = true;
    c.bench_function("simple AND", move |b| {
        b.iter(|| {
            info!(tester.log, "ACCEPT";
                "some_key" => "some_value",
                "another_key" => "another_value",
            );

            debug!(tester.log, "REJECT";
                "some_key" => "some_value",
            );

            trace!(tester.log, "REJECT";
                "another_key" => "another_value",
                "bad_key" => "bad_key",
            );

            if first_iteration {
                tester.assert_count(1);
                first_iteration = false;
            }
        })
    });
}

// simple OR use_case - not expressible in original KVFilter
fn simple_or_benchmark(c: &mut Criterion) {
    let tester = {
        let match_kv = FilterSpec::match_kv;
        let level_at_least = FilterSpec::LevelAtLeast;

        let filter_spec = FilterSpec::any_of(&[
            match_kv("debug_key", "debug_value").and(level_at_least(Level::Debug)),
            match_kv("trace_key", "trace_value").and(level_at_least(Level::Trace)),
        ]);

        new_tester(filter_spec, EvaluationOrder::LoggerAndMessage)
    };

    let mut first_iteration = true;
    c.bench_function("simple OR", move |b| {
        b.iter(|| {
            info!(tester.log, "REJECT";
                "some_key" => "some_value",
                "another_key" => "another_value",
            );

            debug!(tester.log, "ACCEPT";
                "another_key" => "another_value",
                "debug_key" => "debug_value",
            );

            trace!(tester.log, "REJECT";
                "debug_key" => "debug_value",
                "another_key" => "another_value",
            );

            trace!(tester.log, "ACCEPT";
                "trace_key" => "trace_value",
                "another_key" => "another_value",
            );

            if first_iteration {
                tester.assert_count(2);
                first_iteration = false;
            }
        })
    });
}

// @przygienda use-case
fn przygienda_tester() -> Tester {
    let match_any = FilterSpec::match_any_value;

    // (key1 must be either value1a or value1b) AND key2 must be value2
    let positive_filter = FilterSpec::all_of(&[
        match_any(
            "some_key",
            &[
                "some_value_1",
                "some_value_2",
                "some_value_3",
                "some_value_4",
                "foo",
            ],
        ),
        match_any(
            "another_key",
            &[
                "another_value_1",
                "another_value_2",
                "another_value_3",
                "another_value_4",
                "bar",
            ],
        ),
        match_any(
            "key_foo",
            &[
                "foo_value_1",
                "foo_value_2",
                "foo_value_3",
                "foo_value_4",
                "value_foo",
            ],
        ),
        match_any(
            "bar_key",
            &[
                "bar_value_1",
                "bar_value_2",
                "bar_value_3",
                "bar_value_4",
                "xyz",
            ],
        ),
        match_any(
            "ultimate_key",
            &[
                "ultimate_value_1",
                "ultimate_value_2",
                "ultimate_value_3",
                "ultimate_value_4",
                "xyz",
            ],
        ),
    ]);

    // neg_key1 must be neg_value1 OR neg_key2 must be neg_value2a OR neg_key2 must be neg_value2b
    let negative_filter = FilterSpec::any_of(&[
        match_any(
            "some_negative_key",
            &[
                "some_value_1",
                "some_value_2",
                "some_value_3",
                "some_value_4",
                "foo",
            ],
        ),
        match_any(
            "another_negative_key",
            &[
                "some_value_1",
                "some_value_2",
                "some_value_3",
                "some_value_4",
                "foo",
            ],
        ),
    ]);

    let filter_spec = positive_filter.and(negative_filter.not());
    new_tester(filter_spec, EvaluationOrder::LoggerAndMessage)
}


fn przygienda_benchmark(c: &mut Criterion) {
    let tester = przygienda_tester();
    let mut first_iteration = true;
    c.bench_function("przygienda", move |b| {
        b.iter(|| {
            info!(tester.log, "ACCEPT";
                "some_key" => "some_value_4",
                "another_key" => "another_value_1",
                "bar_key" => "bar_value_3",
                "ultimate_key" => "ultimate_value_3",
            );

            info!(tester.log, "REJECT - negative filter";
                "some_key" => "some_value_4",
                "another_key" => "another_value_1",
                "bar_key" => "bar_value_3",
                "ultimate_key" => "ultimate_value_3",
                "some_negative_key" => "foo"
            );

            info!(tester.log, "REJECT - not all keys present";
                "some_key" => "some_value_4",
                "another_key" => "another_value_1",
            );

            if first_iteration {
                tester.assert_count(1);
                first_iteration = false;
            }
        })
    });
}

criterion_group!(benches, simple_and_benchmark, przygienda_benchmark, simple_or_benchmark);
criterion_main!(benches);
