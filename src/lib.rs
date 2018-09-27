//! Filter records by matching their keys and values, and allows arbitrary
//! Bool logic expressions to be used.
//!
//! See the unit tests (especially `test_complex_example` and `test_complex_example_2`) to see how to use it.
//!

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;

#[cfg(test)]
#[macro_use]
extern crate slog;

#[cfg(not(test))]
extern crate slog;

use slog::{Drain, Key, Level, OwnedKVList, Record, Serializer, KV};
use std::cell::Cell;
use std::fmt;

// ========== public KVFilter configuration

/// All the configuration for a KVFilter
///
/// If compiled with the "serde" feature, the config can be serialized and deserialized using Serde.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq)]
pub struct KVFilterConfig {
    /// The specification of the filtering to be applied to the message. See the `FilterSpec` docs.
    filter_spec: FilterSpec,
    /// See the `EvaluationOrder` docs
    evaluation_order: EvaluationOrder,
}

// https://serde.rs/remote-derive.html
#[derive(Serialize, Deserialize)]
#[serde(remote = "Level")]
enum LevelSerdeDef {
    Critical,
    Error,
    Warning,
    Info,
    Debug,
    Trace,
}

/// Specification of a filter. Filters are either simple filters like "Some Key and value must match this:",
/// or compound filters like `And`, `Or` that are recursively composed from another filters.
///
/// If compiled with the "serde" feature, the config can be serialized and deserialized using Serde.
///
/// See the tests for examples.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq)]
pub enum FilterSpec {
    /// Always accept
    Accept,
    /// Always reject
    Reject,
    /// Accept when the key and value match the specification
    MatchKV { key: String, value: String },
    /// Accept when logging level is at least given treshold.
    ///
    /// Example: message with level *Warning* will pass `FilterSpec::LevelAtLeast(Info)`
    #[serde(with = "LevelSerdeDef")]
    LevelAtLeast(Level),
    /// Accept when all the sub-filters accept. Sub-filter are evaluated left-to-right.
    ///
    /// Please note that slog processes KV arguments to `log!` right to left, that is e. g.
    /// `info!(log, "Msg"; "key1" => %value1, "key2" => %value2)` will first expand value2 and then value1.
    And(Box<FilterSpec>, Box<FilterSpec>),
    /// Accept when at least one of the sub-filters accepts. Sub-filter are evaluated left-to-right.
    ///
    /// Please note that slog processes KV arguments to `log!` right to left, that is e. g.
    /// `info!(log, "Msg"; "key1" => %value1, "key2" => %value2)` will first expand value2 and then value1.
    Or(Box<FilterSpec>, Box<FilterSpec>),
    /// Turns an Accept into a Reject and vice versa.
    Not(Box<FilterSpec>),
}

impl FilterSpec {
    pub fn match_kv(key: impl ToString, value: impl ToString) -> FilterSpec {
        FilterSpec::MatchKV {
            key: key.to_string(),
            value: value.to_string(),
        }
    }

    pub fn and(self, other: FilterSpec) -> FilterSpec {
        FilterSpec::And(Box::new(self), Box::new(other))
    }

    pub fn or(self, other: FilterSpec) -> FilterSpec {
        FilterSpec::Or(Box::new(self), Box::new(other))
    }

    pub fn not(self) -> FilterSpec {
        FilterSpec::Not(Box::new(self))
    }
}

/// The order of evaluation of message KVs and logger KVs
///
/// The keys and values to be logged come from two sources:
///
///  - some KVs are associated with the loggers, typically created with `new_log = log.new(o!("key": "value"))`
///  - some KVs are associated with the logged messages, e. g. `info!(log, "message"; "key" => "value")`
///
/// Evaluation order allows us to specify, which KVs will be used for message filtering, and what order will be used.
///
/// I presume in practice `LoggerOnly` and `LoggerAndMessage` will be the most commonly used orders.
///
///  - `LoggerOnly` means that only KVs associated with the loggers will be used for message filtering
///  - `LoggerAndMessage` means that first KVs associated with the loggers will be used for message filtering.
/// If the filter isn't determined by the loggers KVs, message KVs will be used.
///
/// This can have both performance and semantics implications. If you are curious,
/// see the comment at `KVFilter` for a more thorough discussion.
///
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq)]
pub enum EvaluationOrder {
    LoggerOnly,
    MessageOnly,
    LoggerAndMessage,
    MessageAndLogger,
}

/// The KVFilter itself. It implements `Drain`.
///
/// It passes messages matching the criteria specified by a given `config` into an underlying `drain`
/// and discards the rest.
/// ---
/// The rest of this documentation is a little bit difficult, both for me as a writer and for the reader.
/// I try to explain what happens under the hood when a message is being processed, and what performance
/// implications it may have.
///
/// ## TL;DR: I try hard not to do any unnecessary work within the limits set by slog implementation.
///
/// ## Long version:
///
/// When a log message is to be processed, we obtain two KV sets from two sources:
///
///  - KVs associated with the loggers, typically created with `new_log = log.new(o!("key": "value"))`
///  - KVs associated with the logged messages, e. g. `info!(log, "message"; "key" => "value")`
///
/// Each of the sets can be evaluated independently. Each KV set is evaluated in two stages:
///
///  ### 1. `kv_set.serialize(filtering_serializer)` is called for each KV set
///
/// This will eventually make `EvaluateFilterSerializer::emit_arguments`
/// called for each Key and Value in the KV set.
/// The important thing is that if there are any closures (`FnValue` and friends),
/// **all** of the closures in the KV set will be called at this step.
/// That means that if e. g. you don't need to filter on message KVs, just logger KVs
/// is enough for you, you can save a some CPU by using `EvaluationOrder::LoggerOnly`. That will
/// prevent the message closures from being called when a particular message is rejected based on logger KVs.
/// Also, if you  use e. g. `EvaluationOrder::LoggerAndMessage` and  a particular message is resolved
/// to be `Reject`-ed or `Accept`-ed early by just looking at the logger KV set, the message KV set will not
/// be `serialize()`d because the result is already known.
///
/// ### 2. `EvaluateFilterSerializer::emit_arguments(key: String, value: std::fmt::Arguments)` gets called for each KV
///
/// The `value` parameter is not a String, but a ` std::fmt::Arguments`
/// that needs to be turned into a String first so we can compare it to filters specified in the config.
///
/// We do two optimizations here:
///
/// a. Reuse the same String for expanding all the values to avoid some allocation
///
/// b. Only expand the value when we are not sure about the result yet. Again, if we don't need the value, because
/// we already know a message will be Rejected or Accepted, we don't expand the value at all. Remember from
/// bullet 1. that `kv_set.serialize(filtering_serializer)` will call `emit_arguments` with **all** the KVs from a
/// particular set, so we try hard not do any unnecessary work with them when not needed.
pub struct KVFilter<D> {
    drain: D,
    config: KVFilterConfig,
}

impl<D> KVFilter<D> {
    pub fn new_from_config(drain: D, config: KVFilterConfig) -> Self {
        KVFilter { drain, config }
    }

    pub fn new(drain: D, filter_spec: FilterSpec, evaluation_order: EvaluationOrder) -> Self {
        KVFilter {
            drain,
            config: KVFilterConfig {
                filter_spec,
                evaluation_order,
            },
        }
    }

    fn is_match(&self, record: &Record, logger_values: &OwnedKVList) -> bool {
        let mut evaluating_serializer = EvaluateFilterSerializer {
            filter: Filter::from_spec(&self.config.filter_spec),
            message_level: record.level(),
            tmp_string: String::new(),
        };

        macro_rules! serialize_and_return_if_decided {
            ($kv: expr) => {
                $kv
                    .serialize(record, &mut evaluating_serializer)
                    .unwrap(); // Is unwrap the right thing to do here?

                match evaluating_serializer.filter {
                    Filter::Accept => return true,
                    Filter::Reject => return false,
                    _ => {}
                }
            }
        }

        match self.config.evaluation_order {
            EvaluationOrder::LoggerOnly => {
                serialize_and_return_if_decided!(logger_values);
            }
            EvaluationOrder::MessageOnly => {
                serialize_and_return_if_decided!(record.kv());
            }
            EvaluationOrder::LoggerAndMessage => {
                serialize_and_return_if_decided!(logger_values);
                serialize_and_return_if_decided!(record.kv());
            }
            EvaluationOrder::MessageAndLogger => {
                serialize_and_return_if_decided!(record.kv());
                serialize_and_return_if_decided!(logger_values);
            }
        }

        fn final_evaluate_filter(filter: &mut Filter, level: Level) -> AcceptOrReject {
            match filter {
                Filter::Accept => AcceptOrReject::Accept,
                Filter::Reject => AcceptOrReject::Reject,
                Filter::LevelAtLeast(treshold) => {
                    if level.is_at_least(*treshold) {
                        AcceptOrReject::Accept
                    } else {
                        AcceptOrReject::Reject
                    }
                }
                Filter::MatchKV { .. } => AcceptOrReject::Reject,
                Filter::And(a, b) => {
                    if final_evaluate_filter(a, level) == AcceptOrReject::Accept
                        && final_evaluate_filter(b, level) == AcceptOrReject::Accept
                    {
                        AcceptOrReject::Accept
                    } else {
                        AcceptOrReject::Reject
                    }
                }
                Filter::Or(a, b) => {
                    if final_evaluate_filter(a, level) == AcceptOrReject::Accept
                        || final_evaluate_filter(b, level) == AcceptOrReject::Accept
                    {
                        AcceptOrReject::Accept
                    } else {
                        AcceptOrReject::Reject
                    }
                }
                Filter::Not(f) => {
                    if final_evaluate_filter(f, level) == AcceptOrReject::Accept {
                        AcceptOrReject::Reject
                    } else {
                        AcceptOrReject::Accept
                    }
                }
            }
        }

        let final_result = final_evaluate_filter(&mut evaluating_serializer.filter, record.level());

        match final_result {
            AcceptOrReject::Accept => true,
            AcceptOrReject::Reject => false,
        }
    }
}

impl<D> Drain for KVFilter<D>
where
    D: Drain,
{
    type Ok = Option<D::Ok>;
    type Err = Option<D::Err>;

    fn log(
        &self,
        record: &slog::Record,
        logger_values: &slog::OwnedKVList,
    ) -> Result<Self::Ok, Self::Err> {
        if self.is_match(record, logger_values) {
            self.drain
                .log(record, logger_values)
                .map(Some)
                .map_err(Some)
        } else {
            Ok(None)
        }
    }
}

// ========== Implementation

/// Simple enum to express a message is to be either Accepted or Rejected
#[derive(Clone, Copy, Debug, PartialEq)]
enum AcceptOrReject {
    Accept,
    Reject,
}

/// An actual filter in progress that get's progressively simplified during a log message evaluation.
/// A lightweight clone of FilterSpec.
#[derive(Debug, PartialEq)]
enum Filter<'a> {
    Accept,
    Reject,
    MatchKV { key: &'a str, value: &'a str },
    LevelAtLeast(Level),
    And(Box<Filter<'a>>, Box<Filter<'a>>),
    Or(Box<Filter<'a>>, Box<Filter<'a>>),
    Not(Box<Filter<'a>>),
}

impl<'a> Filter<'a> {
    fn from_spec<'b: 'a>(spec: &'b FilterSpec) -> Filter<'a> {
        match spec {
            FilterSpec::Accept => Filter::Accept,
            FilterSpec::Reject => Filter::Reject,
            FilterSpec::MatchKV { key, value } => Filter::MatchKV {
                key: &key,
                value: &value,
            },
            FilterSpec::LevelAtLeast(level) => Filter::LevelAtLeast(*level),
            FilterSpec::And(a, b) => Filter::And(
                Box::new(Filter::from_spec(&a)),
                Box::new(Filter::from_spec(&b)),
            ),
            FilterSpec::Or(a, b) => Filter::Or(
                Box::new(Filter::from_spec(&a)),
                Box::new(Filter::from_spec(&b)),
            ),
            FilterSpec::Not(f) => Filter::Not(Box::new(Filter::from_spec(&f))),
        }
    }
}

/// Helper struct to turn arguments into a string and cache it.
/// The actual cached string is passed around as `tmp_string` to
/// the `is_equal` method. That is quite ugly, but I just didn't succeed adding a
/// tmp_string: &'a mut String
/// member to this struct and successfully negotiate its usage with the borrow checker.
struct ArgumentsValueMemo<'a> {
    arguments: &'a fmt::Arguments<'a>,
    is_serialized: Cell<bool>,
}

impl<'a> ArgumentsValueMemo<'a> {
    fn is_equal(&self, value: &str, tmp_string: &mut String) -> Result<bool, fmt::Error> {
        if !self.is_serialized.get() {
            tmp_string.clear();
            fmt::write(tmp_string, *self.arguments)?;
            self.is_serialized.set(true);
        }
        Ok(tmp_string == value)
    }
}

/// This is the filtering workhorse. It used to process a single log message.
/// It is set up with the logging level of the log message and a filter.
/// `tmp_str` is there just to avoid repeated string allocation and serves as
/// a temporary serialized string for `ArgumentsValueMemo`
struct EvaluateFilterSerializer<'a> {
    message_level: Level,
    filter: Filter<'a>,
    tmp_string: String,
}

impl<'a> Serializer for EvaluateFilterSerializer<'a> {
    fn emit_arguments(&mut self, key: Key, value: &fmt::Arguments) -> slog::Result {
        let mut value = ArgumentsValueMemo {
            arguments: value,
            is_serialized: Cell::new(false),
        };

        /// (Partially) in-place evaluate the filter for a particular key and value
        fn evaluate_filter_with_kv(
            filter: &mut Filter,
            level: Level,
            key: Key,
            value: &mut ArgumentsValueMemo,
            tmp_string: &mut String,
        ) -> slog::Result {
            let maybe_simplified_filter = match filter {
                Filter::Accept => None,
                Filter::Reject => None,
                Filter::LevelAtLeast(treshold) => {
                    if level.is_at_least(*treshold) {
                        Some(Filter::Accept)
                    } else {
                        Some(Filter::Reject)
                    }
                }
                Filter::MatchKV {
                    key: this_key,
                    value: this_value,
                } => {
                    if &key == this_key {
                        if value.is_equal(this_value, tmp_string)? {
                            Some(Filter::Accept)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                Filter::And(a, b) => {
                    evaluate_filter_with_kv(a, level, key, value, tmp_string)?;
                    if **a == Filter::Reject {
                        Some(Filter::Reject)
                    } else {
                        evaluate_filter_with_kv(b, level, key, value, tmp_string)?;
                        if **a == Filter::Accept {
                            if **b == Filter::Accept {
                                Some(Filter::Accept)
                            } else if **b == Filter::Reject {
                                Some(Filter::Reject)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                }
                Filter::Or(a, b) => {
                    evaluate_filter_with_kv(a, level, key, value, tmp_string)?;
                    if **a == Filter::Accept {
                        Some(Filter::Accept)
                    } else {
                        evaluate_filter_with_kv(b, level, key, value, tmp_string)?;
                        if **b == Filter::Accept {
                            Some(Filter::Accept)
                        } else if **a == Filter::Reject && **b == Filter::Reject {
                            Some(Filter::Reject)
                        } else {
                            None
                        }
                    }
                }
                Filter::Not(f) => {
                    evaluate_filter_with_kv(f, level, key, value, tmp_string)?;
                    if **f == Filter::Accept {
                        Some(Filter::Reject)
                    } else if **f == Filter::Reject {
                        Some(Filter::Accept)
                    } else {
                        None
                    }
                }
            };

            if let Some(simplified_filter) = maybe_simplified_filter {
                *filter = simplified_filter
            }

            Ok(())
        }

        evaluate_filter_with_kv(
            &mut self.filter,
            self.message_level,
            key,
            &mut value,
            &mut self.tmp_string,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::FilterSpec::*;
    use super::*;

    use std::fmt;
    use std::io;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};

    use slog::{Drain, FnValue, Level, Logger, OwnedKVList, Record};

    #[derive(Debug)]
    struct StringDrain {
        output: Arc<Mutex<Vec<String>>>,
    }

    impl<'a> Drain for StringDrain {
        type Ok = ();
        type Err = io::Error;

        fn log(&self, message: &Record, _: &OwnedKVList) -> io::Result<()> {
            let formatted = format!("{:?}", message.msg());
            if !formatted.contains("ACCEPT") && !formatted.contains("REJECT") {
                panic!(formatted);
            }

            self.output.lock().unwrap().push(formatted);

            Ok(())
        }
    }

    impl<'a> fmt::Display for StringDrain {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "String drain: {:#?}", self.output.lock().unwrap())
        }
    }

    /// A message that adds the message into the formatted_messages Vec as a side-effect of debug format
    struct TestingMessage {
        message: String,
        increment_on_format: Arc<AtomicUsize>,
    }

    impl TestingMessage {
        fn new(message: &str, increment_on_format: &Arc<AtomicUsize>) -> Self {
            TestingMessage {
                message: message.to_owned(),
                increment_on_format: Arc::clone(increment_on_format),
            }
        }
    }

    impl fmt::Debug for TestingMessage {
        fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            self.increment_on_format.fetch_add(1, Ordering::Relaxed);
            write!(f, "{}", self.message)
        }
    }

    struct Tester {
        accepted_messages: Arc<Mutex<Vec<String>>>,
        evaluated_log_values: Arc<AtomicUsize>,
        log: Logger,
    }

    impl Tester {
        fn new(filter_spec: FilterSpec, evaluation_order: EvaluationOrder) -> Self {
            let accepted_messages = Arc::new(Mutex::new(Vec::new()));
            let evaluated_log_values = Arc::new(AtomicUsize::new(0));
            let evaluated_log_values_clone = Arc::clone(&evaluated_log_values);
            let drain = StringDrain {
                output: accepted_messages.clone(),
            };
            let filter = KVFilter::new(drain, filter_spec, evaluation_order);
            let log = Logger::root(
                filter.fuse(),
                o!("main_log" => FnValue(move |_: &Record| {
                evaluated_log_values_clone.fetch_add(1, Ordering::Relaxed);
                "m"
            })),
            );

            Tester {
                accepted_messages,
                evaluated_log_values,
                log,
            }
        }

        fn assert_accepted(&self, expected_count: usize) {
            let accepted_messages = self.accepted_messages.lock().unwrap();
            for message in accepted_messages.iter() {
                assert!(
                    message.contains("ACCEPT"),
                    "Message without ACCEPT accepted: `{}`",
                    message
                )
            }
            let actual_count = accepted_messages.len();
            assert_eq!(expected_count, actual_count)
        }

        fn assert_evaluated_log_values(&self, expected_count: usize) {
            let actual_count = self.evaluated_log_values.load(Ordering::Relaxed);
            assert_eq!(expected_count, actual_count)
        }
    }

    #[test]
    fn test_lazy_format() {
        let filter_spec = FilterSpec::match_kv("sub_log_key", "sub_log_value")
            .or(FilterSpec::match_kv("key1", "value1"))
            .or(FilterSpec::match_kv("key2", "value2"));

        let tester = Tester::new(filter_spec, EvaluationOrder::LoggerAndMessage);

        let value1_evaluations = Arc::new(AtomicUsize::new(0));
        let value1 = TestingMessage::new("value1", &value1_evaluations);
        let value2_evaluations = Arc::new(AtomicUsize::new(0));
        let value2 = TestingMessage::new("value2", &value2_evaluations);
        let invalid_value_evaluations = Arc::new(AtomicUsize::new(0));
        let invalid_value = TestingMessage::new("invalid", &invalid_value_evaluations);

        let assert_evaluations = |value1: usize, value2: usize, invalid: usize| {
            assert_eq!(value1, value1_evaluations.load(Ordering::Relaxed));
            value1_evaluations.store(0, Ordering::Relaxed);
            assert_eq!(value2, value2_evaluations.load(Ordering::Relaxed));
            value2_evaluations.store(0, Ordering::Relaxed);
            assert_eq!(invalid, invalid_value_evaluations.load(Ordering::Relaxed));
            invalid_value_evaluations.store(0, Ordering::Relaxed);
        };

        let sub_log = tester.log.new(o!("sub_log_key" => "sub_log_value"));
        info!(sub_log, "ACCEPT because of sub_log_key"; "key1" => ?value1);
        assert_evaluations(0, 0, 0);

        info!(tester.log, "ACCEPT because of key1"; "key1" => ?value1);
        assert_evaluations(1, 0, 0);

        info!(tester.log, "ACCEPT because of key1"; "key1" => ?value1);
        assert_evaluations(1, 0, 0);

        info!(tester.log, "ACCEPT because of key2"; "key2" => ?value2);
        assert_evaluations(0, 1, 0);

        // Slog processes KVs in reverse order. If this ever changes, please update the relevant documentation for FilterSpec.
        info!(tester.log,
            "ACCEPT because of key1, don't process key2.";
            "key2" => ?invalid_value, "key1" => ?value1
        );
        assert_evaluations(1, 0, 0);

        info!(tester.log,
          "ACCEPT because of key2, key1 had to be processed first with negative result.";
          "key2" => ?value2, "key1" => ?invalid_value
        );
        assert_evaluations(0, 1, 1);

        info!(tester.log, "REJECT"; "key2" => ?invalid_value, "key1" => ?invalid_value );
        assert_evaluations(0, 0, 2);

        tester.assert_evaluated_log_values(7);
        tester.assert_accepted(6);
    }

    #[test]
    fn test_evaluation_order() {
        fn new_tester(evaluation_order: EvaluationOrder) -> Tester {
            Tester::new(
                FilterSpec::match_kv("key", "value").or(FilterSpec::match_kv("sub_log", "a")),
                evaluation_order,
            )
        }

        {
            let tester = new_tester(EvaluationOrder::LoggerOnly);
            let sub_log = tester.log.new(o!("sub_log" => "a"));

            info!(sub_log, "ACCEPT: Will be accepted because of sub log");
            tester.assert_accepted(1);
            info!(tester.log, "REJECT: Won't be accepted because message KVs are not evaluated"; "key" => "value");
            tester.assert_accepted(1);
            tester.assert_evaluated_log_values(2);
        }

        {
            let tester = new_tester(EvaluationOrder::MessageOnly);
            let sub_log = tester.log.new(o!("sub_log" => "a"));

            info!(
                sub_log,
                "REJECT: Will be rejected because log KVs are ignored"
            );
            tester.assert_accepted(0);
            info!(tester.log, "ACCEPT"; "key" => "value");
            tester.assert_accepted(1);
            tester.assert_evaluated_log_values(0);
        }

        {
            let tester = new_tester(EvaluationOrder::LoggerAndMessage);
            let sub_log = tester.log.new(o!("sub_log" => "a"));

            info!(tester.log, "ACCEPT"; "key" => "value");
            info!(sub_log, "ACCEPT: Will be accepted because of sub log");
            tester.assert_accepted(2);
            tester.assert_evaluated_log_values(2);
        }

        {
            let tester = new_tester(EvaluationOrder::MessageAndLogger);
            let sub_log = tester.log.new(o!("sub_log" => "a"));

            info!(tester.log, "ACCEPT"; "key" => "value");
            info!(sub_log, "ACCEPT: Will be accepted because of sub log");
            tester.assert_accepted(2);
            tester.assert_evaluated_log_values(1);
        }
    }

    #[test]
    fn test_sub_log() {
        {
            let tester = Tester::new(
                FilterSpec::match_kv("main_log", "m"),
                EvaluationOrder::LoggerAndMessage,
            );
            let sub_log = tester.log.new(o!("sub_log" => "a"));
            let sub_sub_log = sub_log.new(o!("sub_sub_log" => "b"));

            info!(tester.log, "ACCEPT: main log");
            info!(sub_log, "ACCEPT: sub log inherits the main_log KV");
            info!(sub_sub_log, "ACCEPT: the same for sub sub log");
            tester.assert_accepted(3);
        }

        {
            let tester = Tester::new(
                FilterSpec::match_kv("sub_sub_log", "b"),
                EvaluationOrder::LoggerAndMessage,
            );
            let sub_log = tester.log.new(o!("sub_log" => "a"));
            let sub_sub_log = sub_log.new(o!("sub_sub_log" => "b"));

            info!(
                tester.log,
                "REJECT: main log doesn't have the sub_sub_log key"
            );
            info!(sub_log, "REJECT: neither has the sub_log");
            info!(sub_sub_log, "ACCEPT: sub sub log has it");
            tester.assert_accepted(1);
        }
    }

    #[test]
    fn test_accept() {
        let tester = Tester::new(Accept, EvaluationOrder::LoggerAndMessage);
        info!(tester.log, "ACCEPT: Everything will pass");
        warn!(tester.log, "ACCEPT: Everything will pass");
        tester.assert_accepted(2);
    }

    #[test]
    fn test_reject() {
        let tester = Tester::new(Reject, EvaluationOrder::LoggerAndMessage);
        info!(tester.log, "REJECT: Everything will be rejected");
        warn!(tester.log, "REJECT: Everything will be rejected");
        tester.assert_accepted(0);
    }

    #[test]
    fn test_level_at_least() {
        let tester = Tester::new(
            LevelAtLeast(Level::Warning),
            EvaluationOrder::LoggerAndMessage,
        );
        info!(tester.log, "REJECT: Level too low");
        warn!(tester.log, "ACCEPT: Level good");
        error!(tester.log, "ACCEPT: Level good");
        tester.assert_accepted(2);
    }

    #[test]
    fn test_match_kv() {
        let tester = Tester::new(
            FilterSpec::match_kv("key", "value"),
            EvaluationOrder::LoggerAndMessage,
        );
        info!(tester.log, "ACCEPT: Good key"; "key" => "value");
        info!(tester.log, "REJECT"; "main_log" => "m");
        info!(tester.log, "REJECT"; "key" => "bad_value");
        info!(tester.log, "REJECT"; "bad_key" => "value");
        tester.assert_accepted(1);
    }

    #[test]
    fn test_and() {
        {
            let tester = Tester::new(
                FilterSpec::match_kv("key1", "value1").and(FilterSpec::match_kv("key2", "value2")),
                EvaluationOrder::LoggerAndMessage,
            );
            info!(tester.log, "ACCEPT"; "key1" => "value1", "key2" => "value2");
            info!(tester.log, "REJECT: key1"; "key1" => "value1");
            info!(tester.log, "REJECT: key1"; "key1" => "value1", "key2" => "boo");
            info!(tester.log, "REJECT: key2"; "key2" => "value2");
            info!(tester.log, "REJECT: key2"; "key1" => "boo", "key2" => "value2");
            info!(tester.log, "REJECT"; "key1" => "boo", "key2" => "boo");
            tester.assert_accepted(1);
        }
    }

    #[test]
    fn test_or() {
        {
            let tester = Tester::new(
                FilterSpec::match_kv("key1", "value1").or(FilterSpec::match_kv("key2", "value2")),
                EvaluationOrder::LoggerAndMessage,
            );
            info!(tester.log, "ACCEPT: key1"; "key1" => "value1");
            info!(tester.log, "ACCEPT: key1"; "key1" => "value1", "key2" => "boo");
            info!(tester.log, "ACCEPT: key2"; "key2" => "value2");
            info!(tester.log, "ACCEPT: key2"; "key1" => "boo", "key2" => "value2");
            info!(tester.log, "REJECT"; "key1" => "boo", "key2" => "boo");
            tester.assert_accepted(4);
        }
    }

    #[test]
    fn test_not() {
        {
            let tester = Tester::new(
                FilterSpec::match_kv("key1", "value1").not(),
                EvaluationOrder::LoggerAndMessage,
            );
            info!(tester.log, "REJECT: key1 match was turned into negative"; "key1" => "value1");
            info!(tester.log, "ACCEPT: No match, we turn it into a negative, that is Accept"; "key1" => "boo");
            tester.assert_accepted(1);
        }
    }

    #[test]
    fn test_complex_example() {
        // This is an example that mimics the original KVFilter.
        // We express the following example filter:
        // KVFilter {
        //   filters: key1 -> [value1a, value1b], key2 -> [value2]
        //   neg_filters: neg_key1 -> [neg_value1], neg_key2 -> [neg_value2a, neg_value2b]
        //   level: Debug (that actually means level at least Info)
        // }

        let match_kv = FilterSpec::match_kv;

        // (key1 must be either value1a or value1b) AND key2 must be value2
        let positive_filter = (match_kv("key1", "value1a").or(match_kv("key1", "value1b")))
            .and(match_kv("key2", "value2"));

        // neg_key1 must be neg_value1 OR neg_key2 must be neg_value2a OR neg_key2 must be neg_value2b
        let negative_filter = match_kv("neg_key1", "neg_value1")
            .or(match_kv("neg_key2", "neg_value2a"))
            .or(match_kv("neg_key2", "neg_value2b"));

        // We pass everything with level at least info, OR anything that matches the positive filter but not the negative one.
        let filter =
            FilterSpec::LevelAtLeast(Level::Info).or(positive_filter.and(negative_filter.not()));

        let tester = Tester::new(filter, EvaluationOrder::LoggerAndMessage);

        info!(tester.log, "ACCEPT: Info level");
        debug!(tester.log, "REJECT 1: Level too low");
        debug!(tester.log, "ACCEPT"; "key1" => "value1a", "key2" => "value2");
        debug!(tester.log, "ACCEPT"; "key1" => "value1b", "key2" => "value2");
        debug!(tester.log, "REJECT 2"; "key1" => "invalid", "key2" => "value2");
        debug!(tester.log, "REJECT 3"; "key1" => "value1b", "key2" => "invalid");
        debug!(tester.log, "REJECT 4"; "invalid" => "value1b", "key2" => "value2");
        debug!(tester.log, "REJECT 5"; "invalid" => "value1b", "key2" => "value2");
        debug!(tester.log, "REJECT 6"; "key1" => "value1a", "key2" => "value2", "neg_key1" => "neg_value1");
        debug!(tester.log, "REJECT 7"; "key1" => "value1a", "key2" => "value2", "neg_key2" => "neg_value2b");
        debug!(tester.log, "ACCEPT"; "key1" => "value1a", "key2" => "value2", "neg_key1" => "invalid");

        tester.assert_accepted(4);
    }

    #[test]
    fn test_complex_example_2() {
        // This is an example that implements the behavior requested at this issue:
        // https://github.com/sile/sloggers/issues/9#issuecomment-422685244
        //
        // The requested behavior:
        //
        // 1. pass all records with ("subsystem": "A1" || "subsystem": "A2") && level at least debug
        // 2. pass all records with (subsystem": "B1" || "subsystem": "B2") && level at least info
        // 3. pass all records with level at least warn
        // 4. reject all other records
        // In all cases, make decisions based only on the LOGGER keys and values,
        // don't take the message KVs into account

        let match_kv = FilterSpec::match_kv;

        let subsystem_a = (match_kv("subsystem", "A1").or(match_kv("subsystem", "A2")))
            .and(FilterSpec::LevelAtLeast(Level::Debug));
        let subsystem_b = (match_kv("subsystem", "B1").or(match_kv("subsystem", "B2")))
            .and(FilterSpec::LevelAtLeast(Level::Info));
        let filter = subsystem_a
            .or(subsystem_b)
            .or(FilterSpec::LevelAtLeast(Level::Warning));

        // EvaluationOrder::Logger means that only the logger KVs will be used for message filtering
        let tester = Tester::new(filter, EvaluationOrder::Logger);
        let subsystem_a1 = tester.log.new(o!("subsystem" => "A1"));
        let subsystem_a2 = tester.log.new(o!("subsystem" => "A2"));
        let subsystem_b1 = tester.log.new(o!("subsystem" => "B1"));
        let subsystem_b2 = tester.log.new(o!("subsystem" => "B2"));
        let subsystem_xxx = tester.log.new(o!("subsystem" => "XXX"));

        // Rule 1
        debug!(subsystem_a1, "ACCEPT");
        debug!(subsystem_a2, "ACCEPT");
        debug!(subsystem_xxx, "REJECT debug XXX");
        debug!(subsystem_xxx, "REJECT debug XXX, message KV is discarded"; "subsystem" => "A1");

        // Rule 2
        debug!(subsystem_b1, "REJECT");
        info!(subsystem_b1, "ACCEPT");
        info!(subsystem_b2, "ACCEPT");
        info!(subsystem_xxx, "REJECT info XXX");

        // Rule 3
        warn!(tester.log, "ACCEPT: Info level");

        // Rule 4
        info!(tester.log, "REJECT: Level too low");

        tester.assert_accepted(5);
    }
}
