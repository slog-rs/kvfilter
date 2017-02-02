//! Filter records by matching some of their keys against a sets of values

extern crate slog;
use std::collections::HashSet;
use std::fmt;

/// Serializer that serializes values to strings
///
/// TODO: Work for all types
/// TODO: Enhance perf. by using thread_local `String` buffer
struct ToStringSerializer {
    val: Option<String>,
}

impl ToStringSerializer {
    fn new() -> ToStringSerializer {
        ToStringSerializer { val: None }
    }

    fn value(&self) -> Option<&String> {
        self.val.as_ref()
    }
}

macro_rules! impl_empty_emit_for {
    ($f:ident, $ot:ty) => {
            fn $f(&mut self, _: &'static str, _: $ot)
                         -> slog::ser::Result {
                unreachable!();
            }
    };
}

macro_rules! impl_empty_emit_for_no_param {
    ($f:ident) => {
            fn $f(&mut self, _: &'static str)
                         -> slog::ser::Result {
                unreachable!();
            }
    };
}

impl slog::Serializer for ToStringSerializer {
    fn emit_str(&mut self, _: &'static str, val: &str) -> slog::ser::Result {
        self.val = Some(val.into());
        Ok(())
    }

    fn emit_none(&mut self, _: &'static str) -> slog::ser::Result {
        self.val = None;

        Ok(())
    }

    impl_empty_emit_for_no_param!(emit_unit);

    impl_empty_emit_for!(emit_usize, usize);
    impl_empty_emit_for!(emit_isize, isize);
    impl_empty_emit_for!(emit_bool, bool);
    impl_empty_emit_for!(emit_char, char);
    impl_empty_emit_for!(emit_u8, u8);
    impl_empty_emit_for!(emit_u16, u16);
    impl_empty_emit_for!(emit_u32, u32);
    impl_empty_emit_for!(emit_u64, u64);
    impl_empty_emit_for!(emit_i8, i8);
    impl_empty_emit_for!(emit_i16, i16);
    impl_empty_emit_for!(emit_i32, i32);
    impl_empty_emit_for!(emit_i64, i64);
    impl_empty_emit_for!(emit_f32, f32);
    impl_empty_emit_for!(emit_f64, f64);
    impl_empty_emit_for!(emit_arguments, &fmt::Arguments);
}

type FilteringMap = Vec<(String, HashSet<String>)>;

/// `Drain` filtering records using list of keys and values they
/// must have.
///
/// This `Drain` filters a log entry on a filtermap
/// that holds the key name in question and acceptable values
/// Key values are gathered up the whole hierarchy of inherited
/// loggers.
///
/// Example
/// =======
///
/// Logger( ... ; o!("thread" => "100");
/// log( ... ; "packet" => "send");
/// log( ... ; "packet" => "receive");
///
/// can be filtered on a map containing "thread" key component. If the
/// values contain "100" the log will be output, otherwise filtered.
/// The filtering map can contain further key "packet" and value "send".
/// With that the output for "receive" would be filtered.
///
/// More precisely, a key is ignored until present and an entry must
/// match for all the keys present any of the values to be left
/// unfiltered. Refer to the test for an example.
///
/// Usage
/// =====
///
/// Filtering in large systems that run multiple threads of same
/// code or have functionality of interest across many components,
/// modules, such as e.g. "sending packets" or "running FSM"
pub struct KVFilter<D: slog::Drain> {
    drain: D,
    filters: FilteringMap,
    level: slog::Level,
}

impl<D: slog::Drain> KVFilter<D> {
    /// Create `KVFilter`
    ///
    /// * `drain` - drain to be sent to
    /// * `level` - maximum level filtered, higher levels pass by
    /// * `filters` - LHashmap of keys with lists of allowed values
    pub fn new(drain: D, level: slog::Level, mut filters: FilteringMap) -> Self {
        KVFilter {
            drain: drain,
            level: level,
            // Reverse the order as the logger exposes it's
            // key-value pairs in reversed order
            filters: filters.drain(..).rev().collect(),
        }
    }

    fn is_match(&self, info: &slog::Record, logger_values: &slog::OwnedKeyValueList) -> bool {
        let mut pending_matches = &self.filters[..];

        // Can't use chaining here, as it's not possible to cast
        // SyncSerialize to Serialize
        for &(k, v) in info.values().iter().rev() {

            if pending_matches.is_empty() {
                return true;
            }

            let cur_match = &pending_matches[0];
            if k == cur_match.0 {
                let mut s = ToStringSerializer::new();
                v.serialize(info, k, &mut s).ok();
                if let Some(v_str) = s.value() {
                    if cur_match.1.contains(v_str) {
                        pending_matches = &pending_matches[1..]
                    }
                }
            }
        }

        for (k, v) in logger_values.iter() {

            if pending_matches.is_empty() {
                return true;
            }

            let cur_match = &pending_matches[0];
            if k == cur_match.0 {
                let mut s = ToStringSerializer::new();
                v.serialize(info, k, &mut s).ok();
                if let Some(v_str) = s.value() {
                    if cur_match.1.contains(v_str) {
                        pending_matches = &pending_matches[1..]
                    }
                }
            }
        }
        pending_matches.is_empty()
    }
}

impl<'a, D: slog::Drain> slog::Drain for KVFilter<D> {
    type Error = D::Error;

    fn log(&self, info: &slog::Record, logger_values: &slog::OwnedKeyValueList) -> Result<(), Self::Error> {
        if info.level().is_at_least(self.level)
            || self.is_match(info, logger_values) {
            self.drain.log(info, logger_values)
        } else {
            Ok(())
        }
    }
}
