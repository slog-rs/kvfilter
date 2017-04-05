//! Filter records by matching some of their keys against a sets of values

extern crate slog;
use std::collections::HashSet;
use std::fmt;
use std::option::Option;

use slog::KV;

struct FilteringSerializer<'a> {
    pending_matches : &'a [(String, HashSet<String>)],
    // TODO: Make thread_local
    tmp_str : String,
}

impl<'a> slog::Serializer for FilteringSerializer<'a> {
    fn emit_arguments(&mut self, key: slog::Key, val: &fmt::Arguments) -> slog::Result {
        if self.pending_matches.is_empty() {
            return Ok(());
        }

        if key == self.pending_matches[0].0 {
            self.tmp_str.clear();
            fmt::write(&mut self.tmp_str, *val)?;

            if self.pending_matches[0].1.contains(&self.tmp_str) {
                self.pending_matches = &self.pending_matches[1..]
            }
        }

        Ok(())
    }
}

type KVFilterList = Vec<(String, HashSet<String>)>;

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
    filters: KVFilterList,
    level: slog::Level,
}

impl<D: slog::Drain> KVFilter<D> {
    /// Create `KVFilter`
    ///
    /// * `drain` - drain to be sent to
    /// * `level` - maximum level filtered, higher levels pass by
    /// * `filters` - LHashmap of keys with lists of allowed values
    pub fn new(drain: D, level: slog::Level, mut filters: KVFilterList) -> Self {
        KVFilter {
            drain: drain,
            level: level,
            // Reverse the order as the logger exposes it's
            // key-value pairs in reversed order
            filters: filters.drain(..).rev().collect(),
        }
    }

    fn is_match(&self, record: &slog::Record, logger_values: &slog::OwnedKVList) -> bool {
        // Can't use chaining here, as it's not possible to cast
        // SyncSerialize to Serialize
        let mut ser = FilteringSerializer {
            pending_matches: &self.filters[..],
            tmp_str: String::new(),
        };

        record.kv().serialize(record, &mut ser).unwrap();

        if ser.pending_matches.is_empty() {
            return true;
        }

        logger_values.serialize(record, &mut ser).unwrap();

        ser.pending_matches.is_empty()
    }
}

impl<'a, D: slog::Drain> slog::Drain for KVFilter<D> {
    type Err = D::Err;
    type Ok = Option<D::Ok>;

    fn log(&self, info: &slog::Record, logger_values: &slog::OwnedKVList) -> Result<Self::Ok, Self::Err> {
        if info.level().is_at_least(self.level)
            || self.is_match(info, logger_values) {
            self.drain.log(info, logger_values).map(Some)
        } else {
            Ok(None)
        }
    }
}
