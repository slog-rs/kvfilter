//! Filter records by matching some of their keys against a sets of values while allowing
//! for records of level high enough to pass.

#![feature(drop_types_in_const)]
#![feature(thread_local)]

#[macro_use]
extern crate slog;

use std::collections::HashSet;
use std::fmt;
use std::option::Option;

use slog::KV;

// use std::cell::RefCell;
//#[thread_local]
//static mut TMP_STR: RefCell<String> = RefCell::new("".into());

struct FilteringSerializer<'a> {
	pending_matches: &'a [(String, HashSet<String>)],
	#[thread_local]
	tmp_str: String,
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
/// must have unless they are of a higher level than filtering applied.
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
/// More precisely
///   * a key is ignored until present in `KVFilterList`, otherwise an entry must
///     match for all the keys present in `KVFilterList` for any of the value given
///     for the key to pass the filter.
///   * Behavior on empty `KVFilterList` is undefined but normally anything should pass.
///
/// Usage
/// =====
///
/// Filtering in large systems that consist of multiple threads of same
/// code or have functionality of interest spread across many components,
/// modules, such as e.g. "sending packet" or "running FSM".
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
	    } else {
		    logger_values.serialize(record, &mut ser).unwrap();
		    ser.pending_matches.is_empty()
	    }
    }
}

impl<'a, D: slog::Drain> slog::Drain for KVFilter<D> {
    type Err = D::Err;
    type Ok = Option<D::Ok>;

	fn log(&self,
	       info: &slog::Record,
	       logger_values: &slog::OwnedKVList)
	       -> Result<Self::Ok, Self::Err> {
		println!("{:#?}", info.msg());

		if info.level() > self.level || self.is_match(info, logger_values) {
            self.drain.log(info, logger_values).map(Some)
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
	use super::KVFilter;
	use slog::{Level, Drain, Record, Logger, OwnedKVList};
	use std::collections::{HashSet};
	use std::iter::FromIterator;
	use std::cell::RefCell;
	use std::sync::Mutex;
	use std::fmt::Display;
	use std::fmt::Formatter;
	use std::fmt::Result as FmtResult;
	use std::io;

	const YES: &'static str = "YES";
	const NO: &'static str = "NO";

	#[derive(Debug)]
	struct StringDrain<'a> {
		output: Mutex<RefCell<&'a mut Option<Vec<String>>>>,
	}

	/// seriously hacked logger drain that just counts messages to make
	/// sure we have tests behaving correcly
	impl<'a> Drain for StringDrain<'a> {
		type Err = io::Error;
		type Ok = ();

		fn log(&self, info: &Record, _: &OwnedKVList) -> io::Result<()> {
			let lo = self.output.lock().unwrap();
			let mut lob = lo.borrow_mut();
			let fmt = format!("{:?}", info.msg());

			if !fmt.contains(YES) && !fmt.contains(NO) {
				panic!(fmt);
			}

			match *lob {
				&mut None => {}
				&mut Some(ref mut c) => c.push(fmt),
			}

			Ok(())
		}
	}

	impl<'a> Display for StringDrain<'a> {
		fn fmt(&self, f: &mut Formatter) -> FmtResult {
			write!(f, "none")
		}
	}

	static mut OUT: Option<Vec<String>> = None;

	#[test]
	/// get an asserting serializer, get a couple of loggers that
	/// have different nodes, components and see whether filtering
	/// is applied properly on the derived `Logger` copies
	/// @note: unfortunately, ugly unsafe block needed to gather
	///        data for the test in the background over statics
	///        drain itself is being moved into the filter & then logger.
	///        cleaner would be some channel work but it's just a test.
	fn nodecomponentlogfilter() {
		{
			assert!(Level::Critical < Level::Warning);

			unsafe {
				OUT = Some(Vec::new());

				let drain = StringDrain {
					output: Mutex::new(RefCell::new(&mut OUT)),
				};

				// build some small filter
				let filter = KVFilter::new(drain,
				                           Level::Info,
				                           vec![("thread".to_string(),
				                                 HashSet::from_iter(vec!["100".to_string(),
				                                                         "200".to_string()])),
				                                ("direction".to_string(),
				                                 HashSet::from_iter(vec!["send".to_string(),
				                                                         "receive".to_string()]))]);

				// Get a root logger that will log into a given drain.
				let mainlog = Logger::root(filter.fuse(),
				                           o!("version" => env!("CARGO_PKG_VERSION")));
				let sublog = mainlog.new(o!("thread" => "200", "sub" => "sub"));
				let subsublog = sublog.new(o!("direction" => "send"));
				let subsubsublog = subsublog.new(o!());

				let wrongthread = mainlog.new(o!("thread" => "100", "sub" => "sub"));

				info!(mainlog, "NO: filtered");
				info!(mainlog, "YES: unfiltered, on of thread matches, direction matches";
				"thread" => "100", "direction" => "send");
				warn!(mainlog, "YES: unfiltered"); // level high enough to pass anyway

				debug!(mainlog, "NO: filtered"); // level too low

				info!(mainlog, "NO: filtered";
				"thread" => "300", "direction" => "send");

				info!(wrongthread, "NO: filtered");

				info!(sublog, "NO: filtered sublog");

				info!(sublog, "YES: unfiltered sublog";
				"direction" => "receive");

				info!(subsubsublog,
				      "YES: unfiltered subsubsublog, direction on subsublog, thread on sublog");

				// test twice same keyword with right value will give filter match
				let stackedthreadslog = wrongthread.new(o!("thread" => "200"));

				info!(stackedthreadslog,
				      "YES: unfiltered since one of the threads matches from inherited";
				"direction" => "send");

				println!("resulting output: {:#?}", OUT);

				if let Some(ref output) = OUT {
					assert_eq!(output.len(), 5);
				} else {
					assert!(false);
				}
			}
		}
	}
}
