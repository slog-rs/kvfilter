<p align="center">

  <a href="https://github.com/slog-rs/slog">
  <img src="https://cdn.rawgit.com/slog-rs/misc/master/media/slog.svg" alt="slog-rs logo">
  </a>
  <br>

  <a href="https://travis-ci.org/slog-rs/kvfilter">
      <img src="https://img.shields.io/travis/slog-rs/kvfilter/master.svg" alt="Travis CI Build Status">
  </a>

  <a href="https://crates.io/crates/slog-kvfilter">
      <img src="https://img.shields.io/crates/d/slog-kvfilter.svg" alt="slog-kvfilter on crates.io">
  </a>

  <a href="https://gitter.im/slog-rs/slog">
      <img src="https://img.shields.io/gitter/room/slog-rs/slog.svg" alt="slog-rs Gitter Chat">
  </a>
</p>

# slog-kvfilter  - Key values and Regex based filter Drain for [slog-rs]

Filter records by matching their messages, keys and values. Records can be matched

 - based on logging level (debug, info, warn, ...)
 - regular expression on record message
 - keys and values
 - simple filters can be arbitrarily composed using `And`, `Or` and `Not` expressions


**slog-kvfilter has undergone a complete rewrite as of version 0.7.0.
The API has changed. See [this issue](https://github.com/slog-rs/kvfilter/issues/15)
for details.**

slog-kvfilter documentation can be found [here](https://docs.rs/slog-kvfilter/*/slog_kvfilter/).

For more information, help, to report issues etc. see
[slog-kvfilter][slog-kvfilter] and [slog-rs][slog-rs].

[slog-kvfilter]: https://github.com/slog-rs/kvfilter/
[slog-rs]: https://github.com/slog-rs/slog