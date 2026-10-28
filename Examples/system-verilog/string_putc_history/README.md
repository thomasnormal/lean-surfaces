# Source-pure `string.putc` history

IEEE 1800-2023 §6.16.2 defines `putc` as a one-byte replacement. The
self-check extractor replays constant-index ASCII and low-byte integral calls
on a string established by blocking literal history. Zero, negative, and
out-of-range writes leave the source value unchanged. Dynamic indices or
characters, timing, control-dependent calls, aliases, and non-ASCII values
remain loud.
