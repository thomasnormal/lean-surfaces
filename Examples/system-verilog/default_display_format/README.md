# Default display formatting

IEEE 1800-2023 §21.2.1.1 gives a default format when `$display` or `$write`
has no format string: integral expressions use decimal output and strings use
character output. The legacy self-check extractor lowers represented integral
values and source-pure ASCII string histories to the existing `%d`/`%s`
renderer. Unpacked values, opaque real values, and dynamic strings remain loud.

The fixture prints the decimal value twice (the `$write` is followed by a bare
`$display`) and then the source-pure string.
