# Source-pure string `$sformatf` assignments

The legacy self-check extractor replays a blocking `$sformatf("%s", ...)` or
`$sformatf("%S", ...)` result assigned to a string when its operand is an ASCII
literal or an earlier source-pure ASCII string history. Later comparisons see
the exact text; dynamic operands, unsupported formats, timed forms, and
nonblocking writes remain loud.
