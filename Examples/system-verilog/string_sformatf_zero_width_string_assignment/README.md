# Zero-width string `$sformatf` assignments

The legacy self-check extractor replays a blocking `$sformatf("%0s", ...)` or
`$sformatf("%0S", ...)` result assigned to a string when its operand is an
ASCII literal or source-pure ASCII string history. A single literal prefix and
suffix around the conversion are retained as well; dynamic operands, other
formats, timed forms, and nonblocking writes remain loud.
