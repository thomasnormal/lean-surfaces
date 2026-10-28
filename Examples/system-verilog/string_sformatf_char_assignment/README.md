# Literal character `$sformatf` assignments

The legacy self-check extractor replays a blocking `$sformatf("%c", ...)` or
`$sformatf("%C", ...)` result assigned to a string when the operand is a known
ASCII integral literal. Later string comparisons see the exact low-byte
character; unknown, zero, non-ASCII/control, dynamic, timed, and nonblocking
forms remain loud.
