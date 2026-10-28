# Literal binary `$sformatf` assignments

The legacy self-check extractor replays a blocking `$sformatf("%b", ...)` or
`$sformatf("%B", ...)` result assigned to a string when the operand is a known
0/1 integral literal. The literal's packed width is retained in the binary text;
unknown, dynamic, timed, and nonblocking forms remain loud.
