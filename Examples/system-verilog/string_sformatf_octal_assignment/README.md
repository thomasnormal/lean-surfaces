# Literal octal `$sformatf` assignments

The legacy self-check extractor replays a blocking `$sformatf("%o", ...)` or
`$sformatf("%O", ...)` result assigned to a string when the operand is a known
0/1 integral literal. The existing octal renderer supplies the exact lower-case
text; unknown, dynamic, timed, and nonblocking forms remain loud.
