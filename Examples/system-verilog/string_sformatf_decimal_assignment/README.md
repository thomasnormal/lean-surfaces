# Literal decimal `$sformatf` assignments

The legacy self-check extractor replays blocking `$sformatf("%d", ...)`,
`$sformatf("%D", ...)`, and zero-width decimal results assigned to strings when
the operand is a known integral literal. The existing decimal renderer supplies
the exact text; unknown, dynamic, timed, and nonblocking forms remain loud.
