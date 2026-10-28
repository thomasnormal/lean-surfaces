# Literal `$sformatf` string assignments

The legacy self-check extractor replays a direct integral-literal
`$sformatf("%h", ...)` or `$sformatf("%H", ...)` result when it is assigned to
a string. Later string comparisons and diagnostics observe the exact ASCII
hexadecimal text; dynamic operands and other formatting remain loud.
