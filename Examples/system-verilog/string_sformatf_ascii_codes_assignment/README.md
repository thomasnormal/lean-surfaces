# ASCII-code `$sformatf` string assignments

The legacy self-check extractor replays a blocking `%s` or `%S` `$sformatf`
result assigned to a string when its operand is a known integral literal whose
width is a multiple of eight and every byte is printable ASCII. Unknown,
non-byte-width, NUL/control, dynamic, timed, and nonblocking forms remain
loud.
