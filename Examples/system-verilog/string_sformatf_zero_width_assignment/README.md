# Zero-width binary and octal `$sformatf` assignments

The legacy self-check extractor replays blocking `%0b/%0B` and `%0o/%0O`
results assigned to strings for known 0/1 integral literals. Binary output
strips leading zeroes and octal output uses its minimal spelling; unknown,
dynamic, timed, and nonblocking forms remain loud.
