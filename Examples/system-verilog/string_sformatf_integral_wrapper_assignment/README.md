# Integral wrapper `$sformatf` assignments

The legacy self-check extractor replays a blocking `$sformatf` result assigned
to a string when its format contains one integral conversion and only literal
ASCII text before or after it. Decimal, hexadecimal, binary, octal, and
character conversions are covered; dynamic operands, multiple conversions,
escaped-percent formats, timed forms, and nonblocking writes remain loud.
