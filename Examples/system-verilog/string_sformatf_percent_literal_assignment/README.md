# Escaped-percent `$sformatf` string assignments

The legacy self-check extractor replays a blocking `$sformatf` result assigned
to a string when its format contains one escaped percent (`%%`), one integral
conversion, and only literal ASCII text. Dynamic operands, multiple
conversions or escaped percents, timed forms, and nonblocking writes remain
loud.
