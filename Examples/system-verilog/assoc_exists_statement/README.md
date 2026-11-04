# Discarded finite associative-array `exists`

This fixture covers IEEE 1800-2023 associative-array `exists(index)` in
expression-statement position. A literal-key call has no represented effect
when its one-bit result is discarded, so the extractor erases that call only
after the finite presence-cell recognizer has validated the source history.
Dynamic keys, aliases, control-dependent calls, and other aggregate uses stay
loud. The following value-position `exists` call checks that the discarded
call did not alter the stored value or presence bit.
