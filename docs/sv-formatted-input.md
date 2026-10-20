# Integral formatted input

The legacy self-check surface admits a direct blocking assignment
`count = $sscanf(input, literal_format, outputs...)` for the integral
subset of IEEE 1800-2023 §21.3.4.3. Extraction retains the input expression,
format text and output targets. It never scans the input or replaces the
call with its observed result.

`LeanModels/Sv/FormattedInput.lean` implements the pure scanner. The
self-check interpreter evaluates the input once, obtains the successful
conversion prefix, then copies those values back in source order through
its existing packed-assignment rules. Each selector sees earlier output
writes. The enclosing count destination is resolved and written last.
A failed conversion leaves its destination and every following output
unchanged. Selected writes preserve neighboring bits; two-state targets
apply the same unknown-to-zero conversion as ordinary assignments.

| Conversion | Admitted behavior |
| --- | --- |
| `%b`, `%o`, `%h`, `%x` | Integral digits, separators and x/z/?; a leading unknown digit fills wider destinations; signs do not match |
| `%d` | Optional sign, decimal digits and separators, or a single x/z/? value; the latter occupies the low bit and is zero-extended |
| `%c` | Packed bytes without skipping whitespace; default width one; a shorter nonempty field succeeds |
| `%s` | Whitespace-delimited packed bytes, truncated or zero-extended to the destination width |
| `%v` | Three characters with a 0/1/x/z scalar in the third position; strength does not enter the integral result |

Conversions other than `%c` skip initial whitespace. Format whitespace
consumes input whitespace, ordinary characters match literally, and `%%`
consumes a percent sign. `*` suppresses a conversion without incrementing
the assignment count. Positive field widths limit characters for `%c`,
`%s` and decimal input; a decimal sign is outside that width. Separators
do not consume the width of based input. Strength input consumes three
characters regardless of field width. These details are checked against
complete independent execution transcripts, including continuation with
another conversion to expose exactly what was consumed.

Packed input is read most-significant byte first, with each NUL byte
acting as a space. Known empty or whitespace-only input has zero matches.
There is exactly one output argument per unsuppressed conversion. Unknown
packed bits, a literal mismatch requiring diagnostics, and invalid
strength scalars refuse at runtime. Additional output arguments remain an
admission refusal because their diagnostics are outside the output model.

General runtime strings, real-valued destinations, other format codes,
effectful inputs or selectors, nested call expressions, nonblocking or
compound assignments, and symbolic `sv-0.2` scanning remain loud. Timing
uses the existing scheduler's leaf delegation; no scanner-specific
scheduling rule is added. Extraction cleanliness does not imply that
other statements in the same program execute.

The authored [copyback fixture](../Examples/system-verilog/formatted_input/copyback.sv)
and [values fixture](../Examples/system-verilog/formatted_input/values.sv)
exercise partial matches, selector dependencies, overlapping count/output
targets, input aliasing, NUL bytes, formats, widths and suppression.
The [proof](../Examples/system-verilog/formatted_input/proof.lean) binds its
proved statement to the extracted fixture and checks the complete
independently observed transcripts.
