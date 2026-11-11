# Plain `always @*` runtime memory read retained for E

This clean-room fixture exercises IEEE 1800-2023 §§9.4.2.2.2 and 7.4: a
plain `always @*` reads a runtime-selected cell of a parameter-sized unpacked
array after an `always_ff` write.  The extractor keeps the parser's
`AlwaysEvent`/`ImplicitEventControl` and source-shaped `ArraySel`; it does not
flatten the parameterized memory or turn the read into a finite scalar choice.

The current one-cycle E memory profile refuses retained implicit-event
processes explicitly because its scheduler does not yet model the wait and
re-arm.  `agree.lean` pins that boundary, preventing the process from being
silently skipped.  The simulator rows cover the initial unknown cell, two
runtime writes and reads, an untouched cell, and x/z/out-of-range read
indices.

Run the focused receipt and differential comparison with:

```text
lake env lean Examples/system-verilog/sem2/always_star_memory_read_e/agree.lean
python3 Examples/system-verilog/sem2/always_star_memory_read_e/check.py
```
