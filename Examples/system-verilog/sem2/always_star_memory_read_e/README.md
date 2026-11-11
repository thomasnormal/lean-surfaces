# Plain `always @*` runtime memory read in E

This clean-room fixture exercises IEEE 1800-2023 §§9.4.2.2.2 and 7.4: a
plain `always @*` reads a runtime-selected cell of a parameter-sized unpacked
array after an `always_ff` write.  The extractor keeps the parser's
`AlwaysEvent`/`ImplicitEventControl` and source-shaped `ArraySel`; it does not
flatten the parameterized memory or turn the read into a finite scalar choice.

The source-shaped E memory profile now admits the acyclic slice used here:
blocking scalar or one-rank memory assignments inside `if`/blocks.  It keeps
the parser body and wakes it when either the selected memory cell or the index
expression changes.  The active pass runs each retained process at most once;
self-retriggering, procedural loops, `case`, and NBA statements remain loud
boundaries.  `agree.lean` checks the E trace rather than allowing a retained
process to be silently skipped.  The simulator rows cover the initial unknown
cell, two runtime writes and reads, an untouched cell, and x/z/out-of-range
read indices.

The E rows are an execution receipt for this admitted slice.  They do not
claim the full event scheduler or a whole-core trace.

Run the focused receipt and differential comparison with:

```text
lake env lean Examples/system-verilog/sem2/always_star_memory_read_e/agree.lean
python3 Examples/system-verilog/sem2/always_star_memory_read_e/check.py
```
