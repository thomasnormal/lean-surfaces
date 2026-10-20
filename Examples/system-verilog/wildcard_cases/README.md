# Symmetric wildcard cases

`table.sv` executes both matching modes on every pair of two-bit four-state
values. Each of its sixteen output rows records the sixteen matching item
positions for one subject. Items and subjects are runtime array reads.

`contexts.sv` checks whole-case signed and mixed-width conversion, exact X
matching in `casez`, dynamic masks, a 65-bit subject, no match, grouped labels,
default placement, first match and nesting. `timers.sv` changes the subject
while each selected arm is waiting. The selected arm finishes unchanged
under both source and reverse schedule oracles.

`proof.lean` records the complete independent transcripts and source hashes,
proves the evaluator bridge and symmetric matching, and proves that a selected
delay retains its own continuation. A compiled-statement certificate binds
the delayed-arm theorem to `timers.sv`.

Regenerate with `python3 extractors/sv/extract.py` followed by the three source
paths. Run the receipt from the repository root:

```sh
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 \
  Examples/system-verilog/wildcard_cases/proof.lean
```

See [the contract](../../../docs/sv-wildcard-cases.md) for scope and boundaries.
