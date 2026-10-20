# Case-inside membership selection

IEEE 1800-2023 §12.5.4, through the existing pure membership predicates and
first-match case chain:

- `table.sv`: every pair of two-bit four-state subjects/items, recording only
  definite matches. Unknown left operands are not wildcards.
- `contexts.sv`: signed/mixed/65-bit types, dynamic items and ranges, ambiguity,
  reversed ranges, common-width arrays/slices, default, nesting and first match.
- `timers.sv`: a selected wildcard/range body retains its continuation while
  subjects/endpoints change; a later case reads the new values.
- `array_widening.sv`: a deliberate refusal preserving the unresolved
  difference between signed case-array widening and scalar membership.

Complete outputs were independently observed on 2026-10-20. The first three
match both source and reverse schedule oracles; the time-zero fixtures also
match `runSelfCheck`. Source hashes are recorded in their envelopes and
`proof.lean`. The proof receipt binds exact compiled wildcard and interval
subtrees, checks the complete accepted transcripts and preserves loudness on
the array-widening source. It does not count that source as runtime agreement.

```sh
python3 extractors/sv/extract.py Examples/system-verilog/case_inside/*.sv
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 Examples/system-verilog/case_inside/proof.lean
```

No evaluator or scheduler changed. Effects, qualifiers, unsupported storage,
tolerance syntax, dollar case endpoints and case-array widening remain loud.
Ordinary `inside` expressions and the existing symbolic structural case path
retain their separate admission contracts.
