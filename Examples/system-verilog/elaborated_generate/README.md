# Elaborated generate scopes

These sources exercise IEEE 1800-2023 clauses 6, 23 and 27 through the
legacy elaborated frontend and existing vector/process semantics.

| Source | Complete independent output | Purpose |
|---|---|---|
| `scopes.sv` | `scopes 22 c 55 aa` | Selected if/case branches, unconditional nesting, zero-count loops and distinct same-named declarations |
| `loops.sv` | `up 3 13 23`, `down 6 7 8` | Ascending/descending genvars, blocking updates and captured NBAs |
| `locals.sv` | `locals 16 19` | Repeated procedural locals and arrays retain distinct values through delays |
| `captures.sv` | `pending 0 0`, `captured 30 31` | Repeated source offsets allocate distinct delayed-assignment captures |
| `imports.sv` | `cells 2 8 3 9` | Scoped package imports, aliases, genvar values and hierarchical fixed-array cells |
| `parameters.sv` | `parameters 10xz -3 c7 -3` | Exact four-state, signed and hierarchical parameter constants |
| `choices.sv` | `choices 1 2 3` | Definite-one and ambiguous truthiness, exact X/Z case selection |
| `member.sv` | `active member` | Deliberate active subroutine-member refusal |
| `hierarchy.sv` | `instance 5` | Deliberate cross-instance storage refusal |
| `dependent.sv` | `dependent 6` | Deliberate dependent static-initialization refusal |

Final independent observations dated 2026-10-20 use `["-ii_val"]`. All seven
runnable sources agree completely under both schedule oracles; `parameters`
and `choices` also agree with the time-zero runner. The three other sources
are deliberate model refusals and are not counted as execution matches.
There is no output projection or additional filtering. Decimal values print
directly as signed 32-bit integers; binary/hex values retain declared widths.
Observations occur at ticks zero, one or three as stated in each source.

`proof.lean` carries source hashes/receipt keys beside all executable
expectations, checks the complete transcripts and refusal boundaries, and
certifies exact parsed declarations/read/write subtrees used by three kernel
proofs. Envelopes are generated from the sources. See
[the contract](../../../docs/sv-elaborated-generate.md) for the admission rules.
