# Integral assignment patterns

These sources exercise IEEE 1800-2023 §10.9 through the existing vector,
concatenation, storage and process rules.

| Source | Complete independent output | Purpose |
|---|---|---|
| `keys.sv` | `keys 80808100 0xx1 1zz0` | Integer bit keys and both packed range directions |
| `structs.sv` | `structs 39a5 12345 -2 1001` | Member/type/default priority, nested and signed structs, two-state conversion |
| `arrays.sv` | `arrays 30 20 10 7 8 9 34 12`, `updated 60 50 40 78 56` | Both unpacked directions and fixed cells of packed structs |
| `replicated.sv` | `repeated 10101010 xz01xz01` | Complete replicated element groups and four-state bits |
| `runtime.sv` | `live 1xz1 9 2`, `captured 1xz1 0` | Current reads, whole-struct self-swap and NBA capture |
| `effects.sv` | `effects 1111 4` | Deliberate effectful-operand refusal |
| `multidim.sv` | `multidim a5` | Deliberate existing multidimensional-storage refusal |
| `self_alias.sv` | `self 7 3` | Whole-RHS snapshot for a split-cell unpacked self-read |

Final independent observations dated 2026-10-20 use `["-ii_val"]`. All five
runnable sources agree completely under both schedule oracles; all except
`runtime` also agree with the time-zero runner. The three further sources
are deliberate model refusals and establish no execution agreement.
There is no output projection or additional filtering. Binary/hex values keep
declared widths; signed decimal printing uses the ordinary integral rule.
Observations occur at tick zero, plus tick one in `runtime`.

`proof.lean` carries exact source hashes/receipt keys beside every executable
expectation group. Four kernel proofs certify the keyed pattern RHS and its
actual blocking/NBA statements in `runtime.sv`; the fixture receipt checks
parsed source membership, complete output and the remaining refusal boundaries.
Envelopes are generated from the sources. See
[the contract](../../../docs/sv-assignment-patterns.md) for admission details.
