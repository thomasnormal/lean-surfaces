# Runtime integral `$clog2`

These sources exercise IEEE 1800-2023 §20.8.1 through the shared numeric
helper and existing value, assignment and process rules.

| Source | Complete independent output | Purpose |
|---|---|---|
| `boundaries.sv` | `0:0 1:0 2:1 3:2 4:2 5:3 6:3 7:3 8:3 9:4 10:4 11:4 12:4 13:4 14:4 15:4 16:4 17:5 `, `neighbors 8 8 9` | Zero, one, small powers and neighbors; loop reads |
| `widths.sv` | `unsigned 8 32 127`, `contexts 128 0 128 32` | Unsigned treatment of signed values, 128-bit arguments, result conversions |
| `runtime.sv` | `before 4`, `after 4 8` | Current reads, delay and captured NBA |
| `composition.sv` | `composed 0803 0808 30`, `selected` | Nested calls, patterns, replication, cases and fixed cells |
| `unknown.sv` | `unknown 8` | Deliberate runtime-X refusal |
| `constant_unknown.sv` | `constant 8 0` | Deliberate X/Z refusal retained through enclosing folding |
| `elaboration_unknown.sv` | `elaboration 8` | Deliberate unknown elaboration-constant refusal |
| `effects.sv` | `effects 3 9` | Deliberate increment-operand refusal |

Final independent observations dated 2026-10-20 use `["-ii_val"]`. The four
runnable sources match complete output under both schedule oracles. Three
also match the time-zero runner; `runtime` observes the captured NBA at tick
one. No output is projected or filtered; the first boundary line retains its
trailing space after `17:5`. The four further sources are deliberate model
refusals. Their successful reference runs establish no model agreement.

`proof.lean` carries the exact source hashes and receipt keys beside every
expectation group. Five kernel proofs certify `runtime.sv`'s actual parsed
RHS and blocking/NBA assignments, with general current values and prior state.
The fixture receipt checks source membership, complete output and refusal
boundaries. See [the contract](../../../docs/sv-runtime-clog2.md).
