# Integral replication

These sources exercise IEEE 1800-2023 §11.4.12.1 and the wide unsized
based-literal rule of §5.7.1 through the existing concatenation and process rules.

| Source | Complete independent output | Purpose |
|---|---|---|
| `groups.sv` | `groups 10xz10xz 101010101010 933a` | Complete groups, nested replication, X/Z and source order |
| `contexts.sv` | `contexts 0ff 9 00000000 1111 abab` | Self-determined widths, unsigned result and assignment context |
| `zero.sv` | `zero a5 3c3c` | Zero-count member identity and nested groups |
| `strings.sv` | `strings 414142 410a410a` | Byte-string literals and escaped newline bits |
| `runtime.sv` | `before xzxzxz`, `after xzxzxz 101010` | Live reads, delay and captured NBA |
| `composition.sv` | `composed a xzxz a a` | Patterns, cases and fixed-array cells |
| `effects.sv` | `effects 1 a` | Deliberate effectful-group refusal, including count zero |
| `dynamic_string.sv` | `dynamic abab` | Source-pure string history through replication |
| `based.sv` | `based xxxxxxxxxxxxxxxxxxxxxx zzzzzzzzzzzzzzzzzzzzzz xxxxxxxxxxxxxxxxxxxxx1`, `contexts 00000000000000xxxxxxxx xxxxxxxxxxxxxxxxxxxxxx 00000000000000xxxxxxxx 0000000000000000000000` | Unsized X/Z context fill versus sized literals and variables |
| `constant_based.sv` | `constant xxxxxxxxxxxxxxxxxxxxxx` | Deliberate frontend elaboration-constant refusal |

Final independent observations dated 2026-10-20 use `["-ii_val"]`. The seven
runnable sources match complete output under both schedule oracles, with no
projection or additional filtering. Six also match the time-zero runner;
`runtime` observes its captured NBA at tick one. The other three sources
remain deliberate model refusals and establish no execution agreement.

`proof.lean` records exact source hashes and independent receipt keys beside
each expectation group. Five kernel proofs certify the actual parsed
replicated RHS and blocking/NBA statements in `runtime.sv`, and the actual
zero-member assignment in `zero.sv`. The receipt checks those source
certificates, all complete transcripts and all refusal boundaries.
See [the contract](../../../docs/sv-replication.md) for admission details.
