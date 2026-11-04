# Dynamic integral casts

IEEE 1800-2023 §6.24.2/§20.5. See [the contract](../../../docs/sv-dynamic-cast.md).

Six sources match complete independent transcripts under both region oracles.
Three successful-reference sources retain model effect-context refusals; the
invalid task source produces an independent runtime diagnostic and status one,
while the model refuses that diagnostic branch. None of these four refusals is
an execution agreement. No transcript filtering, projection or time rescaling
is used.

| Source | Complete independent stdout / boundary |
|---|---|
| `conditional.sv` | `conditional 1 110` |
| `control.sv` | `and-skip 0 01 / or-skip 1 01 / and-write 1 10 / fallback 01 / unknown-fail 0 01 / comparison 1 10` |
| `rules.sv` | `wide 1 01 / ones 0 01 / x 1 x1 / z 1 z0 / two 1 00 / two1 1 01 / sign 1 110 / unsigned 1 110 / u32 1 110 / u32n 1 110 / selfinvalid 0 11 / int 1 00000000` |
| `selected.sv` | `cell 1 1 8 / retain 0 1 8 / outside 1 1 8 / window 1 ab6d / member 1 3f` |
| `source_effect.sv` | `effect 1 001 1` |
| `task_failure.sv` | Runtime invalid-cast diagnostic; destination remains `001`; status 1 |
| `task_success.sv` | `task 110 f` |
| `timing.sv` | `capture 1 8 8 7 / failure 0 8 8` |
| `unordered.sv` | `unordered 7 110` |
| `certificate.sv` | `certificate 1 8` |

`rules` checks assignment conversion before membership, truncation, signed
extension, two-state conversion, sparse values, named X/Z members and invalid
same-type enums. `control` checks skipped calls, logical sequencing, failure
fallback, an unknown logical left operand and comparison context. `selected`
checks fixed cells, failure retention, an out-of-range cell, a packed window
and a packed member. `timing` checks source sampling, NBA capture and retention
across ticks two, three and five. `task_success` checks valid enum and integral
task calls. `certificate` binds the proof declarations to actual parsed code.

The six kernel theorems cover source conversion, acceptance of the two bound
members, failed-branch state/work/output preservation, successful copyback and
snapshot stability after a source change. Their declarations are checked against
the parsed capture and guarded success body. These are properties of that real
fixture, not a general frontend correctness theorem.

Every reference uses top `top`, version `24.03-s004`, date 2026-10-20, arguments
`["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"]`. Source bytes,
invocation key, status, complete transcript and available provenance were
authenticated; the status-one row binds the full retained diagnostic log.

| Source | SHA-256 | Receipt |
|---|---|---|
| `conditional.sv` | `89d9118dcca1c24febecb24e7c81f6936afcaf2213161d788fcae67790568bfa` | `0e7730bbab791e971ef72672` |
| `control.sv` | `22caebe43141a5e12e73de25f3866f8016dc7c5e942d8265047ccec06586a707` | `72538893c3532a3a40c98a5c` |
| `rules.sv` | `8f8c9d0efd54fde3155c299e0f4e3558c6d43a10746559b409336a83a1525e28` | `70711ef71e50f92b905b84c3` |
| `selected.sv` | `de26b062014cf5b52e4504925a081d39e395a6b16cd782fe69503f8ed940b02e` | `a63f4905d24fda41bc5a69bf` |
| `source_effect.sv` | `8104aca35b66cb89ce78f923baf3221c0233a3646108a72ff6dc1b595c4f50c2` | `f8d31e2830d3b79ac35fade6` |
| `task_failure.sv` | `a63600a4a35c4faf4cd6f7f8f70b2015357d20221629d8851a744a99d87b2f62` | `548b04125236309016eb2002` |
| `task_success.sv` | `99d5762c9fa25a8c44cac877815a8f91cfb8d580f97f0713c86c8cad5fef8cd4` | `563759e330aef53817a0fe18` |
| `timing.sv` | `5ad43f4ac4ec844e15185a6c66db652db1c094ae3ac24ecf3ebdd8218babeceb` | `ecedfe9e5fd0bbb1fec98568` |
| `unordered.sv` | `d81576dc0e8c4eb1faaa725bde1c5ac32e93c8dc39459a78d76771f0e2fa32c7` | `c3032fe3eacc1abe09b978a8` |
| `certificate.sv` | `cde576e1db69ee705208f4bb9e4b564d9ca3100f25ce0703b81de97d341c80c7` | `df57813163e4b8a357005397` |

Regenerate and check:

```sh
python3 extractors/sv/extract.py Examples/system-verilog/dynamic_cast/*.sv
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 Examples/system-verilog/dynamic_cast/proof.lean
```
