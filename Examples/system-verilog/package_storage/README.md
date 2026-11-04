# Package integral singleton storage

These sources exercise IEEE 1800-2023 clause 26 through existing vector
storage and statement execution. Envelopes are generated from the sources.

| Source | Complete independent output | Purpose |
|---|---|---|
| `identity.sv` | `bound 4 4 20 boot 10`, `shadow 11 6`, `distinct 6 22` | Imports/reexports share original storage; locals and other packages retain distinct bindings |
| `defaults.sv` | `defaults xxxx 0000 1000 number 7`, `constants 4 2 1001` | Defaults, two-state squash, parameters, enums, aliases and unit imports |
| `packed.sv` | `packed 9 6`, `updated dc d d2` | Packed field and vector-slice stores affect the shared package slot |
| `timers.sv` | `before 5`, `after 8`, `later 13` | Delayed imported blocking and nonblocking writes, observed through qualified reads |
| `dependent.sv` | `dependent 5` | Deliberate runtime-dependent initialization refusal |
| `array.sv` | `array 7` | Deliberate unpacked package storage refusal |
| `subroutine.sv` | `function 9` | Deliberate package subroutine refusal |

All final sources have successful independent four-state observations dated
2026-10-20 with arguments `["-ii_val"]`. Exact source hashes and receipt keys
for executable expectations appear beside the checks in `proof.lean`.
The four runnable sources match complete transcripts under both schedule
oracles; three time-zero sources also match `runSelfCheck`. The other three
sources retain design-level refusals and are not counted as execution matches.
No output lines are projected or filtered. Decimal values print directly as
signed 32-bit integers; `%b` and `%h` preserve the declared source widths.
Timer observations occur at module ticks one, three and six.

`proof.lean` checks the complete transcripts and refusal boundaries, binds its
certificates to exact compiled source subtrees, and proves shared reads,
blocking stores, NBA capture and qualified reads after commit. See
[the contract](../../../docs/sv-package-storage.md) for the admitted fragment.
