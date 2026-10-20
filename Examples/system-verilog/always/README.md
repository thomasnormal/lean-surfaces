# Plain always source repetition

The fixtures exercise IEEE 1800-2023 §9.2.2.1 through the existing retained
loop continuation and scheduler:

| Source | Independent complete output | Purpose |
|---|---|---|
| `tails.sv` | `retained 4 3 z01x` | Time-zero prefix, retained tail and live four-state payload |
| `independent.sv` | `independent 3 2` | Independent two- and three-tick periods |
| `automatic.sv` | `automatic 3 9` | Always-only design; fresh automatic cells on each entry |
| `events.sv` | `waiting 0 0` | Bare and negative-edge waits with no occurrence |
| `internal_edges.sv` | `edges 2 1` | Deliberately refused until procedural writes publish edges |

Independent observations were completed on 2026-10-20 in value-preserving
mode. `proof.lean` checks the four runnable transcripts under both schedule
oracles, the fifth refusal, the initial-only runner boundary and the exact
compiled bodies used in its four kernel theorems.

Each decimal field is the source signed 32-bit `int`, printed with `%0d`;
the `tails` payload is the four-bit `%b` value with X/Z retained. Observations
occur at module ticks seven (`tails` and `independent`), six (`automatic`),
two (`events`), and three (`internal_edges`). The transcript comparison uses
each complete line directly, with no time rescaling or output filtering.

See [the contract](../../../docs/sv-always.md) for the admitted surface and
remaining boundaries. Regenerate envelopes with `extractors/sv/extract.py`;
they are generated artifacts.
