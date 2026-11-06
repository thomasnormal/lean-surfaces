# R2 core scouting

This is the R2 admission census for three real RISC-V cores.  The source trees
were cloned at the pins below and were not modified.  The extractor and
`load_design_sv2` were run from this repository with Lean 4.33.0-rc1.  The
envelopes were kept outside the repository; their SHA-256 values make the
measurements reproducible without vendoring third-party RTL.

## Pins and licenses

| core | upstream pin | license | top | source files in envelope |
| --- | --- | --- | --- | ---: |
| CV32E40P | [`openhwgroup/cv32e40p`](https://github.com/openhwgroup/cv32e40p), tag `v1.0.1`, `6148cf567f2450052458c21c5b3cc2a02423c69d` | Solderpad Hardware License 0.51 (`LICENSE`) | `riscv_core` | 31 |
| Ibex | [`lowRISC/ibex`](https://github.com/lowRISC/ibex), `master`, `d513671dae09e701ceb6cd732d2da5fb52c13856` | Apache-2.0 (`LICENSE`) | `ibex_top` | 224 |
| PicoRV32 | [`YosysHQ/picorv32`](https://github.com/YosysHQ/picorv32), `main`, `ef203c2b0a3fb793280f5114941416c425c5b461` | ISC (`COPYING`) | `picorv32` | 1 |

The CV32E40P input is every `rtl/*.sv`.  The Ibex input is `rtl/*.sv` plus
the primitive and common-cell SystemVerilog dependency directories selected
by `ibex_top.core` (the broad set keeps unresolved primitive dependencies
visible).  PicoRV32 uses the single `picorv32.v` source from its default
FuseSoC target.  No RTL adaptation was made.

## Commands and measurements

For each clone, the command was the symbolic extractor invocation below, with
the listed source set passed as the final arguments:

```text
python3 extractors/sv/extract.py --top TOP -o RESULT.sv.json SOURCE...
```

The loader probe was a small Lean file containing:

```lean
import LeanModels.Sv.Ingest2
load_design_sv2 NAME from "RESULT.sv.json"
#check NAME
```

| core | extraction wall | envelope bytes / SHA-256 | hierarchy modules | static `Unsupported` nodes | loader result |
| --- | ---: | --- | ---: | ---: | --- |
| CV32E40P | 17.08 s | 21,289,394 / `e588884691159820eac0a28eff5315e721b99fdf989f6611540931e5f264a6de` | 23 | 293 | **refused** |
| Ibex | 39.13 s | 13,914,127 / `ae014736a66a58b0f725d0bf358ee8ebab6fb05ef75e0645ea1507137ce2f7d4` | 20 | 396 | **refused** |
| PicoRV32 | 4.37 s | 3,178,052 / `009cc39591b3fcb1c88403ca44f822cb1854d2ebc0b5c728c7cade06a2e47b1b` | 1 | 70 | **loaded** |

The loader diagnostics below are the complete first errors, copied from the
Lean probes:

```text
CV32E40P:
envelope: module: AlwaysPosedge: AlwaysPosedge:edge — edge-qualified clock requires its retained event semantics

Ibex:
envelope: module: AlwaysLatch: unknown process kind "AlwaysLatch"
```

PicoRV32 loads as a 26-`Nat` parameter family.  Loading is not a claim that
the semantic tier is admitted: at the default values,

```text
(picorv32.sem defaults).hasUnsupported = true
processes.size = 1
[(Instantiate, decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory))]
```

Thus its first semantic wall is the register-file unpacked memory, while the
envelope loader itself succeeds.  Its most frequent static walls are
unsized/XZ parametric literals (16), call expressions (13), width
conversions (11), net-z (8), and assignment targets (6); these counts are
telemetry, not silently admitted semantics.

The first admission pass recorded a 2.21-second, 3,181,105-byte envelope with SHA-256
`25ac7e444bd6f4171348484fcba4d99e9c5192036764dabb8b64a6ef8c77be26` before the
extractor was re-run for the current re-probe.  The canonical measurement for
the pinned source is now the reproducible 3,178,052-byte envelope above
(`009cc395…`); the source commit and all loader diagnostics are unchanged.
Later R2 decisions use the canonical envelope, rather than mixing the two
extractor snapshots.

## Ranking and next requests

Measured distance to an R2 proof target is:

1. **PicoRV32** — closest: one-module load succeeds and the remaining first
   semantic wall is a concrete unpacked memory shape (`cpuregs`).
2. **CV32E40P** — next: 23 modules extract, but the loader stops at retained
   edge-process semantics (`AlwaysPosedge`).
3. **Ibex** — last for this tier: the broad dependency closure extracts 20
   modules, but `AlwaysLatch` is encountered before a design family can load;
   primitive/dependency unsupported nodes add further work after that wall.

The result is a scouting decision, not a core selection for the proof rung:
PicoRV32 is the first candidate to revisit after the generic memory route and
the edge/latch process semantics land in the SV tier.  No core was rewritten
to fit the loader.

