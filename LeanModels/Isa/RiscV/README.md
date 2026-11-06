# Sail RISC-V Lean backend scouting (R0)

This directory records the R0 decision.  The generated Sail package is kept
outside this repository while its upstream packaging defects and interface
contract are resolved; no generated source is copied into the LeanModels
tree.

## Decision

Do not vendor the official Sail Lean output or add it as a Lake dependency in
this revision.  Sail generates a substantial RV32I-configured package, but the
package does not build as emitted and its handwritten support file contributes
75 `axiom` declarations.  Both facts violate this repository's build and
no-new-axioms rules.  `LeanModels/Isa/RiscV/Oracle.lean` now records all 75
support signatures as explicit parameters, without pretending to provide
their implementations.  The current usable seed is the axiom-free
handwritten model in [`LeanModels/Rv`](../../Rv), with the Sail C emulator
used only as a differential oracle.  A future official integration still
needs an upstream namespace fix and a generated semantics that consumes the
explicit oracle (or a manually curated axiom-free RV32I model with Sail C
retained as validation only).

## Pins and profile

The source pins used for this measurement are:

| Component | Pin / provenance |
|---|---|
| `riscv/sail-riscv` | tag `0.13.1`, commit `27224ccb2290f022e46213c05b3e72e8a9ea635e` |
| Sail compiler | `Sail 0.20.2` (`sail2 @ 3b7af38d66466ecadad563158b07ce2f82fe05da`) |
| `lean-sail` Lake dependency | input tag `v4`, resolved commit `79b4d08505af29d88b3918f32d29840fae1fa191` |
| RISC-V licence | BSD-2-Clause, upstream file `LICENCE` |

The custom configuration was `/var/tmp/thomas-ahle/fleet2/work/rv32i.json`:
`xlen = 32`, with only top-level `Zicsr` and `Zifencei` enabled; M, A, F, D,
C, S, U, and all other extension families (including V) were disabled.  The
generator was nevertheless invoked with `--all-modules`, so disabled extension
syntax remains in the generated `instruction` universe.  This is a generator
coverage observation, not a claim that those extensions are enabled by the
profile.

## Commands and measurements

The CMake command below ran from the pinned upstream checkout
`/var/tmp/thomas-ahle/fleet2/work/ls-sv2-sail-riscv`, using the pinned Sail
binary and the configuration above; it used downloaded GMP.  Sail commands
ran from that checkout's `model` subdirectory, where `riscv.sail_project`
lives.

```text
cmake -S . -B /var/tmp/thomas-ahle/fleet2/work/ls-sv2-sail-riscv-build \
  -DCMAKE_BUILD_TYPE=Release \
  -DSAIL_BIN=/var/tmp/thomas-ahle/fleet2/work/sail-0.20.2/bin/sail/bin/sail \
  -DSAIL_MODULES=--all-modules -DDOWNLOAD_GMP=ON

/var/tmp/thomas-ahle/fleet2/work/sail-0.20.2/bin/sail/bin/sail \
  --just-check --config /var/tmp/thomas-ahle/fleet2/work/rv32i.json \
  --all-modules riscv.sail_project
```

The first command succeeded in **8.559 s** (MEASURED).  Sail's just-check
succeeded with no diagnostics in **14.977 s** (MEASURED).  The Lean generation
was the `generated_lean` CMake rule expanded for `rv32i`; from `model`, its
relevant command shape was:

```text
/var/tmp/thomas-ahle/fleet2/work/sail-0.20.2/bin/sail/bin/sail \
  --config /var/tmp/thomas-ahle/fleet2/work/rv32i.json \
  --lean --memo-z3 --lean-output-dir \
  /var/tmp/thomas-ahle/fleet2/work/r0-generated-rv32i-all \
  --lean-force-output \
  --lean-non-beq-type instruction \
  --lean-non-beq-type ExecutionResult --lean-non-beq-type Step \
  --lean-noncomputable \
  --lean-noncomputable-function encdec_forwards \
  --lean-noncomputable-function encdec_backwards \
  --lean-noncomputable-function encdec_forwards_matches \
  --lean-noncomputable-function encdec_backwards_matches \
  --lean-noncomputable-function encdec_compressed_forwards \
  --lean-noncomputable-function encdec_compressed_backwards \
  --lean-noncomputable-function encdec_compressed_forwards_matches \
  --lean-noncomputable-function encdec_compressed_backwards_matches \
  --lean-import-file ../handwritten_support/RiscvExtras.lean \
  -o Lean_RV32I --all-modules riscv.sail_project
```

Generation succeeded in **823.955 s** (MEASURED), producing
`/var/tmp/thomas-ahle/fleet2/work/r0-generated-rv32i-all/Lean_RV32I`:

* 165 `.lean` files;
* 48,150,827 bytes (45.92 MiB) of Lean source;
* `InstsEnd.lean`: 45,745,681 bytes;
* `Defs.lean`: 68,045 bytes.

The generated `instruction` declaration has 353 syntactic constructors when
counted from `Defs.lean` (MEASURED).  From the Sail source instruction-family
inventory, the requested profile covers the 40 RV32I base mnemonics, six
Zicsr forms, and one Zifencei form (DERIVED).  The generated declaration also
contains privileged and disabled-extension families because of
`--all-modules`; this is why the constructor count is not an RV32I coverage
count.

## Build and stability result

The generated package was then tested as emitted:

```text
cd /var/tmp/thomas-ahle/fleet2/work/r0-generated-rv32i-all/Lean_RV32I
lake update
lake build
```

`lake update` selected Lean `leanprover/lean4:v4.29.0` and the pinned
`lean-sail` revision above.  The repository then used Lean 4.33.0-rc1.  `Defs`
compiled, then the build failed in `LeanRV32I/RiscvExtras.lean` after
**196.969 s** (MEASURED):

```text
LeanRV32I/RiscvExtras.lean:14:5: unknown namespace `LeanRV32I.Defs`
```

The support file contains `open LeanRV32I.Defs`, while `Defs.lean` emits its
declarations at the root and does not create that namespace.  The same
namespace failure reproduced with smaller generated packages (MEASURED), so
hand-editing this output would conceal an upstream/backend packaging defect.

There is a second independent admission blocker: `RiscvExtras.lean` contains
75 `axiom` declarations (8 platform/reservation/randomness hooks and 67
floating-point/rounding hooks, MEASURED).  The repository-side parameter
contract for those signatures is `SailOracle M PA` in
`LeanModels/Isa/RiscV/Oracle.lean`; the generated package has not yet been
rewired to consume it.  Even if the namespace error were fixed, the emitted
package would not be admissible as-is.

## Differential validation boundary

The generated package could not reach a Lean executable, so no differential
claim is made for it and no `riscv-tests` run is recorded for it.  The existing
fallback model has a separate measured validation: `docs/rv-model.md` records
257/257 generated RV32IMC + M-mode cases matching the pinned Sail 0.13.1 C
emulator, including traps, CSRs, interrupts, compressed instructions, and
memory effects.  The harness's `--coverage-only` mode additionally checks the
fallback model's full 57-row decoder universe without pretending that this is
an oracle comparison.  That result validates the fallback model only; it is
not a substitute for a successful build of the official generated package.

## Packaging recommendation (JUDGED)

1. Keep the generated tree and its build logs outside the repository until
   Sail/`lean-sail` emits a consistent namespace and the support interfaces
   carry explicit oracles instead of axioms.
2. Do not add a Lake dependency pinned to Lean 4.29 while this repository is
   on Lean v4.35.0; revisit after an upstream compatibility pin exists.
3. Use `LeanModels/Rv` as the R0 seed for the next rung, retaining the Sail C
   emulator as a validation oracle.  If the official backend remains blocked,
   grow an axiom-free RV32I model under this tree and record every semantic
   cross-check against Sail; the differential harness now requires all 57
   decoder rows to be covered by passing cases.

