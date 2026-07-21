# SystemVerilog lane — quickstart (M0)

Status: the M0 vertical slice ("scheduler core") plus a first typed spec
surface are in the tree and green, but **deliberately not integrated**:
nothing under `LeanModels/Sv/` is imported from `LeanModels.lean`, so plain
`lake build` does not build (or know about) the SV lane. That is the M0 contract
([sv-design-m0.md](../sv-design-m0.md)) — integration is a later, explicit
step, and further SV work is in progress in this repo. Everything below was
run against the current tree; where a piece is not built yet it is marked
*in progress*.

## What exists

- **Extractor**: `extractors/sv/extract.py` (`python3.12` + pyslang 11.0.0 —
  *not* the Python-lane `python3`). Envelope contract:
  [sv-envelope-schema.md](../sv-envelope-schema.md) (schema `sv-0.1`,
  elaborated widths, `Unsupported` nodes, deterministic output).
- **Examples**: `Examples/sv/{adder,counter,race_blk,swap_nba,toggle,xsel}.sv`
  with checked-in `.sv.json` envelopes.
- **Semantics + proofs**: the M0 stack `LeanModels/Sv/{Basic,Ast,Json,
  Semantics,Obs,Proofs,Tests}.lean` — 4-state values (`0/1/x/z`),
  cycle-level scheduler semantics with an explicit **schedule oracle** σ,
  and the four M0 theorems in `Proofs.lean` (`run_deterministic`,
  `swap_nba_spec` for *all* schedules, `race_blk_racy` exhibiting two
  schedules with different traces, `counter_from_reset`). This is the oracle
  principle paying off: scheduler nondeterminism is a quantified argument,
  and `race_blk`'s race is a theorem, not a flake.
- **Typed spec surface (M0 cycle-level slice)**: `LeanModels/Sv/Surface.lean`
  (the judgments `d ⊨ P`, `d / stim ⇓[σ] tr`, `d ⊑@clk[from rst] model`, and
  the `sv_prove` tactic), `Delab.lean` (goals and `#check` output print back
  in surface notation, plus surface forms of the M0 theorems),
  `ToggleExample.lean` (new-design walkthrough: `Examples/sv/toggle.sv`
  proved against its golden model), and `SelfCheck.lean` (the self-check
  tier for the conformance corpus). What exactly is implemented vs gallery
  target is recorded in the "Implementation status" note of
  [sv-spec-surface.md](../sv-spec-surface.md). SV work continues
  concurrently in this repo — before relying on a file, check it the same
  `lake env lean` way as below.
- **Differential harness vs Xcelium**: `harness/sv/{diff_test.py,cases.json,
  gen_tb.py,runner.lean}`.
- **Corpus census**: axis-1/2 coverage measured on the IEEE 1800-2023
  conformance corpus — results and reproduce commands in
  [sv-corpus-coverage.md](../sv-corpus-coverage.md)
  (`extractors/sv/census.py`, output under `harness/sv/conformance/`).
- **Design/target docs**: [sv-design-m0.md](../sv-design-m0.md) (normative
  M0 contract, verified 4-state operator semantics),
  [sv-spec-surface.md](../sv-spec-surface.md) (the SV gallery — design
  target; its "Implementation status" note records the slice that is now
  real).

## Extract an SV example

From the repo root:

```
python3.12 extractors/sv/extract.py Examples/sv/adder.sv
```

writes `Examples/sv/adder.sv.json` next to the source — byte-identical to
the checked-in envelope (deterministic output; verified by re-running on the
tree). The extractor never fails on valid SV: out-of-tier constructs become
`{"kind": "Unsupported", "sv_kind": <slang class>, "text": …}` nodes.

## Typecheck the semantics and the M0 theorems

The SV lane is invisible to `lake build`; check files directly (from the
repo root — each verified green on the current tree):

```
lake env lean LeanModels/Sv/Proofs.lean
lake env lean LeanModels/Sv/Tests.lean
lake env lean LeanModels/Sv/ToggleExample.lean
```

`Proofs.lean` imports `Obs.lean` → `Semantics.lean` → `Ast.lean` →
`Basic.lean`, so the first command transitively checks the scheduler stack;
`Tests.lean` additionally pulls in `Json.lean` and the typed surface
`Surface.lean`; `ToggleExample.lean` pulls in `Delab.lean` (and through it
`Surface.lean` + `Proofs.lean`). `SelfCheck.lean` checks the same way.

## Run the differential harness vs Xcelium

Requires `xrun` (Xcelium) on `PATH` and `python3.12`+pyslang; the script
(re)builds the `LeanModels.Sv` oleans it needs into `.lake/` by itself and
never runs plain `lake build`:

```
python3 harness/sv/diff_test.py
```

Verified output on the current tree (Xcelium 24.03):

```
CASE                   EXAMPLE     CYCLES  SIGMA              RESULT
------------------------------------------------------------------------
adder_directed         adder            5  sigma_src          PASS
adder_x                adder            5  sigma_src          PASS
counter_reset          counter          8  sigma_src          PASS
counter_xrst           counter          4  sigma_src          PASS
race_blk_one_edge      race_blk         1  sigma_rev          PASS (matched sigma_rev)
swap_nba_swap          swap_nba         4  sigma_src          PASS
xsel_directed          xsel             4  sigma_src          PASS
xsel_x                 xsel             4  sigma_src          PASS
```

Note the `race_blk` row: the Xcelium trace is required to match the Lean
trace for *some* accepted schedule, and the table reports which — here the
reverse order, which is the point of the example. Flags: `--case NAME` (one
case), `--workdir DIR`, `--keep`.

## In progress — do not expect these yet

- **Integration**: no import from `LeanModels.lean`, no
  `leanmodels-sv-run` lake exe, no `Res`/`Span` unification into `Core/`
  (the integration checklist itself is still to be written).
- **`// lean[` blocks**: `lean_blocks` is reserved in the envelope but not
  scanned; there are no SV companion files.
- **Spec surface beyond the M0 slice**: `Surface.lean` implements the
  cycle-level M0 rendering of the judgment family; the rest of the
  [sv-spec-surface.md](../sv-spec-surface.md) gallery (SVA, classes,
  interfaces, …) is a design target — its "Implementation status" note is
  the boundary.
- **Known seam**: `LeanModels/Sv/Json.lean`'s vocabulary predates
  [sv-envelope-schema.md](../sv-envelope-schema.md) and does not match the
  real extractor output; `harness/sv/runner.lean` carries its own envelope
  adapter and documents the mismatch in its header (porting the adapter into
  `Json.lean` is an integration item).
- The event/delay scheduler tier (`initial`, `#`, full stratified regions)
  is beyond M0's cycle-level semantics.

## What can go wrong

**Wrong Python.** The Python lane uses `python3` (3.9); the SV extractor
needs `python3.12` (pyslang). With plain `python3`:

```
    import pyslang
ModuleNotFoundError: No module named 'pyslang'
```

**Wrong runner.** `lake exe leanmodels-run` is the *Python*-lane runner; on
an SV envelope it fails at parse:

```
leanmodels-run: 'Examples/sv/adder.sv.json' is not a valid envelope: envelope: field 'module': property not found: module
```

There is no SV lake exe in M0 — the harness drives
`harness/sv/runner.lean` via `lake env lean --run` internally.

**`no case named 'nope'`.** `--case` takes a case *name* from
`harness/sv/cases.json` (e.g. `adder_directed`), not an example name.

**No `xrun`.** The harness needs Xcelium as ground truth; without it the
Xcelium side fails at testbench compile time. There is no
"Lean-only" mode — differential testing against the real simulator is the
methodology, not an optional check.
