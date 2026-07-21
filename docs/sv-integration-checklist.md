# SV lane — integration checklist (post-M0)

Everything the M0 workflows deliberately did NOT do, per the concurrency
rules in `docs/sv-design-m0.md` (the SV lane must stay invisible to plain
`lake build` until the Python workflow lands). Items 1–4 are the contract's
definition-of-done item 5; the rest are deferrals recorded by the individual
M0 phases.

## 1. Imports into `LeanModels.lean`

Add (in dependency order — each file already typechecks standalone via
`lake env lean`):

```
import LeanModels.Sv.Basic
import LeanModels.Sv.Ast
import LeanModels.Sv.Json
import LeanModels.Sv.Semantics
import LeanModels.Sv.Obs
import LeanModels.Sv.Surface
import LeanModels.Sv.Proofs
import LeanModels.Sv.Delab
import LeanModels.Sv.Tests
```

Layout constraint (load-bearing, do not "fix"): `Surface.lean` imports only
`Obs.lean`, never `Proofs.lean` — `Tests.lean` imports the surface for
`#sv_check`, and `Proofs.lean`'s public example names (e.g. `raceStim`)
collide with `Tests.lean`'s pre-existing private copies. The surface
restatements of the M0 theorems therefore live in `Delab.lean` (imports
both). `SelfCheck.lean` / `ToggleExample.lean` (corpus workflow) have their
own import story — coordinate with that lane before wiring them in.

## 2. Lakefile exe

A real `leanmodels-sv-run` executable (mirroring the Python lane's runner):
entry point wrapping the harness runner logic
(`harness/sv/runner.lean`, invoked in M0 via `lake env lean --run`), i.e.
envelope path + cases args → canonical `CYCLE k name=%b …` lines under
`σ_src`. Until then the harness keeps using `--run`.

## 3. `Res`/`Span` unification into `Core/`

`Sv.Res` (`ok/timeout/unsupported`, `LeanModels/Sv/Basic.lean`) is a local
mirror of the Python lane's `Res` minus exceptions. Unify into
`LeanModels/Core/` with the Python `Res` (exception constructor unused by
SV), port `Res.ok_bind`-style simp lemmas once, and re-point both lanes.
Same for any `Span`/provenance type when SV starts carrying source spans.

## 4. Companion / `// lean[` scanning

The envelope reserves `lean_blocks: []` (`sv-0.1`, never scanned in M0).
Post-integration: extractor scans `// lean[ … // ]` comment blocks, splices
them into generated companions, `@[spec]` attribution — the Python lane's
companion pipeline generalized.

## 5. Gallery theorems still unproven at M0

From `docs/sv-spec-surface.md` (examples 1–19); the M0 surface proves the
example 2/3 shapes only. Still design-target:

- **`Sv.comb` judgment + example 1/5 theorems** (`adder_spec`,
  `xsel_known`, `xsel_xoptimism`): needs a "after combinational settle"
  packaging (Active-region convergence as an acyclicity obligation).
  M0 covers these designs only via `#sv_check` columns in `Tests.lean`.
  Design note: statable today as a 1-cycle `⊨ spec` over a single stimulus
  entry; a dedicated `Sv.comb` should quantify over held inputs instead.
- **Typed port wrappers**: gallery writes `ins.a`/`outs.s` structures
  generated from elaboration info; M0 speaks `SvState.lookup s "a"`.
  Generator belongs with the companion pipeline (item 4).
- **`⊨sva` / `m.props.<label>`**: SVA extraction; needs Preponed sampling,
  hence at least the region-accurate scheduler tier.
- **`Sv.FinishesBy`, event-driven time (example 4)**: `initial`/`#`/
  `$finish` are Unsupported in M0's cycle-level core.
- **Function arrow `f(a,b) ==> v`**: SV `function`s are outside the M0 tier.
- **`sv_witness`** (schedule-counterexample exhibitor tactic): M0 proves
  `race_blk_race` from the raw witnesses instead; a tactic that searches
  {σ_src, σ_rev, …} and `decide`s the trace inequality is the design.
- Examples 6–19 wholesale (nets/resolution, latches, structs, interfaces,
  classes, randomization, DPI, generate, liveness).

## 6. Surface-layer deferrals (recorded by the surface phase)

The M0 surface (`Surface.lean` + `Delab.lean`) shipped `⊨`
(`Models`/`spec`/`onPosedge`), `⇓[σ]` (`Runs` notation),
`Sv.Deterministic` readings, `⊑@clk[from rst]` (`RefinesFromReset`),
first-cut `sv_prove`, `#sv_check`, and goal-state unexpanders. Known gaps:

- **`sv_prove` does no symbolic execution**: new designs still need the
  Proofs.lean script (threshold intro + `sv_simp` + `choose_*` lemmas)
  to get their canonical-trace lemmas; `sv_prove` only bridges raw → surface.
- **`RefinesFromReset` is single-output, Bool-reset, width-fixed**: M0
  observes `Design.firstOutput` only; multi-output refinement and non-`rfl`
  reset states (`RefinesFromReset.of_reset_column` with a proved `hreset`)
  are statable but have no notation/tactic arm.
- **`#sv_check` checks completed `.ok` columns only**: no surface form for
  "this run times out / hits Unsupported" (raw `#guard … matches` still
  needed for those).
- **Delab boundary**: below the judgments, goals show `Runs`/fuel/
  `initState` by design; `⊑@` only pretty-prints the `firstOutput` form.

## 7. Final gate

After the Python workflow lands and imports are added: one plain
`lake build` from repo root must be green (the M0 phases each verified
their files only via `lake env lean`).

## Deferred by down-scope (2026-07-21)

- **Fresh-user acceptance test** (T-flip-flop `toggle.sv` proved from docs
  alone, with pure-Lean line-count comparison — the Python lane's
  `sum_to` pattern): run once the surface grows past the essentials tier.
- **Conformance adapter + oracle** (`initial`/`$display` self-check tier over
  the sv-tests-2 corpus): deferred because the census
  (`docs/sv-corpus-coverage.md`) shows only 11 files unlockable at that tier;
  revisit when the construct-frequency queue's top blockers are implemented.
  Resume handle: workflow script `sv-conformance-census-wf_c3bab9df-371.js`.
