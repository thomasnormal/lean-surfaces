import LeanModels.Sv.Surface
import LeanModels.Sv.Proofs

/-!
# Delaborators + surface forms of the M0 theorems (`LeanModels.Sv`)

For an AI prover the goal state IS the interface (the Python lane's
`Delab.lean` lesson): a judgment that *elaborates* from
`counterDesign ⊑@clk[from rst] counterModel` but *displays* as
`RefinesFromReset counterDesign "clk" "rst" (Design.firstOutput
counterDesign) counterModel` leaks the encoding back into every proof. This
file closes the loop with `app_unexpander`s, so goals and `#check` output
print in the same surface notation the theorems are written in:

* `Models d P`                        → `d ⊨ P`
* `Runs d σ stim tr`                  → `d / stim ⇓[σ] tr`
* `RefinesFromReset d "c" "r" (Design.firstOutput d) m` → `d ⊑@c[from r] m`

`Deterministic d` already prints as itself (plain application — the gallery's
`Sv.Deterministic` shape) and needs no unexpander.

**This file also holds the surface restatements of the M0 theorems** —
`swap_nba_swaps`, `race_blk_race`, `counter_refines`, the `⇓[σ]`
non-vacuity forms, and `sv_prove`-closed determinism corollaries — because
`Surface.lean` deliberately does not import `Proofs.lean` (`Tests.lean` must
import the surface machinery, and `Proofs.lean`'s public example names —
e.g. `raceStim` — collide with `Tests.lean`'s pre-existing private copies).
The raw fuel/`run`-form theorems stay in `Proofs.lean`; everything here
derives from them (the Python corollary pattern), so the surface forms are
corollaries, never re-proofs. Theorem 1's surface form (`run_functional`)
lives in `Surface.lean` (it needs only Obs.lean).

What still leaks (by design — documented, not hidden):

* Below the judgment boundary nothing is sugared: after `intro`/`obtain`,
  goals show `Runs`, `∃ fuel, run … = .ok tr`, `initState`, snapshot lists —
  fuel and interpreter are *supposed* to be visible once you step below the
  surface.
* `d ⊨ P` with a bare lambda `P` prints the lambda (only `spec`/`onPosedge`
  keep it tidy — they print as themselves, which is surface notation).
* `RefinesFromReset` applied to an explicit `out` string (not
  `Design.firstOutput d`) prints raw: the `⊑@` notation always re-elaborates
  to the `firstOutput` form, so printing it for anything else would break
  the display/re-elaborate round-trip.
* `set_option pp.explicit true` bypasses all app unexpanders (standard).

Pinned renderings: the `#guard_msgs`-checked `#check`s at the bottom, plus
`rfl` round-trips (every rendering re-elaborates to the proposition it
displays) and `#print axioms` pins for the surface theorems.
-/

namespace LeanModels.Sv

open Lean PrettyPrinter

/-! ## Unexpanders (display-only) -/

/-- Display `Models d P` as `d ⊨ P`. -/
@[app_unexpander LeanModels.Sv.Models]
def unexpandModels : Unexpander
  | `($_ $d $P) => `($d ⊨ $P)
  | _ => throw ()

/-- Display `Runs d σ stim tr` as `d / stim ⇓[σ] tr`. -/
@[app_unexpander LeanModels.Sv.Runs]
def unexpandRuns : Unexpander
  | `($_ $d $σ $stim $tr) => `($d / $stim ⇓[$σ] $tr)
  | _ => throw ()

/-- Display `RefinesFromReset d "clk" "rst" (Design.firstOutput d) model` as
`d ⊑@clk[from rst] model`. Fires only on string-literal clock/reset names
and a `Design.firstOutput _` observed column (the exact shape the `⊑@`
notation elaborates to — `@[pp_nodot]` on `firstOutput` keeps the
delaborated argument in that form); anything else shows the raw judgment. -/
@[app_unexpander LeanModels.Sv.RefinesFromReset]
def unexpandRefinesFromReset : Unexpander
  | `($_ $d $clk:str $rst:str $out $model) => do
      let clkId := mkIdent (Name.mkSimple clk.getString)
      let rstId := mkIdent (Name.mkSimple rst.getString)
      match out with
      | `(Design.firstOutput $_) => `($d ⊑@$clkId[from $rstId] $model)
      | _ => throw ()
  | _ => throw ()

/-! ## Bridges: raw (Proofs.lean) forms ↔ surface forms

The raw theorems speak `sampledRst`/`counterModelRun`/`"count"`; the
judgments speak `sampled · rst`/`modelRun model`/`Design.firstOutput d`.
Each bridge is one definitional or one-induction lemma, consumed as
`sv_prove` simp extras. -/

/-- `sampledRst` (Proofs.lean) is the generic `sampled` at `"rst"`. -/
theorem sampledRst_eq : sampledRst = fun s => sampled s "rst" := rfl

/-- `counterModelRun` (Proofs.lean) is `modelRun` at `counterModel`. -/
theorem counterModelRun_eq (s : BitVec 8) (rs : List Bool) :
    counterModelRun s rs = modelRun counterModel s rs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp [counterModelRun, modelRun, ih]

/-- `counter`'s observed column is its (only) output port, `count`. -/
theorem counter_firstOutput : counterDesign.firstOutput = "count" := rfl

/-! ## The M0 theorems in surface form

Raw forms stay in `Proofs.lean` (∀-fuel hypothesis shape); each surface form
below is an `sv_prove` corollary. Theorem 1 (`run_functional`) is in
`Surface.lean`. -/

/-- **M0 theorem 2, surface form** (gallery `swap_nba_spec` shape): under
every schedule, every posedge step swaps `a`/`b` — the pre-edge startup
state included. Corollary of `swap_nba_spec`. -/
theorem swap_nba_swaps :
    swapNbaDesign ⊨ onPosedge fun s s' =>
      SvState.lookup s' "a" = SvState.lookup s "b" ∧
      SvState.lookup s' "b" = SvState.lookup s "a" := by
  sv_prove [swap_nba_spec]

/-- **M0 theorem 3, surface form** (gallery `race_blk_racy` content): two
legal schedules, the same 1-cycle stimulus, two different traces — stated in
the `⇓[σ]` run judgment. Corollary of (in fact: identical to)
`race_blk_racy`. -/
theorem race_blk_race :
    ∃ (σ₁ σ₂ : ScheduleOracle) (tr₁ tr₂ : List SvState),
      (raceBlkDesign / raceStim ⇓[σ₁] tr₁) ∧ (raceBlkDesign / raceStim ⇓[σ₂] tr₂) ∧
      tr₁ ≠ tr₂ := by
  sv_prove [race_blk_racy]

/-- **M0 theorem 4, surface form** — the gallery's
`counter ⊑@clk[from rst] counterModel`, verbatim: from the first sampled
reset, the sampled `count` column follows the golden model, for every legal
schedule and every abstract pre-reset state. Corollary of
`counter_from_reset` through the three bridges. -/
theorem counter_refines : counterDesign ⊑@clk[from rst] counterModel := by
  sv_prove [counter_from_reset, sampledRst_eq, counterModelRun_eq, counter_firstOutput]

/-! ### Non-vacuity and determinism, in surface notation

The `⊨`/`⊑@` forms are hypothesis-conditioned; these pin that the runs they
condition on exist (canonical traces, every σ), and re-derive the
`Sv.Deterministic` facts through `sv_prove`'s totality arm. -/

/-- `swap_nba` really runs, under every schedule: the canonical swapped
trace, in `⇓[σ]` form (= `swap_nba_total`). -/
theorem swap_nba_runs (σ : ScheduleOracle) (stim : List SvState) :
    swapNbaDesign / stim ⇓[σ]
      swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim := by
  sv_prove [swap_nba_total σ stim]

/-- `counter` really runs, under every schedule (= `counter_total`). -/
theorem counter_runs (σ : ScheduleOracle) (stim : List SvState) :
    counterDesign / stim ⇓[σ]
      counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim := by
  sv_prove [counter_total σ stim]

-- `sv_prove`'s Deterministic-from-totality arm re-derives the Proofs.lean
-- determinism bonuses; the not-deterministic gallery shape is arm 1.
example : Deterministic swapNbaDesign := by sv_prove [swap_nba_total]
example : Deterministic counterDesign := by sv_prove [counter_total]
example : ¬ Deterministic raceBlkDesign := by sv_prove [race_blk_not_deterministic]

/-! ## Pinned renderings (regression tests)

Each `#check` is `#guard_msgs`-pinned to the surface rendering; the `rfl`
round-trips confirm every rendering re-elaborates to the proposition it
displays. -/

section DelabTests

/-- info: ∀ (d : Design) (P : TraceProp), d ⊨ P : Prop -/
#guard_msgs in
#check ∀ (d : Design) (P : TraceProp), Models d P

/-- info: ∀ (d : Design) (R : SvState → SvState → Prop), d ⊨ onPosedge R : Prop -/
#guard_msgs in
#check ∀ (d : Design) (R : SvState → SvState → Prop), Models d (onPosedge R)

/-- info: ∀ (d : Design) (σ : ScheduleOracle) (stim tr : List SvState), d / stim ⇓[σ] tr : Prop -/
#guard_msgs in
#check ∀ (d : Design) (σ : ScheduleOracle) (stim tr : List SvState), Runs d σ stim tr

/-- info: ∀ (d : Design) (model : BitVec 8 → Bool → BitVec 8), d ⊑@clk[from rst] model : Prop -/
#guard_msgs in
#check ∀ (d : Design) (model : BitVec 8 → Bool → BitVec 8),
  RefinesFromReset d "clk" "rst" (Design.firstOutput d) model

/--
info: LeanModels.Sv.swap_nba_swaps :
  swapNbaDesign ⊨ onPosedge fun s s' => s'.lookup "a" = s.lookup "b" ∧ s'.lookup "b" = s.lookup "a"
-/
#guard_msgs in
#check swap_nba_swaps

/-- info: LeanModels.Sv.counter_refines : counterDesign ⊑@clk[from rst] counterModel -/
#guard_msgs in
#check counter_refines

/--
info: LeanModels.Sv.race_blk_race :
  ∃ σ₁ σ₂ tr₁ tr₂, raceBlkDesign / raceStim ⇓[σ₁] tr₁ ∧ raceBlkDesign / raceStim ⇓[σ₂] tr₂ ∧ tr₁ ≠ tr₂
-/
#guard_msgs in
#check race_blk_race

/--
info: LeanModels.Sv.swap_nba_runs (σ : ScheduleOracle) (stim : List SvState) :
  swapNbaDesign / stim ⇓[σ] swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim
-/
#guard_msgs in
#check swap_nba_runs

-- Round-trips: every rendering above re-elaborates to what it displays.
example (d : Design) (P : TraceProp) : (d ⊨ P) = Models d P := rfl
example (d : Design) (σ : ScheduleOracle) (stim tr : List SvState) :
    (d / stim ⇓[σ] tr) = Runs d σ stim tr := rfl
example (d : Design) (model : BitVec 8 → Bool → BitVec 8) :
    (d ⊑@clk[from rst] model) =
      RefinesFromReset d "clk" "rst" (Design.firstOutput d) model := rfl

end DelabTests

/-! ## Axiom pins (surface theorems use only the standard axioms) -/

/-- info: 'LeanModels.Sv.swap_nba_swaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap_nba_swaps

/-- info: 'LeanModels.Sv.race_blk_race' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms race_blk_race

/-- info: 'LeanModels.Sv.counter_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counter_refines

/-- info: 'LeanModels.Sv.run_functional' depends on axioms: [propext] -/
#guard_msgs in
#print axioms run_functional

end LeanModels.Sv
