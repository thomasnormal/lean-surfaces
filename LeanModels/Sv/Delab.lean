import LeanModels.Sv.Surface

/-!
# Delaborators for the SV surface judgments (`LeanModels.Sv`)

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

The per-design M0 theorems live in the three-file example layout
(`Examples/<design>/spec.lean` states them, `Examples/<design>/proof.lean`
proves them — raw fuel/`run` forms and their `sv_prove` surface
corollaries); the design-specific rendering and axiom pins live in those
spec files. Theorem 1's surface form (`run_functional`) is in
`Surface.lean` (it needs only Obs.lean).

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
displays).
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

/-! ## Pinned renderings (regression tests)

Each `#check` is `#guard_msgs`-pinned to the surface rendering; the `rfl`
round-trips confirm every rendering re-elaborates to the proposition it
displays. The per-design renderings (`swap_nba_swaps`, `counter_refines`,
`race_blk_race`, …) are pinned in their `Examples/<design>/spec.lean`. -/

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

-- Round-trips: every rendering above re-elaborates to what it displays.
example (d : Design) (P : TraceProp) : (d ⊨ P) = Models d P := rfl
example (d : Design) (σ : ScheduleOracle) (stim tr : List SvState) :
    (d / stim ⇓[σ] tr) = Runs d σ stim tr := rfl
example (d : Design) (model : BitVec 8 → Bool → BitVec 8) :
    (d ⊑@clk[from rst] model) =
      RefinesFromReset d "clk" "rst" (Design.firstOutput d) model := rfl

end DelabTests

/-! ## Axiom pin (surface theorems use only the standard axioms) -/

/-- info: 'LeanModels.Sv.run_functional' depends on axioms: [propext] -/
#guard_msgs in
#print axioms run_functional

end LeanModels.Sv
