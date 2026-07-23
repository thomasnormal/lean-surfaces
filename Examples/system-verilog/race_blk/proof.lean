/-
Proof module for `Examples/system-verilog/race_blk/spec.lean` (three-file example layout,
SV lane). M0 theorem 3 of `docs/sv-design-m0.md` — the blocking-assign
race is schedule-dependent — relocated verbatim from the retired
`LeanModels/Sv/Proofs.lean` (raw witnesses) and `LeanModels/Sv/Delab.lean`
(surface corollary). Kernel evaluation via `decide` throughout; no
`native_decide` anywhere.

The design literal below is a hand-built copy of the extracted envelope;
`spec.lean` certifies (at elab time, from disk) that it is node-for-node
equal to `Examples/system-verilog/race_blk/race_blk.sv.json`.
-/
import LeanModels.Sv.Delab

namespace Examples.«system-verilog».race_blk.proof

open LeanModels.Sv

/-- `Examples/system-verilog/race_blk/race_blk.sv` (blocking assigns — the race). -/
def raceBlkDesign : Design :=
  { name := "race_blk"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (.ofNat 8 1) },
      { name := "b", width := 8, init := some (.ofNat 8 2) }]
    processes := #[
      .alwaysPlain "clk" (.blockingAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.blockingAssign "b" (.ident "a"))] }

/-! ## Theorem 3: `race_blk` is schedule-dependent -/

/-- The 1-cycle stimulus of the race witnesses (one posedge, `clk` driven
high — the interpreter's cycle semantics does not consult it, but the
stimulus mirrors the harness's). -/
def raceStim : List SvState := [[("clk", LVec.ofNat 1 1)]]

/-- Source order runs `a = b` then `b = a`: `a` picks up `2`, then `b` reads
the ALREADY-UPDATED `a` — `(2, 2)`. Kernel evaluation (`decide`). -/
theorem race_blk_src :
    run raceBlkDesign σ_src 8 raceStim =
      .ok [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 2), ("b", LVec.ofNat 8 2)]] := by
  decide

/-- Reverse order runs `b = a` first — `(1, 1)`. -/
theorem race_blk_rev :
    run raceBlkDesign σ_rev 8 raceStim =
      .ok [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 1), ("b", LVec.ofNat 8 1)]] := by
  decide

/-- **M0 theorem 3** (`docs/sv-design-m0.md`): two legal schedules, same
1-cycle stimulus, different traces — the Xcelium-verified `(2,2)` vs
`(1,1)` race, with σ_src/σ_rev as the concrete witnesses. -/
theorem race_blk_racy :
    ∃ (σ₁ σ₂ : ScheduleOracle) (tr₁ tr₂ : List SvState),
      Runs raceBlkDesign σ₁ raceStim tr₁ ∧ Runs raceBlkDesign σ₂ raceStim tr₂ ∧
      tr₁ ≠ tr₂ :=
  ⟨σ_src, σ_rev,
   [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 2), ("b", LVec.ofNat 8 2)]],
   [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 1), ("b", LVec.ofNat 8 1)]],
   ⟨8, race_blk_src⟩, ⟨8, race_blk_rev⟩, by decide⟩

/-- The gallery's `race_blk_racy` shape: the blocking-assign race means
`race_blk` is NOT schedule-deterministic. -/
theorem race_blk_not_deterministic : ¬ Deterministic raceBlkDesign := by
  intro h
  have := h σ_src σ_rev raceStim _ _ ⟨8, race_blk_src⟩ ⟨8, race_blk_rev⟩
  exact absurd this (by decide)

/-! ## The surface form (spec.lean's statement; `sv_prove` corollary) -/

/-- **M0 theorem 3, surface form** (gallery `race_blk_racy` content): two
legal schedules, the same 1-cycle stimulus, two different traces — stated in
the `⇓[σ]` run judgment. Corollary of (in fact: identical to)
`race_blk_racy`. -/
theorem race_blk_race :
    ∃ (σ₁ σ₂ : ScheduleOracle) (tr₁ tr₂ : List SvState),
      (raceBlkDesign / raceStim ⇓[σ₁] tr₁) ∧ (raceBlkDesign / raceStim ⇓[σ₂] tr₂) ∧
      tr₁ ≠ tr₂ := by
  sv_prove [race_blk_racy]

-- the not-deterministic gallery shape is `sv_prove`'s arm 1
example : ¬ Deterministic raceBlkDesign := by sv_prove [race_blk_not_deterministic]

end Examples.«system-verilog».race_blk.proof
