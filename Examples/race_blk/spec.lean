/-
Examples/race_blk — the three-file example layout (SV lane):

  race_blk.sv      — the design (blocking assigns — the race)
  race_blk.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean        — THIS FILE: envelope certification, concrete runs in
                     surface syntax (`#sv_check`), and the surface-form
                     theorem STATEMENTS, each proved `:= by proofs`
  proof.lean       — the real proofs (namespace `Examples.race_blk.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module. The
statement duplication between spec and proof is BY DESIGN (Lean has no
forward declarations) and is typechecked by the `:= by proofs` reference.
Unlike the Python lane there is no per-file `load_program`: the design
constant lives once in proof.lean, the spec opens it, and the `#eval`
below certifies it node-for-node equal to the extracted envelope.
-/
import Examples.race_blk.proof
import LeanModels.Sv.Tests
import LeanModels

open LeanModels.Sv
open Examples.race_blk.proof (raceBlkDesign raceStim)

/-! Envelope certification: the proof module's hand-built design literal is
node-for-node the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/race_blk/race_blk.sv.json"
  unless d == raceBlkDesign do
    throw (IO.userError "Examples/race_blk/race_blk.sv.json ≠ raceBlkDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "race_blk envelope has unsupported nodes")

/-! Non-vacuity: concrete runs in surface syntax (`#sv_check`, Surface.lean
— fixed generous fuel), reproducing the Xcelium-verified outcomes. -/

-- race_blk: (2,2) under source order, (1,1) under reverse — the race
#sv_check raceBlkDesign [[clk := 1]] shows a = [2], b = [2]
#sv_check raceBlkDesign [[clk := 1]] under σ_rev shows a = [1], b = [1]

/-- **M0 theorem 3, surface form** (gallery `race_blk_racy` content): two
legal schedules, the same 1-cycle stimulus, two different traces — stated in
the `⇓[σ]` run judgment (σ_src/σ_rev with the Xcelium-verified `(2,2)` vs
`(1,1)` traces are the witnesses). Raw form and proof:
`Examples/race_blk/proof.lean`. -/
theorem race_blk_race :
    ∃ (σ₁ σ₂ : ScheduleOracle) (tr₁ tr₂ : List SvState),
      (raceBlkDesign / raceStim ⇓[σ₁] tr₁) ∧ (raceBlkDesign / raceStim ⇓[σ₂] tr₂) ∧
      tr₁ ≠ tr₂ := by proofs

/-- The gallery's `race_blk_racy` shape: the blocking-assign race means
`race_blk` is NOT schedule-deterministic. -/
theorem race_blk_not_deterministic : ¬ Deterministic raceBlkDesign := by proofs

/-! ## Pinned renderings + axiom pins (the surface prints as written; no
sorry, no native_decide — standard axioms only) -/

/--
info: race_blk_race : ∃ σ₁ σ₂ tr₁ tr₂, raceBlkDesign / raceStim ⇓[σ₁] tr₁ ∧ raceBlkDesign / raceStim ⇓[σ₂] tr₂ ∧ tr₁ ≠ tr₂
-/
#guard_msgs in
#check race_blk_race

/-- info: race_blk_not_deterministic : ¬Deterministic raceBlkDesign -/
#guard_msgs in
#check race_blk_not_deterministic

/-- info: 'race_blk_race' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms race_blk_race
