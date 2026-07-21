/-
Examples/swap_nba — the three-file example layout (SV lane):

  swap_nba.sv      — the design (nonblocking assigns — the correct swap)
  swap_nba.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean        — THIS FILE: envelope certification, concrete runs in
                     surface syntax (`#sv_check`), and the surface-form
                     theorem STATEMENTS, each proved `:= by proofs`
  proof.lean       — the real proofs (namespace `Examples.swap_nba.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module. The
statement duplication between spec and proof is BY DESIGN (Lean has no
forward declarations) and is typechecked by the `:= by proofs` reference.
Unlike the Python lane there is no per-file `load_program`: the design
constant lives once in proof.lean, the spec opens it, and the `#eval`
below certifies it node-for-node equal to the extracted envelope.
-/
import Examples.swap_nba.proof
import LeanModels.Sv.Tests
import LeanModels

open LeanModels.Sv
open Examples.swap_nba.proof (swapNbaDesign swapNbaTrace)

/-! Envelope certification: the proof module's hand-built design literal is
node-for-node the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/swap_nba/swap_nba.sv.json"
  unless d == swapNbaDesign do
    throw (IO.userError "Examples/swap_nba/swap_nba.sv.json ≠ swapNbaDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "swap_nba envelope has unsupported nodes")

/-! Non-vacuity: concrete runs in surface syntax (`#sv_check`, Surface.lean
— fixed generous fuel), reproducing the Xcelium-verified outcomes. -/

-- swap_nba: swaps every cycle — and under the reversed schedule too
#sv_check swapNbaDesign [[clk := 1], [clk := 1]] shows a = [2, 1], b = [1, 2]
#sv_check swapNbaDesign [[clk := 1], [clk := 1]] under σ_rev shows a = [2, 1], b = [1, 2]

/-- **M0 theorem 2, surface form** (gallery `swap_nba_spec` shape): under
every schedule, every posedge step swaps `a`/`b` — the pre-edge startup
state included. Raw form and proof: `Examples/swap_nba/proof.lean`. -/
theorem swap_nba_swaps :
    swapNbaDesign ⊨ onPosedge fun s s' =>
      SvState.lookup s' "a" = SvState.lookup s "b" ∧
      SvState.lookup s' "b" = SvState.lookup s "a" := by proofs

/-- `swap_nba` really runs, under every schedule: the canonical swapped
trace, in `⇓[σ]` form. -/
theorem swap_nba_runs (σ : ScheduleOracle) (stim : List SvState) :
    swapNbaDesign / stim ⇓[σ]
      swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim := by proofs

/-! ## Pinned renderings + axiom pins (the surface prints as written; no
sorry, no native_decide — standard axioms only) -/

/--
info: swap_nba_swaps :
  swapNbaDesign ⊨ onPosedge fun s s' => s'.lookup "a" = s.lookup "b" ∧ s'.lookup "b" = s.lookup "a"
-/
#guard_msgs in
#check swap_nba_swaps

/--
info: swap_nba_runs (σ : ScheduleOracle) (stim : List SvState) :
  swapNbaDesign / stim ⇓[σ] swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim
-/
#guard_msgs in
#check swap_nba_runs

/-- info: 'swap_nba_swaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap_nba_swaps
