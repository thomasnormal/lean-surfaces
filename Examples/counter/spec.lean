/-
Examples/counter — the three-file example layout (SV lane):

  counter.sv      — the design (always_ff reset/increment counter)
  counter.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean       — THIS FILE: envelope certification, concrete runs in
                    surface syntax (`#sv_check`), and the surface-form
                    theorem STATEMENTS, each proved `:= by proofs`
  proof.lean      — the real proofs (namespace `Examples.counter.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module. The
statement duplication between spec and proof is BY DESIGN (Lean has no
forward declarations) and is typechecked by the `:= by proofs` reference.
Unlike the Python lane there is no per-file `load_program`: the design
constant lives once in proof.lean, the spec opens it, and the `#eval`
below certifies it node-for-node equal to the extracted envelope.
-/
import Examples.counter.proof
import LeanModels.Sv.Tests
import LeanModels

open LeanModels.Sv
open Examples.counter.proof (counterDesign counterModel counterTrace)

/-! Envelope certification: the proof module's hand-built design literal is
node-for-node the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/counter/counter.sv.json"
  unless d == counterDesign do
    throw (IO.userError "Examples/counter/counter.sv.json ≠ counterDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "counter envelope has unsupported nodes")

/-! Non-vacuity: concrete runs in surface syntax (`#sv_check`, Surface.lean
— fixed generous fuel), reproducing the Xcelium-verified outcomes. -/

-- counter: x through pre-reset edges (x+1 = x, LRM startup), reset, count
#sv_check counterDesign
    [[clk := 1, rst := 0], [clk := 1, rst := 0], [clk := 1, rst := 1],
     [clk := 1, rst := 0], [clk := 1, rst := 0], [clk := 1, rst := 0]]
  shows count = [x, x, 0, 1, 2, 3]

-- the stimulus cannot clobber the output; a held (absent) rst input
#sv_check counterDesign [[rst := 1, count := 77]] shows count = [0]
#sv_check counterDesign [[clk := 1, rst := 1], []] shows count = [0, 0]

/-- **M0 theorem 4, surface form** — the gallery's
`counter ⊑@clk[from rst] counterModel`, verbatim: from the first sampled
reset, the sampled `count` column follows the golden model
(`if rst then 0 else s + 1` on `BitVec 8`), for every legal schedule and
every abstract pre-reset state. Raw form and proof:
`Examples/counter/proof.lean`. -/
theorem counter_refines : counterDesign ⊑@clk[from rst] counterModel := by proofs

/-- `counter` really runs, under every schedule: the canonical trace
(x startup included), in `⇓[σ]` form. -/
theorem counter_runs (σ : ScheduleOracle) (stim : List SvState) :
    counterDesign / stim ⇓[σ]
      counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim := by proofs

/-! ## Pinned renderings + axiom pins (the surface prints as written; no
sorry, no native_decide — standard axioms only) -/

/-- info: counter_refines : counterDesign ⊑@clk[from rst] counterModel -/
#guard_msgs in
#check counter_refines

/--
info: counter_runs (σ : ScheduleOracle) (stim : List SvState) :
  counterDesign / stim ⇓[σ] counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim
-/
#guard_msgs in
#check counter_runs

/-- info: 'counter_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counter_refines
