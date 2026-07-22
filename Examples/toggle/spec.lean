/-
Examples/toggle — the three-file example layout (SV lane):

  toggle.sv      — the design (always_ff reset/enable T-flip-flop)
  toggle.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean      — THIS FILE: envelope certification, concrete runs in
                   surface syntax (`#sv_check`), and the surface-form
                   theorem STATEMENTS, each proved `:= by proofs`
  proof.lean     — the real proofs (namespace `Examples.toggle.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module. The
statement duplication between spec and proof is BY DESIGN (Lean has no
forward declarations) and is typechecked by the `:= by proofs` reference.
Unlike the Python lane there is no per-file `load_program`: the design
constant lives once in proof.lean, the spec opens it, and the `#eval`
below certifies it node-for-node equal to the extracted envelope.
-/
import Examples.toggle.proof
import LeanModels.Sv.Tests
import LeanModels

open LeanModels.Sv
open Examples.toggle.proof (toggleDesign toggleTrace toggleModel toggleModelRun)

/-! Envelope certification: the proof module's hand-built design literal is
node-for-node the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/toggle/toggle.sv.json"
  unless d == toggleDesign do
    throw (IO.userError "Examples/toggle/toggle.sv.json ≠ toggleDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "toggle envelope has unsupported nodes")

/-! Non-vacuity: concrete runs in surface syntax (`#sv_check`, Surface.lean
— fixed generous fuel), reproducing the Xcelium-verified outcomes
(harness/sv/cases.json rows `toggle_directed`/`toggle_x`). -/

-- reset pulse, then en for 3 cycles: q toggles 0 → 1 → 0 → 1
#sv_check toggleDesign
    [[clk := 1, rst := 1], [clk := 1, rst := 0, en := 1],
     [clk := 1, rst := 0, en := 1], [clk := 1, rst := 0, en := 1]]
  shows q = [0, 1, 0, 1]

-- en = 0 holds q (the elseless inner if is a no-op)
#sv_check toggleDesign [[clk := 1, rst := 1], [rst := 0, en := 0], [en := 0]]
  shows q = [0, 0, 0]

-- before the first reset q is x, and ~x = x: reset is load-bearing
#sv_check toggleDesign [[clk := 1, rst := 0, en := 1]] shows q = [x]

/-- **The from-reset refinement, surface form**: under every legal schedule
and every stimulus, from any snapshot that sampled `rst` true, the `q`
column follows the golden model
`fun q (rst, en) => if rst then false else if en then !q else q`
iterated over the sampled `(rst, en)` columns — starting from EVERY
abstract state `q₀`. This is `⊑@clk[from rst]`'s content generalized to a
two-input model; the M0 `RefinesFromReset` judgment fixes the model input
to the sampled reset `Bool` alone, so the same content is stated through
`⊨`/`spec` (see proof.lean's docstring). Raw form and proof:
`Examples/toggle/proof.lean`. -/
theorem toggle_refines_model :
    toggleDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (s : SvState), tr[i]? = some s → sampled s "rst" = true →
        ∀ q₀ : Bool,
          (tr.drop i).map (fun s' => SvState.lookup s' "q") =
            (toggleModelRun q₀ ((tr.drop i).map
                (fun s' => (sampled s' "rst", sampled s' "en")))).map
              (fun b => some (LVec.ofBool b)) := by proofs

/-- `toggle` really runs, under every schedule: the canonical trace
(x startup included), in `⇓[σ]` form. -/
theorem toggle_runs (σ : ScheduleOracle) (stim : List SvState) :
    toggleDesign / stim ⇓[σ]
      toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) stim := by
  proofs

/-- `toggle` is schedule-deterministic (single edge process). -/
theorem toggle_det : Deterministic toggleDesign := by proofs

/-! ## Pinned renderings + axiom pins (the surface prints as written; no
sorry, no native_decide — standard axioms only) -/

/--
info: toggle_refines_model :
  toggleDesign ⊨
    spec fun _stim tr =>
      ∀ (i : Nat) (s : SvState),
        tr[i]? = some s →
          sampled s "rst" = true →
            ∀ (q₀ : Bool),
              List.map (fun s' => s'.lookup "q") (List.drop i tr) =
                List.map (fun b => some (LVec.ofBool b))
                  (toggleModelRun q₀ (List.map (fun s' => (sampled s' "rst", sampled s' "en")) (List.drop i tr)))
-/
#guard_msgs in
#check toggle_refines_model

/--
info: toggle_runs (σ : ScheduleOracle) (stim : List SvState) :
  toggleDesign / stim ⇓[σ] toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) stim
-/
#guard_msgs in
#check toggle_runs

/-- info: 'toggle_refines_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toggle_refines_model
