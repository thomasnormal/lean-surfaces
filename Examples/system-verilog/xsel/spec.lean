/-
Examples/system-verilog/xsel — the three-file example layout (SV lane):

  xsel.sv      — the design (always_comb if/else mux)
  xsel.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean    — THIS FILE: envelope certification, concrete runs in
                 surface syntax (`#sv_check`), and the surface-form
                 theorem STATEMENTS, each proved `:= by proofs`
  proof.lean   — the real proofs (namespace `Examples.«system-verilog».xsel.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module. The
statement duplication between spec and proof is BY DESIGN (Lean has no
forward declarations) and is typechecked by the `:= by proofs` reference.
Unlike the Python lane there is no per-file `load_program`: the design
constant lives once in proof.lean, the spec opens it, and the `#eval`
below certifies it node-for-node equal to the extracted envelope.
-/
import Examples.«system-verilog».xsel.proof
import LeanModels.Sv.Tests
import LeanModels

open LeanModels.Sv
open Examples.«system-verilog».xsel.proof (xselDesign xselTrace)

/-! Envelope certification: the proof module's hand-built design literal is
node-for-node the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/system-verilog/xsel/xsel.sv.json"
  unless d == xselDesign do
    throw (IO.userError "Examples/system-verilog/xsel/xsel.sv.json ≠ xselDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "xsel envelope has unsupported nodes")

/-! Non-vacuity: concrete runs in surface syntax (`#sv_check`, Surface.lean
— fixed generous fuel), reproducing the Xcelium-verified outcomes
(gallery example 5; the differential matrix lives in
harness/sv/cases.json). -/

-- known select: sel = 1 takes a, sel = 0 takes b
#sv_check xselDesign [[sel := 1, a := 0xAA, b := 0x55]] shows y = ["10101010"]
#sv_check xselDesign [[sel := 0, a := 0xAA, b := 0x55]] shows y = ["01010101"]

-- X-optimism (§12.4): sel = x and sel = z both take the ELSE branch — the
-- simulator picks b, it does NOT merge a/b bitwise
#sv_check xselDesign [[sel := "x", a := 0xAA, b := 0x55]] shows y = ["01010101"]
#sv_check xselDesign [[sel := "z", a := 0xAA, b := 0x55]] shows y = ["01010101"]

/-- **Gallery example 5, known-select form** (`xsel_known`): for every
legal schedule and every stimulus, any settled snapshot with an embedded
`Bool` select and embedded `BitVec 8` data inputs shows the Lean-level mux
`y = if sel then a else b`. Raw form and proof:
`Examples/system-verilog/xsel/proof.lean`. -/
theorem xsel_known (s : Bool) (a b : BitVec 8) :
    xselDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState), tr[i]? = some st →
        SvState.lookup st "sel" = some (LVec.ofBool s) →
        SvState.lookup st "a" = some (LVec.ofBitVec a) →
        SvState.lookup st "b" = some (LVec.ofBitVec b) →
        SvState.lookup st "y" = some (LVec.ofBitVec (if s then a else b)) := by proofs

/-- **Gallery example 5, X-optimism form** (`xsel_x_else`): a `sel` of `x`
or `z` takes the ELSE branch — `y = b`, never a bitwise `a`/`b` merge —
per LRM §12.4 (an `if` condition evaluating to zero, x, or z is not-true).
The `v = lx ∨ v = lz` hypothesis folds the gallery's `Logic.lz` twin into
the one statement. Real hardware might do anything; that the simulator's
optimism is *provable* makes the simulation/hardware gap a stateable
property instead of folklore. -/
theorem xsel_x_else (v : Logic) (hv : v = Logic.lx ∨ v = Logic.lz) :
    xselDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState) (vb : LVec), tr[i]? = some st →
        SvState.lookup st "sel" = some (LVec.ofLogic v) →
        SvState.lookup st "b" = some vb →
        SvState.lookup st "y" = some vb := by proofs

/-- `xsel` really runs, under every schedule: the canonical settled trace
(x startup included), in `⇓[σ]` form. -/
theorem xsel_runs (σ : ScheduleOracle) (stim : List SvState) :
    xselDesign / stim ⇓[σ] xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim := by
  proofs

/-! ## Pinned renderings + axiom pins (the surface prints as written; no
sorry, no native_decide — standard axioms only) -/

/--
info: xsel_known (s : Bool) (a b : BitVec 8) :
  xselDesign ⊨
    spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState),
        tr[i]? = some st →
          st.lookup "sel" = some (LVec.ofBool s) →
            st.lookup "a" = some (LVec.ofBitVec a) →
              st.lookup "b" = some (LVec.ofBitVec b) → st.lookup "y" = some (LVec.ofBitVec (if s = true then a else b))
-/
#guard_msgs in
#check xsel_known

/--
info: xsel_x_else (v : Logic) (hv : v = Logic.lx ∨ v = Logic.lz) :
  xselDesign ⊨
    spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState) (vb : LVec),
        tr[i]? = some st → st.lookup "sel" = some (LVec.ofLogic v) → st.lookup "b" = some vb → st.lookup "y" = some vb
-/
#guard_msgs in
#check xsel_x_else

/--
info: xsel_runs (σ : ScheduleOracle) (stim : List SvState) :
  xselDesign / stim ⇓[σ] xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim
-/
#guard_msgs in
#check xsel_runs

/-- info: 'xsel_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xsel_known

/-- info: 'xsel_x_else' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xsel_x_else
