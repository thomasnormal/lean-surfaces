/-
Examples/adder — the three-file example layout (SV lane):

  adder.sv      — the design (continuous-assign 8-bit adder)
  adder.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean     — THIS FILE: envelope certification, concrete runs in
                  surface syntax (`#sv_check`), and the surface-form
                  theorem STATEMENTS, each proved `:= by proofs`
  proof.lean    — the real proofs (namespace `Examples.adder.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module. The
statement duplication between spec and proof is BY DESIGN (Lean has no
forward declarations) and is typechecked by the `:= by proofs` reference.
Unlike the Python lane there is no per-file `load_program`: the design
constant lives once in proof.lean, the spec opens it, and the `#eval`
below certifies it node-for-node equal to the extracted envelope.
-/
import Examples.adder.proof
import LeanModels.Sv.Tests
import LeanModels

open LeanModels.Sv
open Examples.adder.proof (adderDesign adderTrace)

/-! Envelope certification: the proof module's hand-built design literal is
node-for-node the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/adder/adder.sv.json"
  unless d == adderDesign do
    throw (IO.userError "Examples/adder/adder.sv.json ≠ adderDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "adder envelope has unsupported nodes")

/-! Non-vacuity: concrete runs in surface syntax (`#sv_check`, Surface.lean
— fixed generous fuel), reproducing the Xcelium-verified outcomes
(gallery example 1; the differential matrix lives in
harness/sv/cases.json). -/

-- known add, and mod-2^8 wrap: 200 + 100 = 300 ≡ 44
#sv_check adderDesign [[a := 5, b := 3], [a := 200, b := 100]] shows s = [8, "00101100"]

-- whole-vector x-collapse: ONE x input bit → ALL EIGHT result bits x (§11.4.3)
#sv_check adderDesign [[a := "0000000x", b := 3]] shows s = [x]

-- with no stimulus for a cycle, inputs stay x from startup → s all-x
#sv_check adderDesign [[]] shows s = [x]

/-- **Gallery example 1, known-inputs form** (`adder_spec`): for every
legal schedule and every stimulus, any settled snapshot whose inputs are
the embedded `BitVec 8` values `a`/`b` shows their sum on `s` (mod-2^8
wrap inherited from `BitVec` arithmetic). The `BitVec` binders are the
gallery's point: the theorem speaks about KNOWN (x/z-free) inputs, and the
embedding makes that hypothesis explicit. Raw form and proof:
`Examples/adder/proof.lean`. -/
theorem adder_spec (a b : BitVec 8) :
    adderDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState), tr[i]? = some st →
        SvState.lookup st "a" = some (LVec.ofBitVec a) →
        SvState.lookup st "b" = some (LVec.ofBitVec b) →
        SvState.lookup st "s" = some (LVec.ofBitVec (a + b)) := by proofs

/-- **Gallery example 1, x-collapse form** (`adder_x_collapse`): one
`x`/`z` bit anywhere in either settled operand x-poisons ALL EIGHT result
bits (LRM §11.4.3 whole-vector collapse) — arithmetic on unknowns never
carries bit-precisely. -/
theorem adder_x_collapse :
    adderDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState) (va vb : LVec), tr[i]? = some st →
        SvState.lookup st "a" = some va →
        SvState.lookup st "b" = some vb →
        va.width = 8 → vb.width = 8 →
        va.allKnown = false ∨ vb.allKnown = false →
        SvState.lookup st "s" = some (LVec.xVec 8) := by proofs

/-- `adder` really runs, under every schedule: the canonical settled trace
(x startup included), in `⇓[σ]` form. -/
theorem adder_runs (σ : ScheduleOracle) (stim : List SvState) :
    adderDesign / stim ⇓[σ] adderTrace (LVec.xVec 8) (LVec.xVec 8) stim := by proofs

/-! ## Pinned renderings + axiom pins (the surface prints as written; no
sorry, no native_decide — standard axioms only) -/

/--
info: adder_spec (a b : BitVec 8) :
  adderDesign ⊨
    spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState),
        tr[i]? = some st →
          st.lookup "a" = some (LVec.ofBitVec a) →
            st.lookup "b" = some (LVec.ofBitVec b) → st.lookup "s" = some (LVec.ofBitVec (a + b))
-/
#guard_msgs in
#check adder_spec

/--
info: adder_x_collapse :
  adderDesign ⊨
    spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState) (va vb : LVec),
        tr[i]? = some st →
          st.lookup "a" = some va →
            st.lookup "b" = some vb →
              va.width = 8 →
                vb.width = 8 → va.allKnown = false ∨ vb.allKnown = false → st.lookup "s" = some (LVec.xVec 8)
-/
#guard_msgs in
#check adder_x_collapse

/--
info: adder_runs (σ : ScheduleOracle) (stim : List SvState) :
  adderDesign / stim ⇓[σ] adderTrace (LVec.xVec 8) (LVec.xVec 8) stim
-/
#guard_msgs in
#check adder_runs

/-- info: 'adder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adder_spec

/-- info: 'adder_x_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adder_x_collapse
