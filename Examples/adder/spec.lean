/-
Examples/adder — the three-file example layout (SV lane), demo-only form:

  adder.sv      — the design (continuous-assign 8-bit adder)
  adder.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean     — THIS FILE: the design literal, envelope certification,
                  and concrete runs in surface syntax (`#sv_check`)

No theorems have been proved about `adder` yet, so there is no
`proof.lean` (the three-file layout drops to two files; when the first
theorem lands, its raw form and proof move to a new
`Examples/adder/proof.lean` — namespace `Examples.adder.proof` — and its
surface statement is stated here `:= by proofs`). Since no proof module
holds the design constant, the literal lives here, certified node-for-node
equal to the extracted envelope by the `#eval` below.
-/
import LeanModels.Sv.Tests

open LeanModels.Sv

/-- `Examples/adder/adder.sv` (continuous assign `s = a + b`),
hand-transcribed. -/
def adderDesign : Design :=
  { name := "adder"
    decls := #[
      { name := "a", width := 8, isInput := true },
      { name := "b", width := 8, isInput := true },
      { name := "s", width := 8, isOutput := true }]
    processes := #[.assign "s" (.binary .add (.ident "a") (.ident "b"))] }

/-! Envelope certification: the hand-built design literal is node-for-node
the extracted envelope (a mismatch fails the file). -/
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
