/-
Examples/xsel — the three-file example layout (SV lane), demo-only form:

  xsel.sv      — the design (always_comb if/else mux)
  xsel.sv.json — generated envelope (extractors/sv/extract.py)
  spec.lean    — THIS FILE: the design literal, envelope certification,
                 and concrete runs in surface syntax (`#sv_check`)

No theorems have been proved about `xsel` yet, so there is no `proof.lean`
(the three-file layout drops to two files; when the first theorem lands,
its raw form and proof move to a new `Examples/xsel/proof.lean` —
namespace `Examples.xsel.proof` — and its surface statement is stated here
`:= by proofs`). Since no proof module holds the design constant, the
literal lives here, certified node-for-node equal to the extracted
envelope by the `#eval` below.
-/
import LeanModels.Sv.Tests

open LeanModels.Sv

/-- `Examples/xsel/xsel.sv` (`always_comb` if/else mux on `sel`),
hand-transcribed. -/
def xselDesign : Design :=
  { name := "xsel"
    decls := #[
      { name := "sel", width := 1, isInput := true },
      { name := "a", width := 8, isInput := true },
      { name := "b", width := 8, isInput := true },
      { name := "y", width := 8, isOutput := true }]
    processes := #[
      .alwaysComb (.ifStmt (.ident "sel")
        (.blockingAssign "y" (.ident "a"))
        (some (.blockingAssign "y" (.ident "b"))))] }

/-! Envelope certification: the hand-built design literal is node-for-node
the extracted envelope (a mismatch fails the file). -/
#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/xsel/xsel.sv.json"
  unless d == xselDesign do
    throw (IO.userError "Examples/xsel/xsel.sv.json ≠ xselDesign")
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
