import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.selectedTypes.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false

def structPart : SExpr := .squash2
  (.selectRead 4 false true (.m0 (.ident "struct_value")) (.m0 (.ident "index_value")))

def mixedPart : SExpr :=
  .selectRead 4 false true (.m0 (.ident "mixed_value")) (.m0 (.ident "index_value"))

/-- An unknown index into a two-state aggregate yields zero, for any source. -/
theorem unknown_struct (source : LVec) :
    evalSExpr 32 [("struct_value", source),
      ("index_value", .lit "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")] structPart =
    .ok (.lit "0000") := by
  have unknown : selectedIndex true (.lit "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx") = none := by
    change selectedIndex true ⟨#[.lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx]⟩ = none
    simp [selectedIndex, toIntS?, LVec.toNat?, LVec.allKnown, Logic.isKnown]
  simp [structPart, evalSExpr, evalExpr, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, selectedRead, unknown]
  change squash2v (LVec.xVec 4) = ⟨#[.l0, .l0, .l0, .l0]⟩
  simp [squash2v, LVec.toTwoState, LVec.xVec, LVec.replicate]
  rfl

private theorem index_six : selectedIndex true
    (.lit "00000000000000000000000000000110") = some 6 := by
  change selectedIndex true (LVec.ofNat 32 6) = some 6
  have sign : msb (LVec.ofNat 32 6) = .l0 := by
    simp [msb, LVec.ofNat, Array.back?_eq_getElem?] <;> decide
  have zero_one : (Logic.l0 == Logic.l1) = false := rfl
  simp [selectedIndex, toIntS?, LVec.toNat?_ofNat, sign, zero_one]

/-- Partial overlap keeps the high source bits and clears only the invalid bits. -/
theorem partial_struct (a b c d e f g h : Logic) :
    evalSExpr 32 [("struct_value", ⟨#[a, b, c, d, e, f, g, h]⟩),
      ("index_value", .lit "00000000000000000000000000000110")] structPart =
    .ok (squash2v ⟨#[g, h, .lx, .lx]⟩) := by
  simp [structPart, evalSExpr, evalExpr, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, selectedRead, index_six, Array.ofFn_succ]

/-- A mixed aggregate's whole four-state type retains the invalid-bit x fill. -/
theorem partial_mixed (a b c d e f g h : Logic) :
    evalSExpr 32 [("mixed_value", ⟨#[a, b, c, d, e, f, g, h]⟩),
      ("index_value", .lit "00000000000000000000000000000110")] mixedPart =
    .ok ⟨#[g, h, .lx, .lx]⟩ := by
  simp [mixedPart, evalSExpr, evalExpr, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, selectedRead, index_six, Array.ofFn_succ]

#print axioms unknown_struct
#print axioms partial_struct
#print axioms partial_mixed

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/selected_types/selected_types.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "selected-types fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "selected-types process shape changed")
  unless statements[10]? == some (.assign false "struct_part" structPart) &&
      statements[11]? == some (.assign false "mixed_part" mixedPart) do
    throw (IO.userError "proved selections differ from the extracted fixture")
  unless runSelfCheck design 4096 == .ok [
      "inside 1001 1001 xz01 1001",
      "partial 0010 0010 xx10 0010",
      "negative 0100 0100 01xx 0100",
      "outside 0 0 x 0",
      "unknown 0000 0000 xxxx 0000",
      "minus 0100 0100 01xx 0100",
      "simple 0010 0100 xx10 0000",
      "integral 000a 0010 0010 1010", "PASS"] do
    throw (IO.userError "selected-types fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.selectedTypes.proof
