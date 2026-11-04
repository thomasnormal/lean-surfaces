import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.formattedInput.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The zero-match statement in the extracted copyback fixture. -/
def zeroMatch : SStmt :=
  .scanf (.m0 (.lit (.ofNat 24 7413815)))
    [.conversion false none 'h', .whitespace, .conversion false none 'h']
    [[.selected "word" 4 false true false (.m0 (.lit (.ofNat 32 8)))],
     [.selected "word" 4 false true false (.m0 (.lit (.ofNat 32 4)))]]
    [.whole "n" 32 false]

/-- Failure before conversion leaves the entire packed destination unchanged. -/
theorem zero_match_preserves_word (word : LVec) :
    execSStmt 32 [("word", word), ("n", .ofNat 32 99)] [] {} zeroMatch =
      .ok ([("word", word), ("n", .ofNat 32 0)], [], {}) := by
  have packed : FormattedInput.packedCharacters (.ofNat 24 7413815) =
      .ok ['q', ' ', '7'] := by
    simp only [FormattedInput.packedCharacters, LVec.toNat?_ofNat, LVec.width_ofNat]
    rfl
  have scanned : FormattedInput.scan (.ofNat 24 7413815)
      [.conversion false none 'h', .whitespace, .conversion false none 'h'] [4, 4] =
      .ok (0, []) := by
    simp only [FormattedInput.scan, packed]
    rfl
  have zero : ((LVec.ofNat 32 0).resizeSigned 32).extract 0 32 = .ofNat 32 0 := by decide
  have order : ([0] : List Nat).eraseDups.length = 1 := by decide
  have countWidth : (LVec.ofNat 32 99).width = 32 := rfl
  simp [zeroMatch, execSStmt, evalSExpr, evalExpr, scanned,
    execScanWrites, execPackedTargets, packedTargetSlices, PackedTarget.width,
    rightToLeftAssignmentOrder, validAssignmentOrder, SvState.lookup, SvState.set,
    zero, order, countWidth, Bind.bind, Pure.pure]

#print axioms zero_match_preserves_word

/-- The fixture deliberately aliases an output with the return destination. -/
def resultLast : SStmt :=
  .scanf (.m0 (.lit (.ofNat 16 12594))) [.conversion false none 'd']
    [[.whole "n" 32 false]] [.whole "n" 32 false]

/-- The return count replaces the earlier converted value in the same variable. -/
theorem return_count_is_last :
    execSStmt 32 [("n", .ofNat 32 99)] [] {} resultLast =
      .ok ([("n", .ofNat 32 1)], [], {}) := by
  have packed : FormattedInput.packedCharacters (.ofNat 16 12594) =
      .ok ['1', '2'] := by
    simp only [FormattedInput.packedCharacters, LVec.toNat?_ofNat, LVec.width_ofNat]
    rfl
  have scanned : FormattedInput.scan (.ofNat 16 12594)
      [.conversion false none 'd'] [32] = .ok (1, [.ofNat 32 12]) := by
    simp only [FormattedInput.scan, packed]
    rfl
  have first : (LVec.ofNat 32 12).extract 0 32 = .ofNat 32 12 := by decide
  have last : ((LVec.ofNat 32 1).resizeSigned 32).extract 0 32 = .ofNat 32 1 := by decide
  have order : ([0] : List Nat).eraseDups.length = 1 := by decide
  have oldWidth : (LVec.ofNat 32 99).width = 32 := rfl
  have newWidth : (LVec.ofNat 32 12).width = 32 := rfl
  simp [resultLast, execSStmt, evalSExpr, evalExpr, scanned,
    execScanWrites, execPackedTargets, packedTargetSlices, PackedTarget.width,
    rightToLeftAssignmentOrder, validAssignmentOrder, SvState.lookup, SvState.set,
    first, last, order, oldWidth, newWidth, Bind.bind, Pure.pure]

#print axioms return_count_is_last

-- Full independently observed transcripts, 2026-10-20. Source SHA-256:
-- copyback.sv: 6628e63543655738b05feab385d45ee533e667be0462a0edf4f0fd0f46d9b8af
-- values.sv: 9921540347ab3b18a4a7c8b44d056673b5f9079fff7678c4690471267bca42bc
-- The theorems above use kernel proofs.
def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/formatted_input/copyback.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "formatted-input fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "formatted-input process shape changed")
  unless statements[5]? == some zeroMatch && statements[12]? == some resultLast do
    throw (IO.userError "proved statement differs from the extracted source")
  unless runSelfCheck design 4096 == Res.ok [
      "full 2 b5af", "partial 1 b3af", "zero 0 b3af", "ordered 2 8 b5ef",
      "result_last 1", "overlap abc1", "two_state 1 00",
      "nul_characters 1 4120", "input_once 1 12", "concat 1 x 0"] do
    throw (IO.userError "formatted-input copyback transcript disagrees")


  let valuesText ← IO.FS.readFile "Examples/system-verilog/formatted_input/values.sv.json"
  let .ok values := loadEnvelopeDesign valuesText
    | throw (IO.userError "formatted-input values failed to load")
  unless runSelfCheck values 4096 == Res.ok [
      "decimal 1 ff85",
      "plus 1 002a",
      "decimal_x 1 000X",
      "decimal_z 1 000Z",
      "decimal_tail 1 000c",
      "underscores 1 007b",
      "leading_underscore 1 000c",
      "hex_prefix 1 0x12",
      "negative_hex 0 5555",
      "hex_x 1 xxxf",
      "hex_z 1 zzz1",
      "binary_question 1 zzzZ",
      "empty 0 5555",
      "whitespace 0 5555",
      "mismatch 0 5555",
      "sign_only 0 5555",
      "character_space 1 0020",
      "character_short 1 0041",
      "character_width 1 4142",
      "string 1 6263",
      "string_width 1 6162",
      "strength_one 1 0001",
      "strength_zero 1 0000",
      "strength_x 1 000X",
      "strength_z 1 000Z",
      "strength_lower 1 0001",
      "strength_other 1 0001",
      "strength_number 1 0001",
      "partial 1 0003 aaaa",
      "suppressed_eof 0 5555 aaaa",
      "suppressed_empty 0 5555 aaaa",
      "only_suppressed 0 5555 aaaa",
      "null_tail 1 000c",
      "null_middle 2 0001 0002",
      "underscore_only 0 0101010101010101",
      "negative_x 0 0101010101010101",
      "positive_hex 0 0101010101010101",
      "double_x 1 000000000000000x",
      "null_strings 2 0041 0042",
      "width_suppression 2 000c 0022",
      "literal 1 000c",
      "signed_width 2 fff4 0033",
      "based_width 2 00ab 0063",
      "based_leading 2 00ab 0063",
      "strength_width 2 0001 005a"] do
    throw (IO.userError "formatted-input values transcript disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.formattedInput.proof
