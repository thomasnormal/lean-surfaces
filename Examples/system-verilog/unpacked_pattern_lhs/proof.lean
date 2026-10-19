import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedPatternLhs.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unpacked_pattern_lhs/unpacked_pattern_lhs.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-pattern-LHS fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-pattern-LHS fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedPatternLhs.proof
