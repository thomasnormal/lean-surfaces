import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedPatternReplication.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unpacked_pattern_replication/unpacked_pattern_replication.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested-pattern fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested-pattern fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedPatternReplication.proof
