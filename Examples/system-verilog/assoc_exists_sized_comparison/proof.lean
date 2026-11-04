import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocExistsSizedComparison.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_exists_sized_comparison/assoc_exists_sized_comparison.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sized associative exists fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "sized associative exists fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocExistsSizedComparison.proof
