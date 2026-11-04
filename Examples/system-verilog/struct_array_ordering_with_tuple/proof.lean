import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structArrayOrderingWithTuple.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_array_ordering_with_tuple/struct_array_ordering_with_tuple.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct-array tuple-ordering fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "struct-array tuple-ordering fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structArrayOrderingWithTuple.proof
