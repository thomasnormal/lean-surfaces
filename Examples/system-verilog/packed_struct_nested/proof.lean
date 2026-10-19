import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedStructNested.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_struct_nested/packed_struct_nested.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested packed-struct fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested packed-struct fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedStructNested.proof
