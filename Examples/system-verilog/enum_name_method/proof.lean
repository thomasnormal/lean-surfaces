import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.enumNameMethod.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/enum_name_method/enum_name_method.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "enum-name-method fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "name=BLUE", "unknown=''"] do
    throw (IO.userError "enum-name-method fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.enumNameMethod.proof
