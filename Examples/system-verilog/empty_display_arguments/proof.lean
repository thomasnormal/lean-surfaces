import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyDisplayArguments.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_display_arguments/empty_display_arguments.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty display fixture failed to load")
  let expected := ["start msg1 end", "          5           2           3", "PASS"]
  unless SelfCheck.runSelfCheck design 4096 == .ok expected do
    throw (IO.userError "empty display fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyDisplayArguments.proof
