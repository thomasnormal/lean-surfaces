import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.arrayNamedDisplay.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/array_named_display/array_named_display.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "array-named-display fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["ARRAY '{1, 2, 3}", "PASS"] do
    throw (IO.userError "array-named-display fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.arrayNamedDisplay.proof
