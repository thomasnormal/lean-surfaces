import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringIntegerConversion.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_integer_conversion/string_integer_conversion.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-integer-conversion fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-integer-conversion fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringIntegerConversion.proof
