import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.literalFormatConcat.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/literal_format_concat/literal_format_concat.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal-format-concat fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "literal-format-concat fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.literalFormatConcat.proof
