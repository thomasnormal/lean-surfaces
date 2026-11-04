import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringNullCharacter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_null_character/string_null_character.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-null-character fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-null-character fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringNullCharacter.proof
