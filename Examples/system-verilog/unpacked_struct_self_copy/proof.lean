import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedStructSelfCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unpacked_struct_self_copy/unpacked_struct_self_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-struct-self-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-struct-self-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedStructSelfCopy.proof
