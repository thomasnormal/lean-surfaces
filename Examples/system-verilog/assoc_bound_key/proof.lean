import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocBoundKey.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_bound_key/assoc_bound_key.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "assoc-bound-key fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "assoc-bound-key fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocBoundKey.proof
