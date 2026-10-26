import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.sdfStaticScope.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sdf_static_scope/sdf_static_scope.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sdf-static-scope fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "sdf-static-scope fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.sdfStaticScope.proof
