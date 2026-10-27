import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.staticDependencyInitializer.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/static_dependency_initializer/static_dependency_initializer.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "static-dependency-initializer fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "static-dependency-initializer fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.staticDependencyInitializer.proof
