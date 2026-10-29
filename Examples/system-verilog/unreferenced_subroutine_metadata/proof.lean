import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unreferencedSubroutineMetadata.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unreferenced_subroutine_metadata/unreferenced_subroutine_metadata.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unreferenced subroutine fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unreferenced subroutine fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unreferencedSubroutineMetadata.proof
