import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.orderingAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/ordering_adapter/ordering_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "ordering adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "ordering adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.orderingAdapter.proof
