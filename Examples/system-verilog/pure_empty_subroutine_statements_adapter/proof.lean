import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureEmptySubroutineStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_empty_subroutine_statements_adapter/pure_empty_subroutine_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure empty subroutine adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure empty subroutine adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureEmptySubroutineStatementsAdapter.proof
