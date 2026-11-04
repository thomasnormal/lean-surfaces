import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.arrayOobReads.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/array_oob_reads/array_oob_reads.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "array-oob-reads fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "array-oob-reads fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.arrayOobReads.proof
