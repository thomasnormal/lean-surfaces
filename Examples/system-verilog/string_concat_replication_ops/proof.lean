import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringConcatReplicationOps.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_concat_replication_ops/string_concat_replication_ops.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string concat/replication fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["Hello_World!", "testtesttesttest"] do
    throw (IO.userError "string concat/replication fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringConcatReplicationOps.proof
