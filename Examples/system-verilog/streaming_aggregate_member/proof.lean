import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingAggregateMember.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_aggregate_member/streaming_aggregate_member.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "streaming-aggregate-member fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "streaming-aggregate-member fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingAggregateMember.proof
