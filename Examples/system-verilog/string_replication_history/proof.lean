import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringReplicationHistory.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- REFERENCE: 82f4f2f0cc4388ec09b60d4e 24.03-s004 2026-10-20 | tests=dynamic_string | source=Examples/system-verilog/replication/dynamic_string.sv@sha256:0a0c353132b7a1b138b565a6731dbe3d1ef11fbab7d16db05fabb4b484889a7e | top=top | args=["-ii_val"] | map=../replication/README.md#integral-replication
-- SYNTHETIC-ORACLE: tests=fixtureReceipt | origin=spec | authority=docs/sv-assignment-targets.md#source-pure-string-replication-writes | map=history:unconditional-blocking-ascii;replication:constant-count;display:packed-bytes

def fixtureReceipt : IO Unit := do
  let .ok design := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/replication/dynamic_string.sv.json")
    | throw (IO.userError "dynamic_string failed to load")
  unless runSelfCheck design 32768 == .ok ["dynamic abab"] do
    throw (IO.userError "dynamic_string transcript differs")

#eval fixtureReceipt

end Examples.systemVerilog.stringReplicationHistory.proof
