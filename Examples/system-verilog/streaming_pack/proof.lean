import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingPack.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false

def paddedPack : SStmt :=
  .m0 (.blockingAssign "wide"
    (.concat #[.ident "hi", .ident "lo", .lit (.lit "0000")]))

/-- The extracted source pack appends zeros after both sampled values. -/
theorem padded_pack (hi lo previous : LVec) :
    execSStmt 32 [("hi", hi), ("lo", lo), ("wide", previous)] [] {} paddedPack =
    .ok ([("hi", hi), ("lo", lo),
      ("wide", LVec.concatMany #[hi, lo, .lit "0000"])], [], {}) := by
  rfl

#print axioms padded_pack

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_pack/streaming_pack.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "streaming source fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "streaming source process shape changed")
  unless statements[5]? == some paddedPack do
    throw (IO.userError "proved pack differs from the extracted fixture")
  unless runSelfCheck design 4096 ==
      .ok ["10xz0110 10xz0110 011010xz 10xz01100000 10000110", "PASS"] do
    throw (IO.userError "streaming source fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingPack.proof
