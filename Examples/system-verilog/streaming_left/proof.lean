import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingLeft.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false

def index0 : LVec := .lit "00000000000000000000000000000000"
def index4 : LVec := .lit "00000000000000000000000000000100"
def index8 : LVec := .lit "00000000000000000000000000001000"

def shortSource : SExpr := .m0 (.concat #[.ident "short_source"])

def leftChunks : SExpr := .concat #[
  .selectRead 4 false false shortSource (.m0 (.lit index0)),
  .selectRead 4 false false shortSource (.m0 (.lit index4)),
  .selectRead 2 false false shortSource (.m0 (.lit index8))]

/-- Four-bit slices reverse chunk order while the final high slice stays two bits. -/
theorem chunks_value (source : LVec) :
    evalSExpr 32 [("short_source", source)] leftChunks =
    .ok (LVec.concatMany #[
      selectedRead 4 false false (LVec.concatMany #[source]) index0,
      selectedRead 4 false false (LVec.concatMany #[source]) index4,
      selectedRead 2 false false (LVec.concatMany #[source]) index8]) := by
  rfl

#print axioms chunks_value

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_left/streaming_left.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "left-streaming fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "left-streaming process shape changed")
  unless statements[5]? == some (.assign false "chunk4" leftChunks) do
    throw (IO.userError "proved chunk expression differs from the extracted fixture")
  unless runSelfCheck design 4096 ==
      .ok ["0110zx01 110xz010 10xz0110 1010xz0110 110xz0100000", "PASS"] do
    throw (IO.userError "left-streaming fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingLeft.proof
