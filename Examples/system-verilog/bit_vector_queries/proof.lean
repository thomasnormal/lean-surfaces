import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.bitVectorQueries.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

def duplicateQuery : SExpr :=
  .bitQuery .countbits (.m0 (.ident "value"))
    #[.m0 (.ident "control"), .m0 (.ident "control")]

def singleQuery : SExpr :=
  .bitQuery .countbits (.m0 (.ident "value")) #[.m0 (.ident "control")]

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/bit_vector_queries/runtime_controls.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real query fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "real query fixture process shape changed")
  let some (SStmt.assign false "selected" query) := statements[5]?
    | throw (IO.userError "real query fixture assignment shape changed")
  unless query == duplicateQuery do
    throw (IO.userError "proved query differs from the extracted real fixture")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real query fixture did not print PASS")

#guard evalSExpr 16 [("value", .lit "10xz01"), ("control", .lit "101")]
  duplicateQuery == .ok (.ofNat 32 2)

#guard evalSExpr 16 [("value", .lit "10xz01"), ("control", .lit "01x")]
  duplicateQuery == .ok (.ofNat 32 1)

theorem duplicate_control_counts_once (value control : LVec) :
    evalSExpr 16 [("value", value), ("control", control)] duplicateQuery =
      evalSExpr 16 [("value", value), ("control", control)] singleQuery := by
  simp [duplicateQuery, singleQuery, evalSExpr, evalSExprs, evalExpr, readSignal,
    SvState.lookup, evalBitQuery, countSelected_duplicate, Bind.bind, Pure.pure]

#print axioms duplicate_control_counts_once

end Examples.systemVerilog.bitVectorQueries.proof
