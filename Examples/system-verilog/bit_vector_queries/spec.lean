import «Examples».«system-verilog».bit_vector_queries.proof

namespace Examples.systemVerilog.bitVectorQueries

open LeanModels.Sv LeanModels.Sv.SelfCheck

def countWithDuplicateControl (value control : LVec) : Res LVec :=
  evalSExpr 16 [("value", value), ("control", control)] proof.duplicateQuery

def countWithControl (value control : LVec) : Res LVec :=
  evalSExpr 16 [("value", value), ("control", control)] proof.singleQuery

#guard countWithDuplicateControl (.lit "10xz01") (.lit "101") == .ok (.ofNat 32 2)

theorem duplicate_control_counts_once (value control : LVec) :
    countWithDuplicateControl value control = countWithControl value control :=
  proof.duplicate_control_counts_once value control

#print axioms duplicate_control_counts_once

end Examples.systemVerilog.bitVectorQueries
