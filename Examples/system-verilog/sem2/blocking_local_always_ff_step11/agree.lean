/-
Step 11 clean-room evidence for blocking assignments to a local temporary in
`always_ff`.  The loader retains the parser's LocalDecl and the assignments;
the current E edge fragment refuses scoped procedural storage before it can
execute the blocking local.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.blocking_local_always_ff_step11.agree

load_design_sv2 blocking_local_always_ff_step11
  from "Examples/system-verilog/sem2/blocking_local_always_ff_step11/blocking_local_always_ff_step11.sv.json"

#guard blocking_local_always_ff_step11.pdesign.others == []
#guard match blocking_local_always_ff_step11.sem.processes.toList with
  | [LeanModels.Sv.Process2.alwaysFF "clk" (.block body)] =>
      body.size == 5 &&
      match body[0]? with
      | some (LeanModels.Sv.Stmt2.unsupported "LocalDecl"
          "block-local declaration requires scoped procedural storage") => true
      | _ => false
  | _ => false
#guard blocking_local_always_ff_step11.sem.hasUnsupported

end Examples.«system-verilog».sem2.blocking_local_always_ff_step11.agree
