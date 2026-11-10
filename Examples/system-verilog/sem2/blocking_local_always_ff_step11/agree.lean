/-
Step 11 clean-room evidence for blocking assignments to a local temporary in
`always_ff`.  The loader retains the parser's LocalDecl and the assignments;
the envelope now retains block scope, resolved lifetime and symbolic local
types. The current E edge fragment refuses scoped procedural storage before it can
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

load_design_sv2 static_local_lifetime_step11
  from "Examples/system-verilog/sem2/blocking_local_always_ff_step11/static_local_lifetime_step11.sv.json"

-- Source metadata is retained, but storage is not silently made module-global.
#guard static_local_lifetime_step11.pdesign.others == []
#guard (static_local_lifetime_step11.sem 4).hasUnsupported
#guard (static_local_lifetime_step11.sem 4).decls.size == 9

end Examples.«system-verilog».sem2.blocking_local_always_ff_step11.agree
