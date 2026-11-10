/-
Step 11 clean-room evidence for plain `case` in `always_ff`.

The parser-shaped Design2 view retains two CaseStmt nodes under one edge body;
the E-core-1 edge executor still refuses this construct at its explicit
12.5 boundary.  This file records the source shape only; it does not add a
run2 meaning or claim an E execution.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.case_always_ff_step11.agree

load_design_sv2 case_always_ff_step11
  from "Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv.json"

#guard case_always_ff_step11.pdesign.others == []
#guard !case_always_ff_step11.sem.hasUnsupported
#guard match case_always_ff_step11.sem.processes.toList with
  | [LeanModels.Sv.Process2.alwaysFF "clk" (.block body)] => body.size == 2
  | _ => false

end Examples.«system-verilog».sem2.case_always_ff_step11.agree
