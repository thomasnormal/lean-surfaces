import LeanModels.Sv.Ingest2

/-! Clean-room first-wall receipt for a looped edge update over fixed array cells.
The parser retains the edge process and leaves the indexed loop target loud;
ordinary E refuses the clocked process before assigning an invented loop or
memory meaning.
-/
namespace Examples.«system-verilog».sem2.for_loop_e

open LeanModels.Sv

load_design_sv2 forLoopE from
  "Examples/system-verilog/sem2/for_loop_e/for_loop_e.sv.json"

#guard forLoopE.pdesign.others == []
#guard match (forLoopE.sem).processes.toList with
  | [.alwaysFF "clk" (.block #[.unsupported "AssignmentExpression:target" _, _]),
      .assign (.ident "q") (.ident "values[3]")] => true
  | _ => false

end Examples.«system-verilog».sem2.for_loop_e
