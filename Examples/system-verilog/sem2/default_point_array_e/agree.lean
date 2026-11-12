import LeanModels.Sv.Ingest2

/-! Clean-room first-wall receipt for a fixed unpacked array in an edge process.
The symbolic extractor expands the fixed default-point cells, but the retained
loop target remains unsupported and the ordinary E runner stops at the explicit
edge-process boundary.  No clocked or memory behavior is approximated here.
-/
namespace Examples.«system-verilog».sem2.default_point_array_e

open LeanModels.Sv

load_design_sv2 defaultPointArrayE from
  "Examples/system-verilog/sem2/default_point_array_e/default_point_array_e.sv.json"

#guard defaultPointArrayE.pdesign.others == []
#guard match defaultPointArrayE.sem.processes.toList with
  | [.alwaysFF "clk" (.block #[.nbaAssign (.ident "pipe[0]") (.ident "d"),
      .unsupported "AssignmentExpression:target" _]),
      .assign (.ident "q") (.ident "pipe[3]")] => true
  | _ => false

end Examples.«system-verilog».sem2.default_point_array_e
