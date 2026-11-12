import LeanModels.Sv.Ingest2

/-! Clean-room refusal for a dynamic unpacked-array read.

The parameter-dependent dimension keeps the parser's source-shaped `ArraySel`
node.  The current ordinary E loader has no canonical memory state at this
entry point, so it refuses the declaration instead of flattening the array.
-/
namespace Examples.«system-verilog».sem2.array_index_e

open LeanModels.Sv

load_design_sv2 arrayIndexE from
  "Examples/system-verilog/sem2/array_index_e/array_index_e.sv.json"

#guard arrayIndexE.pdesign.others == []
#guard match arrayIndexE.pdesign.processes with
  | [.alwaysComb (.blockingAssign "y" (.arrayElem "values" [(.ident "i")]))] => true
  | _ => false

end Examples.«system-verilog».sem2.array_index_e
