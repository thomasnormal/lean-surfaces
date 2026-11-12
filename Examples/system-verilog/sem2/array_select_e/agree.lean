import LeanModels.Sv.Ingest2

/-! Parser/elaboration boundary for a selected undeclared array name.
Slang retains its own diagnostics as Unsupported nodes; the loader refuses the
invalid source and no invented `ArraySel` declaration is introduced.
-/
namespace Examples.«system-verilog».sem2.array_select_e

open LeanModels.Sv

load_design_sv2 arraySelectE from
  "Examples/system-verilog/sem2/array_select_e/array_select_e.sv.json"

#guard arraySelectE.pdesign.others ==
  [("SlangError:UndeclaredIdentifier", "array_select_e.sv:2: use of undeclared identifier 'missing'")]
#guard match arraySelectE.pdesign.processes with
  | [.unsupported "ContinuousAssignSymbol:InvalidExpression" _] => true
  | _ => false
#guard match arraySelectE.pdesign.decls with
  | [_, _] => true
  | _ => false

end Examples.«system-verilog».sem2.array_select_e
