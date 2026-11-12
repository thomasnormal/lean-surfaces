import LeanModels.Sv.Ingest2

/-! Source-shaped automatic functions stay as declaration and call nodes.  The
current E rung retains the parser node and refuses at instantiation until its
straight-line body evaluator is connected; it never accepts Slang's erased
inline form. -/

namespace Examples.«system-verilog».sem2.symbolic_inline_function

open LeanModels.Sv

load_design_sv2 symbolicInlineFunction
  from "Examples/system-verilog/sem2/symbolic_inline_function/symbolic_inline_function.sv.json"

#guard symbolicInlineFunction.pdesign.functions.length == 2

#guard match symbolicInlineFunction.pdesign.functions with
  | [id, bump] => id.name == "id" && bump.name == "bump" &&
      bump.formals.length == 1
  | _ => false

#guard match symbolicInlineFunction.pdesign.processes with
  | [.assign "y" (.functionCall "id" [.ident "a"]),
     .assign "z" (.functionCall "bump" [.ident "a"])] => true
  | _ => false

end Examples.«system-verilog».sem2.symbolic_inline_function
