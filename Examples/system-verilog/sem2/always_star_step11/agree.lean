/-
Step 11 source evidence for plain always @*. Retained extraction preserves
its ImplicitEventControl rather than replacing it by always_comb. E's frozen
process boundary stays loud; these are no execution witnesses.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.always_star_step11.agree

open LeanModels.Sv

load_design_sv2 alwaysStarStep11
  from "Examples/system-verilog/sem2/always_star_step11/always_star_step11.sv.json"

#guard alwaysStarStep11.pdesign.others == []
#guard match (alwaysStarStep11.sem 4).processes.toList with
  | [.unsupported "ProceduralBlockSymbol:Always" _, .alwaysComb _] => true
  | _ => false
#guard (alwaysStarStep11.sem 4).hasUnsupported

load_design_sv2 alwaysStarFunctionSensitivityStep11
  from "Examples/system-verilog/sem2/always_star_step11/always_star_function_sensitivity_step11.sv.json"

-- User function calls and implicit events stay source-shaped in the envelope
-- and loud at the frozen process/expression boundary; no inlining witness.
#guard (alwaysStarFunctionSensitivityStep11.sem 4).hasUnsupported

load_design_sv2 alwaysStarStartupStep11
  from "Examples/system-verilog/sem2/always_star_step11/always_star_startup_step11.sv.json"

#guard alwaysStarStartupStep11.pdesign.others == []
#guard (alwaysStarStartupStep11.sem 4).hasUnsupported

end Examples.«system-verilog».sem2.always_star_step11.agree
