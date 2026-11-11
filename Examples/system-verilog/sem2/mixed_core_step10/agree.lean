/-
Step 10 source evidence for a mixed E slot: two source-shaped `always_comb`
processes sit beside one NBA-only `always_ff`. The fixture deliberately keeps
this at the parser/profile boundary; no mixed E executor is claimed here.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile

namespace Examples.«system-verilog».sem2.mixed_core_step10.agree

open LeanModels.Sv

load_design_sv2 mixedCoreStep10
  from "Examples/system-verilog/sem2/mixed_core_step10/mixed_core_step10.sv.json"

#guard mixedCoreStep10.pdesign.others == []
#guard !mixedCoreStep10.sem.hasUnsupported
#guard mixedCoreStep10.sem.ffMixedProfileB == true
#guard mixedCoreStep10.sem.ffOnlyProfileB == false
#guard mixedCoreStep10.sem.processes.size == 3
#guard match mixedCoreStep10.sem.processes.toList with
  | [.alwaysComb _, .alwaysComb _, .alwaysFF "clk" _] => true
  | _ => false

end Examples.«system-verilog».sem2.mixed_core_step10.agree
