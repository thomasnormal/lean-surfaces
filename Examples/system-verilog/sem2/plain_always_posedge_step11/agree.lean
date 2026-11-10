/-
Step 11 clean-room evidence for a plain `always @(posedge clk)`.

The source kind is retained as `Process2.alwaysPlain`; this fixture records
its NBA-only profile. Source-oracle rows remain in the testbench, harness and
design note; the legacy cycle witness is retired. Source-preserving E
transport stays on its review branch.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile

namespace Examples.«system-verilog».sem2.plain_always_posedge_step11.agree

open LeanModels.Sv

load_design_sv2 plainAlwaysPosedgeStep11
  from "Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv.json"

#guard plainAlwaysPosedgeStep11.pdesign.others == []
#guard plainAlwaysPosedgeStep11.sem.ffOnlyProfileB == true
#guard match plainAlwaysPosedgeStep11.sem.processes.toList with
  | [.alwaysPlain "clk" (.block body)] => body.size == 2
  | _ => false

end Examples.«system-verilog».sem2.plain_always_posedge_step11.agree
