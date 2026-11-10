/-
Step 11 clean-room evidence for a plain `always @(posedge clk)`.

The source kind is retained as `Process2.alwaysPlain`; the NBA-only body is
eligible for the existing edge profile.  This fixture records the profile and
four-state trace without changing the shared E Kernel.
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

private def stimulus (en d : String) : SvState :=
  [("clk", LVec.ofNat 1 1), ("en", LVec.lit en), ("d", LVec.lit d)]

private def trace : Res (List SvState) :=
  run2 plainAlwaysPosedgeStep11.sem σ_src 256 [
    stimulus "0" "1001",
    stimulus "1" "0110",
    stimulus "x" "0011",
    stimulus "z" "zzzz",
    stimulus "1" "xz01"]

#guard match trace with
  | .ok [s0, s1, s2, s3, s4] =>
      SvState.showSignal s0 "q" == "1010" && SvState.showSignal s0 "q_copy" == "1001" &&
      SvState.showSignal s1 "q" == "0110" && SvState.showSignal s1 "q_copy" == "0110" &&
      SvState.showSignal s2 "q" == "1010" && SvState.showSignal s2 "q_copy" == "0011" &&
      SvState.showSignal s3 "q" == "1010" && SvState.showSignal s3 "q_copy" == "zzzz" &&
      SvState.showSignal s4 "q" == "xz01" && SvState.showSignal s4 "q_copy" == "xz01"
  | _ => false

end Examples.«system-verilog».sem2.plain_always_posedge_step11.agree
