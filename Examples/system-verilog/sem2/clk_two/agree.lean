import LeanModels.Sv.Ingest2
import LeanModels.Sv.MultiClock

namespace Examples.«system-verilog».sem2.clk_two.agree

open LeanModels.Sv

load_design_sv2 clk_two from "Examples/system-verilog/sem2/clk_two/clk_two.sv.json"

#guard clk_two.sem.clockNames.length == 2
#guard clk_two.sem.multiClockReport.isNone

private def instant (rises : List String) (clk1 clk2 d : Logic) : ClockInstant :=
  { rises, inputs := [("clk1", LVec.ofLogic clk1), ("clk2", LVec.ofLogic clk2),
      ("d", LVec.ofLogic d)] }

-- Separate domains tick independently.
#guard (runMulti clk_two.sem σ_src 128 [
    instant ["clk1"] .l0 .l0 .l1,
    instant ["clk2"] .l0 .l1 .l1]).toOption.map
      (·.map fun st => (SvState.showSignal st "a", SvState.showSignal st "b")) ==
  some [("1", "x"), ("1", "1")]

-- Coincident edges commit together: b samples the old a.
#guard (runMulti clk_two.sem σ_src 128 [
    instant ["clk1", "clk2"] .l0 .l0 .l1]).toOption.map
      (·.map fun st => (SvState.showSignal st "a", SvState.showSignal st "b")) ==
  some [("1", "x")]

end Examples.«system-verilog».sem2.clk_two.agree
