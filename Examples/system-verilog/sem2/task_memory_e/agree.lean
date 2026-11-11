import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! Clean-room E receipt for a referenced empty input-only task. -/

namespace Examples.«system-verilog».sem2.task_memory_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 taskMemoryE
  from "Examples/system-verilog/sem2/task_memory_e/task_memory_e.sv.json"

private def design : Res MemEDesign :=
  MemEDesign.ofPDesign taskMemoryE.pdesign [4]

private def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 0xa5)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0xa5)]]

private def runRows (d : MemEDesign) (s : MemEState) :
    List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

private def outputs : Except String (List (Option LVec)) :=
  match design with
  | .ok d =>
      match runRows d d.init stimuli with
      | .ok ss => .ok (ss.map fun s => SvState.lookup s.scalar "q")
      | .error e => .error e
  | .timeout => .error "memory design elaboration timed out"
  | .unsupported e => .error e

#guard taskMemoryE.pdesign.others ==
  [("SubroutineSymbol:empty-task", "task empty_statement;\n    begin end\n  endtask")]

#guard !memEAllowedOther ("SubroutineSymbol:Subroutine", "task nonempty")

#guard match design with
  | .ok d =>
      d.others == taskMemoryE.pdesign.others &&
      d.memDecls.length == 1 && d.processes.length == 2
  | .timeout => false
  | .unsupported _ => false

#guard match outputs with
  | .ok [q0, q1, q2] =>
      q0 == some (LVec.xVec 8) &&
      q1 == some (LVec.ofNat 8 0xa5) &&
      q2 == some (LVec.ofNat 8 0xa5)
  | _ => false

end Examples.«system-verilog».sem2.task_memory_e
