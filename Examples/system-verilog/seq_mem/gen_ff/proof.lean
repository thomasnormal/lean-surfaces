import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».seq_mem.gen_ff.proof

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 genMemory from
  "Examples/system-verilog/seq_mem/gen_ff/gen_ff.sv.json"

private def memD : MemDesign2 := genMemory.pdesign.instantiateMemD2 [8, 4]

-- Four source genvar processes are retained as four memory writers; the
-- unpacked declaration remains one source-shaped memory state.
#guard memD.memDecls.length == 1
#guard memD.processes.length == 5
#guard match runMem2 memD 64
    [[("clk", .ofNat 1 0), ("d", .ofNat 8 3)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 17)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 34)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "xxxxxxxx" &&
      SvState.showSignal s1 "q" == "00010001" &&
      SvState.showSignal s2 "q" == "00010001"
  | _ => false

end Examples.«system-verilog».seq_mem.gen_ff.proof
