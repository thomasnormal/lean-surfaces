import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_mem.more_proof

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 defaultArray from
  "Examples/system-verilog/seq_mem/default_array/default_array.sv.json"
load_design_sv2 rangeFf from
  "Examples/system-verilog/seq_mem/range_ff/range_ff.sv.json"
load_design_sv2 rangePlain from
  "Examples/system-verilog/seq_mem/range_plain/range_plain.sv.json"

private def defaultD : MemDesign2 := defaultArray.pdesign.instantiateMemD2 [8, 4]
private def rangeFfD : MemDesign2 := rangeFf.pdesign.instantiateMemD2 [8, 4]
private def rangePlainD : MemDesign2 := rangePlain.pdesign.instantiateMemD2 [8, 4]

#guard defaultD.memDecls.length == 1
#guard rangeFfD.memDecls.length == 1
#guard rangePlainD.memDecls.length == 1

-- Plain `always` and the C-style [N] spelling retain the source-shaped cell.
#guard match runMem2 defaultD 64
    [[("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 8 3)],
     [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 8 17)],
     [("clk", .ofNat 1 0), ("rstn", .ofNat 1 1), ("d", .ofNat 8 34)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "00000000" &&
      SvState.showSignal s1 "q" == "00010001" &&
      SvState.showSignal s2 "q" == "00010001"
  | _ => false

-- Both edge styles and the [0:N-1] spelling work without an async reset.
#guard match runMem2 rangeFfD 64
    [[("clk", .ofNat 1 0), ("d", .ofNat 8 3)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 17)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 34)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "xxxxxxxx" &&
      SvState.showSignal s1 "q" == "00010001" &&
      SvState.showSignal s2 "q" == "00010001"
  | _ => false

#guard match runMem2 rangePlainD 64
    [[("clk", .ofNat 1 0), ("d", .ofNat 8 3)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 17)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 34)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "xxxxxxxx" &&
      SvState.showSignal s1 "q" == "00010001" &&
      SvState.showSignal s2 "q" == "00010001"
  | _ => false

end Examples.«system-verilog».seq_mem.more_proof
