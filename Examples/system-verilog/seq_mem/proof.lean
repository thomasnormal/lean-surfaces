import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_mem.proof

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 asyncMem from
  "Examples/system-verilog/seq_mem/async_mem_fifo.sv.json"

-- The declaration and both source selects stay structural in the envelope.
#guard (asyncMem.pdesign.decls.filter fun d => !d.unpackedDims.isEmpty).length == 1
#guard (((asyncMem.pdesign.decls.filter fun d => !d.unpackedDims.isEmpty).head?).getD
    default).unpackedDims.length == 1

private def memD : MemDesign2 := asyncMem.pdesign.instantiateMemD2 [8, 4]

#guard memD.memDecls.length == 1
#guard memD.processes.length == 2

-- Reset writes one cell, the next edge writes d, and q observes that cell
-- through the continuous assignment.  The array is never expanded into
-- four default-point declarations.
#guard match runMem2 memD 64
    [[("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 8 3)],
     [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 8 17)],
     [("clk", .ofNat 1 0), ("rstn", .ofNat 1 1), ("d", .ofNat 8 34)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "00000000" &&
      SvState.showSignal s1 "q" == "00010001" &&
      SvState.showSignal s2 "q" == "00010001"
  | _ => false

end Examples.«system-verilog».seq_mem.proof
