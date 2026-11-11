import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! The first Carnot memory wall through E.  The retained unpacked declaration,
the source `ArraySel` target and the cell read all stay in the envelope; this
receipt does not use the provisional MemCycle route. -/

namespace Examples.«system-verilog».sem2.async_mem_fifo_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 asyncMem from
  "Examples/system-verilog/seq_mem/async_mem_fifo.sv.json"

private def design : Res MemEDesign :=
  MemEDesign.ofPDesign asyncMem.pdesign [8, 4]

private def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

#guard match design with
  | .ok d => d.memDecls.length == 1 && d.processes.length == 2
  | _ => false

#guard match design with
  | .ok d =>
      match runRows d d.init
        [[("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 0), ("d", LVec.ofNat 8 3)],
         [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
         [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
         [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)],
         [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)]] with
      | .ok [s0, s1, s2, s3, s4] =>
          SvState.lookup s0.scalar "q" == some (LVec.ofNat 8 0) &&
          SvState.lookup s1.scalar "q" == some (LVec.ofNat 8 0) &&
          SvState.lookup s2.scalar "q" == some (LVec.ofNat 8 17) &&
          SvState.lookup s3.scalar "q" == some (LVec.ofNat 8 17) &&
          SvState.lookup s4.scalar "q" == some (LVec.ofNat 8 34)
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.async_mem_fifo_e
