import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! MemE receipt for a fixed one-rank unpacked memory with a run-time
procedural loop index.  The `for (int i ...)` stays source-shaped, and the
NBA queue samples every `s[i-1]` from the pre-edge memory before one commit. -/
namespace Examples.«system-verilog».sem2.memory_shape_d_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeD
  from "Examples/system-verilog/sem2/memory_shape_d_e/memory_shape_d_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0), ("idx", LVec.ofNat 2 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 1), ("idx", LVec.ofNat 2 0)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 2), ("idx", LVec.ofNat 2 1)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 2), ("idx", LVec.ofNat 2 1)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 4), ("idx", LVec.ofNat 2 3)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 4), ("idx", LVec.ofNat 2 3)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 4), ("idx", LVec.lit "xx")]]

def design : Res MemEDesign :=
  MemEDesign.ofPDesign memoryShapeD.pdesign [4]

def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

def outputs : Except String (List (String × String)) := do
  let d ← match design with
    | .ok d => .ok d
    | .timeout => .error "E memory admission timed out"
    | .unsupported msg => .error msg
  let rows ← runRows d d.init stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal s.scalar "q",
     SvState.showSignal s.scalar "selected"))

end Examples.«system-verilog».sem2.memory_shape_d_e
