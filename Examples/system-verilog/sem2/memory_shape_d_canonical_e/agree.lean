import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical E receipt for fixed one-rank unpacked storage with a retained
loop-local index.  The source `for (int i...)` remains a runtime loop and all
indexed NBAs commit through the existing `MemState`/`MemNbaQueue`. -/
namespace Examples.«system-verilog».sem2.memory_shape_d_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeD
  from "Examples/system-verilog/sem2/memory_shape_d_canonical_e/memory_shape_d_canonical_e.sv.json"

def stimulus (w : Nat) : List SvState :=
   [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat w 0), ("idx", LVec.ofNat 2 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat w 1), ("idx", LVec.ofNat 2 0)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat w 2), ("idx", LVec.lit "xx")]]

def outputs (w : Int) : Res (List (String × String)) := do
  let d ← PDesign.instantiateCoreMem memoryShapeD.pdesign [w]
  let rows ← runCoreMemRows d d.initial (stimulus w.toNat)
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "q",
     SvState.showSignal (CoreMemState.view d s) "selected"))

#guard match PDesign.instantiateCoreMem memoryShapeD.pdesign [4] with
  | .ok d => d.memories.size == 1 && d.processes.size == 3
  | _ => false

#guard match outputs 4 with
  | .ok rows => rows ==
      [("xxxx", "xxxx"), ("xxxx", "0001"), ("xxxx", "xxxx")]
  | _ => false
end Examples.«system-verilog».sem2.memory_shape_d_canonical_e
