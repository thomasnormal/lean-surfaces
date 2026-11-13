import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for a source-shaped parameterized shift register.

The retained `PStmt.forLoop` runs against the existing `MemState`; its cells
are never expanded into scalar declarations and the scalar store stays the
canonical E-core-1 `Store`.
-/
namespace Examples.«system-verilog».sem2.memory_shape_a_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeA
  from "Examples/system-verilog/sem2/memory_shape_a_canonical_e/memory_shape_a_canonical_e.sv.json"

#check memoryShapeA.e

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 1), ("idx", LVec.ofNat 5 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 2), ("idx", LVec.ofNat 5 0)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 3), ("idx", LVec.ofNat 5 1)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 4), ("idx", LVec.ofNat 5 1)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 5), ("idx", LVec.lit "xxxxx")],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 6), ("idx", LVec.ofNat 5 2)]]

def outputs (w p : Int) : Res (List (String × String)) := do
  let d ← PDesign.instantiateCoreMem memoryShapeA.pdesign [w, p]
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "q",
     SvState.showSignal (CoreMemState.view d s) "selected"))

#guard match PDesign.instantiateCoreMem memoryShapeA.pdesign [4, 3] with
  | .ok d => d.memories.size == 1 && d.processes.size == 3 &&
      match d.processes[0]? with
      | some proc => match proc with
        | .edge p => match p.body with
          | .block [(.forLoop ..), (.nbaAssignL (.arrayElem "s" [_]) _)] => true
          | _ => false
        | _ => false
      | _ => false
  | _ => false

#guard match outputs 4 3 with
  | .ok rows => rows ==
      [("xxxx", "xxxx"), ("xxxx", "0010"), ("xxxx", "xxxx"),
       ("xxxx", "0010"), ("xxxx", "xxxx"), ("0010", "0010")]
  | _ => false

#guard match outputs 8 5 with
  | .ok rows => rows ==
      [("xxxxxxxx", "xxxxxxxx"), ("xxxxxxxx", "00000010"),
       ("xxxxxxxx", "xxxxxxxx"), ("xxxxxxxx", "00000010"),
       ("xxxxxxxx", "xxxxxxxx"), ("xxxxxxxx", "00000010")]
  | _ => false

end Examples.«system-verilog».sem2.memory_shape_a_canonical_e
