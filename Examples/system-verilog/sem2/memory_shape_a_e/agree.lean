import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMem1

/-! Canonical E receipt for a source-shaped parameterized shift register.

`PStmt.forLoop` remains in the retained process.  The two points below use
one native `MemState` each; the storage is never expanded into declarations.
The final row drives an all-x run-time index, exercising the LRM all-x read.
-/
namespace Examples.«system-verilog».sem2.memory_shape_a_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeA
  from "Examples/system-verilog/sem2/memory_shape_a_e/memory_shape_a_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 1), ("idx", LVec.ofNat 5 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 2), ("idx", LVec.ofNat 5 0)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 3), ("idx", LVec.ofNat 5 1)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 4), ("idx", LVec.ofNat 5 1)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 5), ("idx", LVec.lit "xxxxx")],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 6), ("idx", LVec.ofNat 5 2)]]

def runAt (w p : Int) : Res (List MemState1) := do
  let d ← PDesign.instantiateMemCore1 memoryShapeA.pdesign [w, p]
  runMemCore1Rows d d.initial stimulus

def out (d : MemElab1) (s : MemState1) : String × String :=
  (SvState.showSignal (MemState1.view d s) "q", SvState.showSignal (MemState1.view d s) "selected")

def outputs (w p : Int) : Res (List (String × String)) := do
  let d ← PDesign.instantiateMemCore1 memoryShapeA.pdesign [w, p]
  let rows ← runMemCore1Rows d d.initial stimulus
  .ok (rows.map (out d))

#guard match PDesign.instantiateMemCore1 memoryShapeA.pdesign [4, 3] with
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

end Examples.«system-verilog».sem2.memory_shape_a_e
