import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for a source-shaped time-zero memory initializer.

The initializer is retained as an `Initial` node and executes before the first
cycle sample.  Its conditional loop and direct cell write use the existing
`MemState`; no cell expansion or second memory meaning is introduced.
-/
namespace Examples.«system-verilog».sem2.memory_initial_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryInitial
  from "Examples/system-verilog/sem2/memory_initial_canonical_e/memory_initial_canonical_e.sv.json"

def stimulus : List SvState :=
  [[("idx", LVec.ofNat 2 0)],
   [("idx", LVec.ofNat 2 1)],
   [("idx", LVec.lit "xx")]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem memoryInitial.pdesign [8, 3, 1]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match PDesign.instantiateCoreMem memoryInitial.pdesign [8, 3, 1] with
  | .ok d => d.memories.size == 1 && d.processes.size == 2 &&
      match d.processes[0]? with
      | some (CoreMemProc.initial (.block [(.ifStmt _ _ none), (.blockingAssignL (.arrayElem "s" [_]) _)])) => true
      | _ => false
  | _ => false

#guard match outputs with
  | .ok ["10100101", "00000000", "xxxxxxxx"] => true
  | _ => false

end Examples.«system-verilog».sem2.memory_initial_canonical_e
