import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for nested source-shaped generate expansion.

`GenerateIf` selects the parameter point and the nested `GenerateFor` copies
its original edge process once per genvar value. The copied process still uses
`PStmt`/`PLhs` and native `MemState`; no cell declarations or `Process2`
lowering are introduced.
-/
namespace Examples.«system-verilog».sem2.generate_memory_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 generateMemoryCanonical
  from "Examples/system-verilog/sem2/generate_memory_canonical_e/generate_memory_canonical_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 1)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 1)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 3)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3)]]

def outputs (w n : Int) : Res (List String) := do
  let d ← PDesign.instantiateCoreMem generateMemoryCanonical.pdesign [w, n]
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match PDesign.instantiateCoreMem generateMemoryCanonical.pdesign [4, 2] with
  | .ok d => d.memories.size == 1 && d.processes.size == 3 &&
      match d.processes[1]? with
      | some (CoreMemProc.edge p) =>
          match p.body with
          | .nbaAssignL (.arrayElem "s" [(.int 0)]) _ => true
          | _ => false
      | _ => false
  | _ => false

#guard match outputs 4 2 with
  | .ok [s0, s1, s2, s3] =>
      s0 == "xxxx" && s1 == "0001" && s2 == "0001" && s3 == "0011"
  | _ => false

#guard match outputs 4 1 with
  | .ok [s0, s1, s2, s3] =>
      s0 == "xxxx" && s1 == "0001" && s2 == "0001" && s3 == "0011"
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.generate_memory_canonical_e
