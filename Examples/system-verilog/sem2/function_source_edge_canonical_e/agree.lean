import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.function_source_edge_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 functionSourceEdge from
  "Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv.json"
def stimuli : List SvState := [
  [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 1 0)],
  [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 1 0)],
  [("clk", LVec.ofNat 1 0), ("d", LVec.lit "x")],
  [("clk", LVec.ofNat 1 1), ("d", LVec.lit "x")],
  [("clk", LVec.ofNat 1 0), ("d", LVec.lit "z")],
  [("clk", LVec.ofNat 1 1), ("d", LVec.lit "z")],
  [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 1 1)],
  [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 1 1)]
]
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem functionSourceEdge.pdesign []
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard functionSourceEdge.pdesign.functions.any (fun f => f.name == "invert")
#guard match functionSourceEdge.pdesign.functions.find? (fun f => f.name == "invert") with
  | some f => f.automatic && f.formals.all (fun formal => formal.isInput)
  | none => false
#guard match functionSourceEdge.pdesign.processes with
  | [.alwaysFF "clk" (.nbaAssign "q" (.functionCall "invert" [_]))] => true
  | _ => false
#guard match outputs with
  | .ok ["x", "1", "1", "x", "x", "x", "x", "0"] => true
  | _ => false
end Examples.«system-verilog».sem2.function_source_edge_canonical_e
