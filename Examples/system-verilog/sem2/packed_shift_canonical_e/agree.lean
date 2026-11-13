import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.packed_shift_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 packedShiftCanonical from
  "Examples/system-verilog/sem2/packed_shift_canonical_e/packed_shift_canonical_e.sv.json"
def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 1)]]
def outputs (n : Int) : Res (List String) := do
  let d ← PDesign.instantiateCoreMem packedShiftCanonical.pdesign [n]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard match outputs 4 with | .ok ["xxxx", "xxx1", "xxx1", "xx11"] => true | _ => false
#guard match outputs 8 with | .ok ["xxxxxxxx", "xxxxxxx1", "xxxxxxx1", "xxxxxx11"] => true | _ => false
end Examples.«system-verilog».sem2.packed_shift_canonical_e
