import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.packed_shift_register_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 packedShiftRegisterCanonicalE from
  "Examples/system-verilog/sem2/packed_shift_register_canonical_e/packed_shift_register_canonical_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 1)],
   [("clk", LVec.lit "x"), ("v", LVec.lit "x")],
   [("clk", LVec.ofNat 1 0), ("v", LVec.lit "z")],
   [("clk", LVec.ofNat 1 1), ("v", LVec.lit "z")]]

def outputs (n : Int) : Res (List String) := do
  let d ← PDesign.instantiateE2 packedShiftRegisterCanonicalE.pdesign [n]
  let states ← runCoreMemRows d d.initial stimulus
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match outputs 4 with
  | .ok ["xxxx", "xxx1", "xxx1", "xx10", "xx10", "x101", "x101", "x101", "101z"] => true
  | _ => false

#guard match outputs 8 with
  | .ok ["xxxxxxxx", "xxxxxxx1", "xxxxxxx1", "xxxxxx10", "xxxxxx10",
      "xxxxx101", "xxxxx101", "xxxxx101", "xxxx101z"] => true
  | _ => false

end Examples.«system-verilog».sem2.packed_shift_register_canonical_e
