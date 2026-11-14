import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.parameterized_size_cast_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 parameterizedSizeCastCanonicalE from
  "Examples/system-verilog/sem2/parameterized_size_cast_canonical_e/parameterized_size_cast_canonical_e.sv.json"

def stimulus : List SvState :=
  [[("x", LVec.ofNat 8 0)],
   [("x", LVec.ofNat 8 0xa5)],
   [("x", LVec.ofNat 8 0x3c)],
   [("x", LVec.lit "xxxxxxxx")],
   [("x", LVec.lit "zzzzzzzz")],
   [("x", LVec.lit "10x1z0x1")]]

def outputs (w : Int) : Res (List String) := do
  let d ← PDesign.instantiateE2 parameterizedSizeCastCanonicalE.pdesign [w]
  let states ← runCoreMemRows d d.initial stimulus
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard match outputs 2 with
  | .ok ["00", "01", "00", "xx", "zz", "x1"] => true
  | _ => false

#guard match outputs 12 with
  | .ok ["000000000000", "000010100101", "000000111100", "0000xxxxxxxx",
      "0000zzzzzzzz", "000010x1z0x1"] => true
  | _ => false

end Examples.«system-verilog».sem2.parameterized_size_cast_canonical_e
