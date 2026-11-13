import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.bit_select_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 bitSelectCanonical
  from "Examples/system-verilog/sem2/bit_select_canonical_e/bit_select_canonical_e.sv.json"

def stimuli : List SvState :=
  [[("d", LVec.ofNat 8 0xa5), ("idx", LVec.ofNat 3 3)],
   [("d", LVec.ofNat 8 0x5a), ("idx", LVec.ofNat 3 6)],
   [("d", LVec.lit "xxxxxxxx"), ("idx", LVec.ofNat 3 3)],
   [("d", LVec.ofNat 8 0xa5), ("idx", LVec.lit "xxx")],
   [("d", LVec.ofNat 8 0xa5), ("idx", LVec.lit "zzz")]]

def outputRow (stimulus : SvState) : Res (String × String) := do
  let d ← PDesign.instantiateCoreMem bitSelectCanonical.pdesign [8]
  let st ← d.step d.initial stimulus
  .ok (SvState.showSignal (CoreMemState.view d st) "q0",
       SvState.showSignal (CoreMemState.view d st) "qidx")

def outputs : Res (List (String × String)) := stimuli.mapM outputRow

#guard match PDesign.instantiateCoreMem bitSelectCanonical.pdesign [8] with
  | .ok d => d.elems.lookup "d" == some 1 && d.elems.lookup "idx" == some 1
  | _ => false

#guard match outputs with
  | .ok [("1", "0"), ("0", "1"), ("x", "x"), ("1", "x"), ("1", "x")] => true
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.bit_select_canonical_e
