import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.unpacked_array_target_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 unpackedArrayTarget from
  "Examples/system-verilog/sem2/unpacked_array_target_canonical_e/unpacked_array_target_canonical_e.sv.json"

/-! The source-shaped select is retained as `PLhs.arrayElem`; the executor
resolves its run-time index against the native one-rank `MemState` (§7.4.6,
§11.5.1, IEEE 1800-2023). -/
#guard unpackedArrayTarget.pdesign.processes.any fun p => match p with
  | .alwaysComb (.block (.blockingAssignL (.arrayElem "slot" [(.ident "idx")]) (.ident "x") ::
      .blockingAssign "y" (.arrayElem "slot" [(.ident "idx")]) :: [])) => true
  | _ => false

def stimulus : List SvState :=
  [[("x", LVec.ofNat 8 0), ("idx", LVec.ofNat 1 0)],
   [("x", LVec.ofNat 8 0xa5), ("idx", LVec.ofNat 1 1)],
   [("x", LVec.ofNat 8 0x3c), ("idx", LVec.ofNat 1 0)],
   [("x", LVec.lit "xxxxxxxx"), ("idx", LVec.ofNat 1 1)],
   [("x", LVec.ofNat 8 0x5a), ("idx", LVec.lit "x")],
   [("x", LVec.lit "zzzzzzzz"), ("idx", LVec.ofNat 1 0)],
   [("x", LVec.ofNat 8 0x96), ("idx", LVec.lit "z")],
   [("x", LVec.ofNat 8 0x0f), ("idx", LVec.ofNat 1 1)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem unpackedArrayTarget.pdesign []
  let initial ← d.initialState
  let initialY := SvState.showSignal (CoreMemState.view d initial) "y"
  let rows ← runCoreMemRows d initial stimulus
  .ok (initialY :: rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard match outputs with
  | .ok ["xxxxxxxx", "00000000", "10100101", "00111100", "xxxxxxxx",
      "xxxxxxxx", "zzzzzzzz", "xxxxxxxx", "00001111"] => true
  | _ => false

end Examples.«system-verilog».sem2.unpacked_array_target_canonical_e
