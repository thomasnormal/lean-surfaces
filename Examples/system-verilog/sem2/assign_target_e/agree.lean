import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.ArrayFast
namespace Examples.«system-verilog».sem2.assign_target_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 assignTargetE from
  "Examples/system-verilog/sem2/assign_target_e/assign_target_e.sv.json"
#guard assignTargetE.pdesign.others == []
#guard match assignTargetE.sem.processes.toList with
  | [.assign (.ident "missing") (.ident "x"), .assign (.ident "y") (.ident "x")] => true
  | _ => false

/-! The ordinary canonical route now completes the eight empty-input cycles
used by the real-block census; this guard is also the bounded performance
regression for the function-valued scalar store. -/
def eightRows : Res (List CoreMemState) := do
  let d ← assignTargetE.e
  runCoreMemRows d d.initial [[], [], [], [], [], [], [], []]

#guard match eightRows with
  | .ok rows => rows.length == 8
  | _ => false

/-! The scalar projection is also executable by the direct flat-array
instrument.  This is a bounded performance receipt, not a replacement for the
canonical `CoreMemDesign` route: the latter remains authoritative for memory
designs. -/
def fastEightRows : Res (List FastConfig) := do
  let d ← assignTargetE.e
  fastRun d.scalar σ_src 1000 [[], [], [], [], [], [], [], []]

#guard match fastEightRows with
  | .ok rows => rows.length == 8
  | _ => false
end Examples.«system-verilog».sem2.assign_target_e
