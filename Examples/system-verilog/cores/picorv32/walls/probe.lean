import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.HierarchyCoreMem

/-!
Current ordinary-route probes for the PicoRV32 memory walls.  `load_design_sv2`
now exposes the canonical source-shaped memory family through `.sem` (and
`.e`); this file deliberately does not call the retired scalar or side-route
memory elaborators.  In particular, the hierarchy shape is checked through
the same user-facing family that the real-design loader uses, so a crash is
never mistaken for a refusal.
-/

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 unpacked_cpuregs_wall
  from "Examples/system-verilog/cores/picorv32/walls/unpacked_cpuregs.sv.json"

/-! PicoRV32's one-rank `cpuregs` is admitted as one native memory. -/
#guard match unpacked_cpuregs_wall.sem 32 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false
#guard match unpacked_cpuregs_wall.e 32 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false

/-! The canonical time-zero settle now completes for the pinned parameter
point; the remaining performance wall is in later empty-input cycles. -/
#guard match unpacked_cpuregs_wall.e 32 with
  | .ok d => match d.initialState with | .ok _ => true | _ => false
  | _ => false

set_option maxRecDepth 100000 in
load_design_sv2 net_z_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/net_z_memory.sv.json"

#guard match net_z_memory_wall.sem 4 with
  | .ok d => d.memories.size == 1 && d.processes.size == 1
  | _ => false
#guard net_z_memory_wall.pdesign.others ==
  [("NetSymbol:net-z", "pcpi_mul_wr")]
#guard net_z_memory_wall.pdesign.netMetadata ==
  [{ name := "pcpi_mul_wr", width := 1, netKind := "Wire", signed := false,
     fourState := true, isNet := true, driverReason := some "no driver: the net reads z" }]

set_option maxRecDepth 100000 in
load_design_sv2 task_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/task_memory.sv.json"

#guard match task_memory_wall.sem 4 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false
#guard task_memory_wall.pdesign.others ==
  [("SubroutineSymbol:empty-task", "task empty_statement;\n    begin end\n  endtask")]

set_option maxRecDepth 100000 in
load_design_sv2 task_memory_comments_wall
  from "Examples/system-verilog/cores/picorv32/walls/task_memory_comments.sv.json"

/-! A nonempty task marker remains a loud module-member refusal. -/
#guard match task_memory_comments_wall.sem 4 with
  | .unsupported _ => true
  | _ => false

set_option maxRecDepth 100000 in
load_design_sv2 xz_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/xz_memory.sv.json"

#guard xz_memory_wall.pdesign.others ==
  [("IntegerLiteral:unsized-xz-parametric", "'bx")]
#guard match xz_memory_wall.sem 32 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false

set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeB
  from "Examples/system-verilog/sem2/memory_shape_b_canonical_e/memory_shape_b_canonical_e.sv.json"

/-! Shape (b) uses the ordinary hierarchy-memory family.  This guard is the
Lean side of the simulator oracle and remains bounded, so a hierarchy bug is
reported as a failed check rather than a process crash. -/
#guard match memoryShapeB.sem 4 3 with
  | .ok d => d.memories.size == 1 && d.processes.size == 5
  | _ => false
