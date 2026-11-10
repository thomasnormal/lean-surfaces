/-
Source regression for the narrow edge elaborator. Async-reset Process2 has
already lost the original always style and reset iff in the legacy loader.
It must not enter E through the source-preserving single-event packet.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Elab

namespace Examples.«system-verilog».sem2.plain_always_posedge_step11.reset_boundary

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 resetMetadata
  from "Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_reset_metadata_step11.sv.json"

-- Test the loaded source, without pinning the loader's metadata loss as an
-- expected Process2 shape. A later faithful/loud loader fix is compatible.
#guard match Elab1.ofEdgeDesign2 resetMetadata.sem with
  | .error _ => true
  | .ok _ => false

-- Both reset polarities are outside this narrow transport, even with a body
-- that is otherwise fully admitted. E's manually constructed reset rule stays.
#guard match FF.ofProcess2 (.alwaysFFR "clk" "rn" (.block #[]) false) with
  | .error msg => msg.startsWith "9.4.2:" | .ok _ => false
#guard match FF.ofProcess2 (.alwaysFFR "clk" "rp" (.block #[]) true) with
  | .error msg => msg.startsWith "9.4.2:" | .ok _ => false

end Examples.«system-verilog».sem2.plain_always_posedge_step11.reset_boundary
