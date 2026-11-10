import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».seq_mem.gen_members.proof

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 genmemIf from
  "Examples/system-verilog/seq_mem/gen_members/genmem_if.sv.json"
load_design_sv2 genmemFor from
  "Examples/system-verilog/seq_mem/gen_members/genmem_for.sv.json"

private def ifD : MemDesign2 := genmemIf.pdesign.instantiateMemD2 [4]
private def forD : MemDesign2 := genmemFor.pdesign.instantiateMemD2 [4]

-- Generate members are expanded only into source-shaped processes; the
-- unpacked declarations remain one memory state each.
#guard ifD.memDecls.length == 1
#guard ifD.processes.length == 1
#guard forD.memDecls.length == 2
#guard forD.processes.length == 5
#guard match ifD.processes with
  | [.assign "q" (.arrayElem "mem" [.int 0])] => true
  | _ => false
#guard match forD.processes with
  | [.assign "q" (.arrayElem "tap" [.int 0]),
     .assignL (.arrayElem "tap" [.int 0]) (.arrayElem "mem" [.int 0]),
     .assignL (.arrayElem "tap" [.int 1]) (.arrayElem "mem" [.int 1]),
     .assignL (.arrayElem "tap" [.int 2]) (.arrayElem "mem" [.int 2]),
     .assignL (.arrayElem "tap" [.int 3]) (.arrayElem "mem" [.int 3])] => true
  | _ => false

end Examples.«system-verilog».seq_mem.gen_members.proof
