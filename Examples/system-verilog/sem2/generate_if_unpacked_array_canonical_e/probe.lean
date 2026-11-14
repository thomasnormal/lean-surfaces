import LeanModels.Sv.Ingest2
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 generateIfUnpackedArray from
  "Examples/system-verilog/sem2/generate_if_unpacked_array_canonical_e/generate_if_unpacked_array_canonical_e.sv.json"

def kinds : CoreMemProc → String
  | .comb _ => "comb"
  | .edge _ => "edge"
  | .assign _ _ => "assign"
  | .initial _ => "initial"
  | .implicit _ => "implicit"
  | .unsupported k _ => k

#guard match generateIfUnpackedArray.e 2 with
  | .ok d => d.memories.size == 1 && d.processes.toList.map kinds ==
      ["assign", "assign"]
  | _ => false
#guard match generateIfUnpackedArray.e 1 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false
#guard match generateIfUnpackedArray.e 0 with
  | .ok d => d.memories.size == 0 && d.processes.isEmpty
  | _ => false
