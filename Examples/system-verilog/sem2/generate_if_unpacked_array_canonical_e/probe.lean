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
  | .ok d => d.memories.size == 0 && d.processes.toList.map kinds ==
      ["GenerateDecl:UnpackedDecl", "assign", "assign"]
  | _ => false
