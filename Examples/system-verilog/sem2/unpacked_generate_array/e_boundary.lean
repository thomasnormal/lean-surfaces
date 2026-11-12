import LeanModels.Sv.Ingest2

/-! Ordinary E boundary for a parameter-dependent unpacked array.
The source-shaped declaration is valid and remains in the envelope, but the
ordinary scalar E entry refuses its storage before executing the continuous
cell assignments.  The separate canonical-memory receipt is not used here.
-/
namespace Examples.«system-verilog».sem2.unpacked_generate_array.e_boundary

open LeanModels.Sv

load_design_sv2 unpackedGenerateArrayE from
  "Examples/system-verilog/sem2/unpacked_generate_array/unpacked_generate_array.sv.json"

#guard match (unpackedGenerateArrayE.sem 8 2).processes.toList with
  | [.unsupported "Instantiate" msg] => msg == "decl 'stage': unpacked array storage outside E (UnpackedDecl:memory)"
  | _ => false

end Examples.«system-verilog».sem2.unpacked_generate_array.e_boundary
