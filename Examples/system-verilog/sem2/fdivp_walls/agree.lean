import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
namespace Examples.«system-verilog».sem2.fdivp_walls
open LeanModels.Sv
set_option maxRecDepth 100000 in
load_design_sv2 fdivpGenerate from "Examples/system-verilog/sem2/fdivp_walls/fdivp_generate_localdecl.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 fdivpLargePow from "Examples/system-verilog/sem2/fdivp_walls/fdivp_large_pow.sv.json"

def unsupportedKinds (ps : Array Process2) : Array String :=
  ps.toList.filterMap (fun p => match p with | .unsupported k _ => some k | _ => none) |>.toArray

#guard match fdivpGenerate.pdesign.instantiate2 [8] 100 with
  | .ok d => unsupportedKinds d.processes ==
      #["GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign",
        "GenerateDecl:LocalParam", "GenerateDecl:Var", "GenerateDecl:Var", "Assign", "Assign"]
  | _ => false

#guard match fdivpLargePow.pdesign.instantiate2 [8193] 100 with
  | .ok d => unsupportedKinds d.processes == #[]
  | _ => false
end Examples.«system-verilog».sem2.fdivp_walls
