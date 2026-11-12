import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.packed_rhs_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 packedRhsE from "Examples/system-verilog/sem2/packed_rhs_e/packed_rhs_e.sv.json"
def design8 : Res MemEDesign := MemEDesign.ofPDesign packedRhsE.pdesign [8]
def design4 : Res MemEDesign := MemEDesign.ofPDesign packedRhsE.pdesign [4]
def stimuli : List SvState :=
  [[("clk", .ofNat 1 0), ("v", .ofNat 1 0)],
   [("clk", .ofNat 1 1), ("v", .ofNat 1 1)],
   [("clk", .ofNat 1 0), ("v", .ofNat 1 0)],
   [("clk", .ofNat 1 1), ("v", .ofNat 1 1)],
   [("clk", .ofNat 1 0), ("v", .lit "x")]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do let s' ← d.step s row; let tail ← runRows d s' rest; .ok (s' :: tail)
#guard match design8 with | .ok d => d.decls.any (·.name == "t") && d.processes.length == 2 | _ => false
#guard match design4 with | .ok d => d.decls.any (·.name == "t") && d.processes.length == 2 | _ => false
#eval match design8 with
  | .ok d => match runRows d d.init stimuli with
    | .ok ss => ss.map (fun (s : MemEState) => SvState.showSignal s.scalar "q")
    | .error msg => ["ERROR:" ++ msg]
  | .timeout => ["ERROR:timeout"]
  | .unsupported msg => ["ERROR:" ++ msg]
end Examples.«system-verilog».sem2.packed_rhs_e
