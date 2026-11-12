import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyMemE
namespace Examples.«system-verilog».sem2.param_mem_input_gen_e
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 paramMemInputGenE from
  "Examples/system-verilog/sem2/param_mem_input_gen_e/param_mem_input_gen_e.sv.json"
def design4 : Res MemEDesign := MemEDesign.ofGenerated paramMemInputGenE.pdesign [8, 4]
def design2 : Res MemEDesign := MemEDesign.ofGenerated paramMemInputGenE.pdesign [8, 2]
def stimuli : List SvState :=
  [[("clk", .ofNat 1 0), ("a[0]", .ofNat 8 0), ("a[1]", .ofNat 8 0)],
   [("clk", .ofNat 1 1), ("a[0]", .ofNat 8 0xa5), ("a[1]", .ofNat 8 0x3c)],
   [("clk", .ofNat 1 0), ("a[0]", .ofNat 8 0x5a), ("a[1]", .ofNat 8 0xc3)],
   [("clk", .ofNat 1 1), ("a[0]", .ofNat 8 0x5a), ("a[1]", .ofNat 8 0xc3)],
   [("clk", .ofNat 1 0), ("a[0]", .lit "xxxxxxxx"), ("a[1]", .lit "xxxxxxxx")]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do let s' ← d.step s row; let tail ← runRows d s' rest; .ok (s' :: tail)
 #guard match design4 with | .ok d => d.memDecls.length == 2 && d.processes.length == 5 | _ => false
 #guard match design2 with | .ok d => d.memDecls.length == 2 && d.processes.length == 3 | _ => false
#eval match design4 with
  | .ok d => match runRows d d.init stimuli with
    | .ok ss => ss.map (fun (s : MemEState) => SvState.showSignal s.scalar "q")
    | .error msg => ["ERROR:" ++ msg]
  | .timeout => ["ERROR:timeout"]
  | .unsupported msg => ["ERROR:" ++ msg]
end Examples.«system-verilog».sem2.param_mem_input_gen_e
