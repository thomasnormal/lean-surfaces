import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.param_mem_shift_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 paramMemShiftE from
  "Examples/system-verilog/sem2/param_mem_shift_e/param_mem_shift_e.sv.json"
def design : Res MemEDesign := MemEDesign.ofPDesign paramMemShiftE.pdesign [8,4]
def design2 : Res MemEDesign := MemEDesign.ofPDesign paramMemShiftE.pdesign [8,2]
def stimuli : List SvState :=
  [[("clk", .ofNat 1 0), ("d", .ofNat 8 0)],
   [("clk", .ofNat 1 1), ("d", .ofNat 8 0xa5)],
   [("clk", .ofNat 1 0), ("d", .ofNat 8 0x5a)],
   [("clk", .ofNat 1 1), ("d", .ofNat 8 0x5a)],
   [("clk", .ofNat 1 0), ("d", .lit "xxxxxxxx")]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do let s' ← d.step s row; let tail ← runRows d s' rest; .ok (s' :: tail)
#guard match design with | .ok d => d.memDecls.length == 1 && d.processes.length == 2 | _ => false
#guard match design2 with | .ok d => d.memDecls.length == 1 && d.processes.length == 2 | _ => false
#eval match design with
  | .ok d => match runRows d d.init stimuli with
    | .ok ss => ss.map (fun (s : MemEState) => SvState.showSignal s.scalar "q")
    | .error msg => ["ERROR:" ++ msg]
  | .timeout => ["ERROR:timeout"]
  | .unsupported msg => ["ERROR:" ++ msg]
end Examples.«system-verilog».sem2.param_mem_shift_e
