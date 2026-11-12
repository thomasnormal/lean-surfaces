import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.fixed_mem_local_loop_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 fixedMemLocalLoopE from
  "Examples/system-verilog/sem2/fixed_mem_local_loop_e/fixed_mem_local_loop_e.sv.json"
def design8 : Res MemEDesign := MemEDesign.ofPDesign fixedMemLocalLoopE.pdesign [8]
def design4 : Res MemEDesign := MemEDesign.ofPDesign fixedMemLocalLoopE.pdesign [4]
def stimuli8 : List SvState :=
  [[("clk", .ofNat 1 0), ("d", .ofNat 8 0), ("idx", .ofNat 2 0)],
   [("clk", .ofNat 1 1), ("d", .ofNat 8 0xa5), ("idx", .ofNat 2 1)],
   [("clk", .ofNat 1 0), ("d", .ofNat 8 0x5a), ("idx", .ofNat 2 1)],
   [("clk", .ofNat 1 1), ("d", .ofNat 8 0x5a), ("idx", .lit "xx")],
   [("clk", .ofNat 1 0), ("d", .lit "xxxxxxxx"), ("idx", .lit "xx")]]
def stimuli4 : List SvState :=
  [[("clk", .ofNat 1 0), ("d", .ofNat 4 0), ("idx", .ofNat 2 0)],
   [("clk", .ofNat 1 1), ("d", .ofNat 4 0xa), ("idx", .ofNat 2 1)],
   [("clk", .ofNat 1 0), ("d", .ofNat 4 0x5), ("idx", .ofNat 2 1)],
   [("clk", .ofNat 1 1), ("d", .ofNat 4 0x5), ("idx", .lit "xx")],
   [("clk", .ofNat 1 0), ("d", .lit "xxxx"), ("idx", .lit "xx")]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do let s' ← d.step s row; let tail ← runRows d s' rest; .ok (s' :: tail)
#guard match design8 with | .ok d => d.memDecls.length == 1 && d.processes.length == 2 | _ => false
#guard match design4 with | .ok d => d.memDecls.length == 1 && d.processes.length == 2 | _ => false
#eval match design8 with
  | .ok d => match runRows d d.init stimuli8 with
    | .ok ss => ss.map (fun (s : MemEState) => SvState.showSignal s.scalar "q")
    | .error msg => ["ERROR:" ++ msg]
  | .timeout => ["ERROR:timeout"]
  | .unsupported msg => ["ERROR:" ++ msg]
end Examples.«system-verilog».sem2.fixed_mem_local_loop_e
