import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! Clean-room E receipt for a source-shaped plain `always @*` memory read.
The parser keeps the implicit event and runtime ArraySel.  E wakes the body
only when the selected cell or the index expression changes. -/
namespace Examples.«system-verilog».sem2.always_star_memory_read_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 alwaysStarMemoryReadE
  from "Examples/system-verilog/sem2/always_star_memory_read_e/always_star_memory_read_e.sv.json"

#guard alwaysStarMemoryReadE.pdesign.others == []
#guard match alwaysStarMemoryReadE.pdesign.processes with
  | [.alwaysFF "clk" _, .alwaysImplicit (.block [
      .blockingAssign "q" (.arrayElem "mem" [LeanModels.Sv.PExpr.ident "ridx"])])] => true
  | _ => false

private def design : Res MemEDesign :=
  MemEDesign.ofPDesign alwaysStarMemoryReadE.pdesign [4]

private def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 0),
    ("widx", LVec.ofNat 2 0), ("ridx", LVec.ofNat 2 0), ("d", LVec.ofNat 8 0)],
   [("clk", LVec.ofNat 1 1), ("we", LVec.ofNat 1 1),
    ("widx", LVec.ofNat 2 2), ("ridx", LVec.ofNat 2 0), ("d", LVec.ofNat 8 0xa5)],
   [("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 1),
    ("widx", LVec.ofNat 2 2), ("ridx", LVec.ofNat 2 2), ("d", LVec.ofNat 8 0xa5)],
   [("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 1),
    ("widx", LVec.ofNat 2 1), ("ridx", LVec.ofNat 2 1), ("d", LVec.ofNat 8 0x3c)],
   [("clk", LVec.ofNat 1 1), ("we", LVec.ofNat 1 1),
    ("widx", LVec.ofNat 2 1), ("ridx", LVec.ofNat 2 1), ("d", LVec.ofNat 8 0x3c)],
   [("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 0),
    ("widx", LVec.ofNat 2 1), ("ridx", LVec.ofNat 2 1), ("d", LVec.ofNat 8 0x3c)],
   [("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 0),
    ("widx", LVec.ofNat 2 1), ("ridx", LVec.lit "xx"), ("d", LVec.ofNat 8 0x3c)],
   [("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 0),
    ("widx", LVec.ofNat 2 1), ("ridx", LVec.lit "zz"), ("d", LVec.ofNat 8 0x3c)],
   [("clk", LVec.ofNat 1 0), ("we", LVec.ofNat 1 0),
    ("widx", LVec.ofNat 2 1), ("ridx", LVec.ofNat 2 3), ("d", LVec.ofNat 8 0x3c)]]

private def runRows (d : MemEDesign) (s : MemEState) :
    List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

private def outputs : Except String (List (Option LVec)) :=
  match design with
  | .ok d =>
      match runRows d d.init stimuli with
      | .ok ss => .ok (ss.map fun s => SvState.lookup s.scalar "q")
      | .error e => .error e
  | .timeout => .error "memory E elaboration timed out"
  | .unsupported e => .error e

#guard match design with
  | .ok d => d.memDecls.length == 1 && d.processes.length == 2
  | _ => false

#guard match outputs with
  | .ok [
      q0, q1, q2, q3, q4, q5, q6, q7, q8] =>
      q0 == some (LVec.xVec 8) &&
      q1 == some (LVec.xVec 8) &&
      q2 == some (LVec.ofNat 8 0xa5) &&
      q3 == some (LVec.xVec 8) &&
      q4 == some (LVec.ofNat 8 0x3c) &&
      q5 == some (LVec.ofNat 8 0x3c) &&
      q6 == some (LVec.xVec 8) &&
      q7 == some (LVec.xVec 8) &&
      q8 == some (LVec.xVec 8)
  | _ => false

end Examples.«system-verilog».sem2.always_star_memory_read_e
