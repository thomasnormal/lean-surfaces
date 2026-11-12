import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
import LeanModels.Sv.Kernel.Core0Entry

/-! Clean-room E memory witness for a one-rank unpacked register file.

The parser keeps `cpuregs` as one source declaration.  `MemEDesign` gives it a
native `MemState`; run-time reads and writes use the sampled index, and an
unknown index produces the IEEE x/no-update result instead of a flattened
constant cell. -/

namespace Examples.«system-verilog».sem2.unpacked_cpuregs_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 cpuregsE
  from "Examples/system-verilog/sem2/unpacked_cpuregs_e/unpacked_cpuregs_e.sv.json"

private def canonical : Res MemoryElab :=
  LeanModels.Sv.Kernel.PDesign.instantiateMemoryE cpuregsE.pdesign [32]

private def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 0),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 0),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.lit "xxxxx"),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.lit "zzzzz"),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.lit "xxxxx"), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.lit "xxxxx"), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 7),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.lit "x")],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 7),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.lit "x")],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 7),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 0)]]

private def runRows (d : MemEDesign) (s : MemEState) :
    List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

private def output (s : MemEState) : Option LVec :=
  SvState.lookup s.scalar "rdata"

private def outputs : Except String (List (Option LVec)) :=
  match canonical with
  | .ok e =>
      match e.memoryInitial with
      | .ok initial =>
          match runRows e.memory initial stimuli with
          | .ok ss => .ok (ss.map output)
          | .error e => .error e
      | .error e => .error e
  | .timeout => .error "memory design elaboration timed out"
  | .unsupported e => .error e

private def x32 : LVec := LVec.xVec 32
private def a5 : LVec := LVec.ofNat 32 0xa5
private def z5 : LVec := LVec.ofNat 32 0x5a

#guard match canonical with
  | .ok e => e.memory.memDecls.length == 1 && e.memory.processes.length == 2 &&
      e.memory.memDecls.all (fun (p : PDecl) => p.name == "cpuregs")
  | _ => false

#guard match outputs with
  | .ok [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10] =>
      s0 == some x32 && s1 == some x32 && s2 == some a5 &&
      s3 == some x32 && s4 == some x32 && s5 == some a5 &&
      s6 == some a5 && s7 == some a5 && s8 == some z5 &&
      s9 == some z5 && s10 == some z5
  | _ => false

end Examples.«system-verilog».sem2.unpacked_cpuregs_e
