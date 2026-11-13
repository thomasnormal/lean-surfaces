import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for PicoRV32's one-rank register-file shape.

The source declaration stays one `MemShape`; run-time read and write indices
are evaluated against the native `MemState`, and the edge body keeps its
nonblocking queue.  This is the canonical-E executor route, not the retired
MemE profile and not a cell expansion.
-/

namespace Examples.«system-verilog».sem2.unpacked_cpuregs_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 cpuregsCanonical
  from "Examples/system-verilog/sem2/unpacked_cpuregs_canonical_e/unpacked_cpuregs_canonical_e.sv.json"

def stimuli : List SvState :=
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

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem cpuregsCanonical.pdesign [32]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "rdata")

#guard match PDesign.instantiateCoreMem cpuregsCanonical.pdesign [32] with
  | .ok d => d.memories.size == 1 && d.processes.size == 2 &&
      match d.memories[0]? with
      | some md => md.source.name == "cpuregs" && md.shape.elemWidth == 32
      | _ => false
  | _ => false

#guard match outputs with
  | .ok [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10] =>
      s0 == "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" &&
      s1 == "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" &&
      s2 == "00000000000000000000000010100101" &&
      s3 == "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" &&
      s4 == "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" &&
      s5 == "00000000000000000000000010100101" &&
      s6 == "00000000000000000000000010100101" &&
      s7 == "00000000000000000000000010100101" &&
      s8 == "00000000000000000000000001011010" &&
      s9 == "00000000000000000000000001011010" &&
      s10 == "00000000000000000000000001011010"
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.unpacked_cpuregs_canonical_e
