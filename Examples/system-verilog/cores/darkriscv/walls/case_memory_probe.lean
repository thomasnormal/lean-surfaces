import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

/-!
  Clean-room guard for a normal `case` selecting a one-rank unpacked memory
  cell.  The source-shaped `Case`/`ArraySel` nodes are retained by the parser;
  the memory route executes the first matching arm, queues the selected NBA,
  and publishes the cell through the continuous assignment.  Normal case
  matching follows IEEE 1800-2023 §12.5.1.
-/

set_option maxRecDepth 100000 in
load_design_sv2 dark_case_memory_wall
  from "Examples/system-verilog/cores/darkriscv/walls/case_memory.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def stimulus (clk : Nat) (sel : Nat) (d : Nat) : SvState :=
  [("clk", LVec.ofNat 1 clk), ("sel", LVec.ofNat 2 sel),
   ("d", LVec.ofNat 8 d)]

private def observed (st : SvState) : Option Nat :=
  (SvState.lookup st "q").bind LVec.toNat?

private def caseTrace : Res (List (Option Nat)) :=
  match runMem2 (dark_case_memory_wall.pdesign.instantiateMemD2 [1]) 64
      [ stimulus 0 0 0,
        stimulus 1 0 0x3C,
        stimulus 0 0 0x3C,
        stimulus 1 1 0,
        stimulus 0 1 0,
        stimulus 1 2 0,
        stimulus 0 2 0,
        stimulus 1 3 0,
        stimulus 0 3 0 ] with
  | .ok states => .ok (states.map observed)
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout

#guard match (dark_case_memory_wall.pdesign.instantiateMemD2 [1]).processes with
  | [.alwaysPlain "clk" (.block [
      .caseStmt (.ident "sel") _ _ .normal .none]),
      .assign "q" (.arrayElem "mem" [.int 0])] => true
  | _ => false

#guard caseTrace == .ok [
  none,
  some 0x3C,
  some 0x3C,
  some 0xA5,
  some 0xA5,
  some 0x5A,
  some 0x5A,
  some 0x5A,
  some 0x5A]
