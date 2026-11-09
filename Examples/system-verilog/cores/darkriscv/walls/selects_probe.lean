import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

/-!
  Clean-room guard for declared-signal bit- and part-selects on the memory
  route.  The expressions stay in the parser's `PartSel`/`BitSel` nodes; the
  guard checks both their retained source shape and the cycle trace.  The
  selected windows follow IEEE 1800-2023 §11.5.1 (part-selects) and §11.5.2
  (bit-selects), including the live value sampled after the NBA edge.
-/

set_option maxRecDepth 100000 in
load_design_sv2 dark_selects_wall
  from "Examples/system-verilog/cores/darkriscv/walls/selects.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def stimulus (clk : Nat) (d : Nat) (i : Nat) : SvState :=
  [("clk", LVec.ofNat 1 clk), ("d", LVec.ofNat 32 d), ("i", LVec.ofNat 5 i)]

private def selected (st : SvState) : Option Nat × Option Nat × Option Nat :=
  ((SvState.lookup st "q").bind LVec.toNat?,
   (SvState.lookup st "b").bind LVec.toNat?,
   (SvState.lookup st "r").bind LVec.toNat?)

private def selectTrace : Res (List (Option Nat × Option Nat × Option Nat)) :=
  match runMem2 (dark_selects_wall.pdesign.instantiateMemD2 []) 64
      [ stimulus 0 0 0,
        stimulus 1 0xA5A55A5A 3,
        stimulus 0 0xA5A55A5A 3,
        stimulus 1 0xA5A55A5A 3,
        stimulus 0 0xA5A55A5A 3,
        stimulus 1 0x12345678 31,
        stimulus 0 0x12345678 31,
        stimulus 1 0x12345678 31,
        stimulus 0 0x12345678 31] with
  | .ok states => .ok (states.map selected)
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout

#guard match (dark_selects_wall.pdesign.instantiateMemD2 []).processes with
  | [.alwaysPlain "clk" (.nbaAssign "r" (.ident "d")),
      .assign "q" (.partSel (.ident "r") (.int 7) (.int 0)),
      .assign "b" (.bitSel (.ident "r") (.ident "i"))] => true
  | _ => false

#guard selectTrace == .ok [
  (none, none, none),
  (some 0x5A, some 1, some 0xA5A55A5A),
  (some 0x5A, some 1, some 0xA5A55A5A),
  (some 0x5A, some 1, some 0xA5A55A5A),
  (some 0x5A, some 1, some 0xA5A55A5A),
  (some 0x78, some 0, some 0x12345678),
  (some 0x78, some 0, some 0x12345678),
  (some 0x78, some 0, some 0x12345678),
  (some 0x78, some 0, some 0x12345678)]
