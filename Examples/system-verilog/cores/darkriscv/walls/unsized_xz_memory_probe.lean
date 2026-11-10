import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

/-!
  Clean-room guard for the memory route's point-dependent unsized x/z
  conversion marker.  The extractor retains the literal's 32-bit payload;
  the route applies IEEE 1800-2023 §5.7.1 at the concrete destination width,
  including mixed payloads (`'hx0` and `'hz1`).
-/

set_option maxRecDepth 100000 in
load_design_sv2 unsized_xz_memory_wall
  from "Examples/system-verilog/cores/darkriscv/walls/unsized_xz_memory.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def stimulus (clk : Nat) : SvState :=
  [("clk", LVec.ofNat 1 clk)]

private structure Observed where
  qx : Option LVec
  qz : Option LVec
  qhx : Option LVec
  qhz : Option LVec
  qm : Option LVec

private def observed (st : SvState) : Observed :=
  { qx := SvState.lookup st "qx", qz := SvState.lookup st "qz",
    qhx := SvState.lookup st "qhx", qhz := SvState.lookup st "qhz",
    qm := SvState.lookup st "qm" }

private def xzTrace : Res (List Observed) :=
  match runMem2 (unsized_xz_memory_wall.pdesign.instantiateMemD2 [8]) 128
      [stimulus 0, stimulus 1] with
  | .ok states => .ok (states.map observed)
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout

#guard match unsized_xz_memory_wall.pdesign.instantiateMemD2 [8] with
  | { processes := [
      .assign "qm" (.ident "mem[0]"),
      .alwaysPlain "clk" (.block [
        .nbaAssign "qx" (.unsupported "ConversionExpression:unsized-xz" bx),
        .nbaAssign "qz" (.unsupported "ConversionExpression:unsized-xz" bz),
        .nbaAssign "qhx" (.unsupported "ConversionExpression:unsized-xz" hx),
        .nbaAssign "qhz" (.unsupported "ConversionExpression:unsized-xz" hz)])], .. } =>
      bx == "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" &&
      bz == "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz" &&
      hx == "xxxxxxxxxxxxxxxxxxxxxxxxxxxx0000" &&
      hz == "zzzzzzzzzzzzzzzzzzzzzzzzzzzz0001"
  | _ => false

#guard match xzTrace with
  | .ok [r0, r1] =>
      r0.qx == some (LVec.xVec 64) &&
      r0.qz == some (LVec.xVec 64) &&
      r0.qhx == some (LVec.xVec 64) &&
      r0.qhz == some (LVec.xVec 64) &&
      r0.qm == some (LVec.xVec 8) &&
      r1.qx == some (LVec.xVec 64) &&
      r1.qz == some (LVec.replicate 64 .lz) &&
      r1.qhx == some (LVec.lit
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx0000") &&
      r1.qhz == some (LVec.lit
        "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0001") &&
      r1.qm == some (LVec.xVec 8)
  | _ => false
