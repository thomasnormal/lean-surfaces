import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».sem2.unsized_xz_ternary_mem.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 unsizedXZTernaryMem
  from "Examples/system-verilog/sem2/unsized_xz_ternary_mem/unsized_xz_ternary_mem.sv.json"

private def sourceValue : PExpr :=
  match unsizedXZTernaryMem.pdesign.processes with
  | [.assign _ value, .assign _ _] => value
  | _ => .unsupported "fixture" "unexpected process shape"

private def markerPayload : String :=
  match sourceValue with
  | .ternary _ (.unsupported "ConversionExpression:unsized-xz" payload) _ => payload
  | _ => ""

#guard markerPayload == "zzzzzzzzzzzzzzzzzzzzzzzzzzzz0001"
#guard unsizedXZ2 none markerPayload ==
  .unsupported "ConversionExpression:unsized-xz"
    "unsized x/z conversion has no destination width"
#guard unsizedXZ2 (some 8) "not-a-binary-literal" ==
  .unsupported "ConversionExpression:unsized-xz"
    "unsized x/z conversion has an invalid payload"

private def memAt (n : Int) : MemDesign2 :=
  unsizedXZTernaryMem.pdesign.instantiateMemD2 [n]

#guard (memAt 40).memDecls.length == 1
#guard (memAt 8).memDecls.length == 1

private def concreteValue (n : Nat) : Expr2 :=
  instExpr2 (memAt n).env (memAt n).elems (some n) sourceValue

#guard match concreteValue 40 with
  | .ternary (.ident "a") (.lit v) (.resize 40 (.lit z)) =>
      v == LVec.lit "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0001" &&
      z == LVec.ofNat 32 0
  | _ => false

#guard match concreteValue 8 with
  | .ternary (.ident "a") (.lit v) (.resize 8 (.lit z)) =>
      v == LVec.lit "zzzz0001" && z == LVec.ofNat 32 0
  | _ => false

private def stimulus (a : String) : SvState :=
  [("a", LVec.lit a), ("clk", LVec.ofNat 1 1)]

private def trace (n : Int) : Res (List SvState) :=
  runMem2 (memAt n) 128 [stimulus "1", stimulus "0", stimulus "x"]

#guard match trace 40 with
  | .ok [r1, r0, rx] =>
      SvState.lookup r1 "y" == some (LVec.lit
        "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0001") &&
      SvState.lookup r0 "y" == some (LVec.ofNat 40 0) &&
      SvState.lookup rx "y" == some (LVec.lit
        "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx000x") &&
      SvState.lookup r1 "mem_q" == some (LVec.xVec 40) &&
      SvState.lookup r0 "mem_q" == some (LVec.xVec 40) &&
      SvState.lookup rx "mem_q" == some (LVec.xVec 40)
  | _ => false

#guard match trace 8 with
  | .ok [r1, r0, rx] =>
      SvState.lookup r1 "y" == some (LVec.lit "zzzz0001") &&
      SvState.lookup r0 "y" == some (LVec.ofNat 8 0) &&
      SvState.lookup rx "y" == some (LVec.lit "xxxx000x") &&
      SvState.lookup r1 "mem_q" == some (LVec.xVec 8) &&
      SvState.lookup r0 "mem_q" == some (LVec.xVec 8) &&
      SvState.lookup rx "mem_q" == some (LVec.xVec 8)
  | _ => false

end Examples.«system-verilog».sem2.unsized_xz_ternary_mem.agree
