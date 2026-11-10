/-
Step 11 clean-room evidence for a dynamic packed bit-select NBA target.

The semantic tier retains the parser's select target as `Lhs2.index` and its
legacy cycle runner already exercises the IEEE no-op behavior for x/z and
out-of-range indices.  E-core-1 intentionally requires a static NBA window;
the final guards pin that boundary without changing a shared Kernel file.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Edge

namespace Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 dynamicNbaTargetStep11
  from "Examples/system-verilog/sem2/dynamic_nba_target_step11/dynamic_nba_target_step11.sv.json"

private def stimulus (idx d en : String) : SvState :=
  [("clk", LVec.ofNat 1 1), ("idx", LVec.lit idx),
   ("d", LVec.lit d), ("en", LVec.lit en)]

private def trace : Res (List SvState) :=
  run2 dynamicNbaTargetStep11.sem σ_src 256 [
    stimulus "xxx" "x" "x",
    stimulus "000" "1" "1",
    stimulus "011" "0" "1",
    stimulus "x0x" "1" "1",
    stimulus "z01" "0" "1",
    stimulus "100" "1" "1",
    stimulus "001" "0" "0"]

#guard match dynamicNbaTargetStep11.sem.processes.toList with
  | [.alwaysFF "clk" (.block #[.ifStmt (.ident "en")
      (.nbaAssign (.index "q" (.ident "idx") 1) (.ident "d")) none])] => true
  | _ => false
#guard !dynamicNbaTargetStep11.sem.hasUnsupported

#guard match trace with
  | .ok [s0, s1, s2, s3, s4, s5, s6] =>
      SvState.showSignal s0 "q" == "xxxx" &&
      SvState.showSignal s1 "q" == "xxx1" &&
      SvState.showSignal s2 "q" == "0xx1" &&
      SvState.showSignal s3 "q" == "0xx1" &&
      SvState.showSignal s4 "q" == "0xx1" &&
      SvState.showSignal s5 "q" == "0xx1" &&
      SvState.showSignal s6 "q" == "0xx1"
  | _ => false

private def edgeBody : Stmt2 :=
  match dynamicNbaTargetStep11.sem.processes[0]? with
  | some (LeanModels.Sv.Process2.alwaysFF _ body) => body
  | _ => .unsupported "fixture" "unexpected process"

private def edge : Elab1 :=
  { decls := dynamicNbaTargetStep11.sem.decls
    procs := #[{ clk := "clk", rstn := none, body := edgeBody }] }

-- E-core-1's static-window contract is the deliberate current boundary.
#guard edge.okB == false
#guard match edge.procs[0]? with
  | some f => f.body.ffOkB edge.design == false
  | _ => false

end Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree
