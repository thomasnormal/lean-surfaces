/-
Step 11 clean-room evidence for a dynamic packed bit-select NBA target.

The frontend retains the parser's select target as `Lhs2.index`. Source-oracle
rows remain recorded in the testbench, harness and design note; the legacy
cycle witness is retired. E-core-1 currently requires a static NBA window;
the final guards retain that boundary pending the reviewed native rule.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Edge

namespace Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 dynamicNbaTargetStep11
  from "Examples/system-verilog/sem2/dynamic_nba_target_step11/dynamic_nba_target_step11.sv.json"

#guard match dynamicNbaTargetStep11.sem.processes.toList with
  | [.alwaysFF "clk" (.block #[.ifStmt (.ident "en")
      (.nbaAssign (.index "q" (.ident "idx") 1) (.ident "d")) none])] => true
  | _ => false
#guard !dynamicNbaTargetStep11.sem.hasUnsupported

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
