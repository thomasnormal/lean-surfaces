/-
Step 11 clean-room evidence for casez and casex in `always_ff`.

The frontend retains both parser-shaped CaseStmt nodes. Source-oracle rows
remain recorded in the testbench, harness and design note; the legacy cycle
witness is retired. E-core-1's edge executor still keeps case bodies at its
explicit 12.5 boundary pending the reviewed native rule.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Edge

namespace Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 casezCasexAlwaysFfStep11
  from "Examples/system-verilog/sem2/casez_casex_always_ff_step11/casez_casex_always_ff_step11.sv.json"

private def hasCaseModes : Bool :=
  match casezCasexAlwaysFfStep11.sem.processes.toList with
  | [.alwaysFF _ (.block body)] =>
      match body[0]?, body[1]? with
      | some (LeanModels.Sv.Stmt2.caseStmt _ _ _ .casez _),
          some (LeanModels.Sv.Stmt2.caseStmt _ _ _ .casex _) => true
      | _, _ => false
  | _ => false

#guard casezCasexAlwaysFfStep11.pdesign.others == []
#guard !casezCasexAlwaysFfStep11.sem.hasUnsupported
#guard hasCaseModes

-- E-core-1 currently refuses all case bodies at the explicit 12.5 boundary.
private def edgeBody : Stmt2 :=
  match casezCasexAlwaysFfStep11.sem.processes[0]? with
  | some (LeanModels.Sv.Process2.alwaysFF _ body) => body
  | _ => .unsupported "fixture" "unexpected process"

private def edge : Elab1 :=
  { decls := casezCasexAlwaysFfStep11.sem.decls
    procs := #[{ clk := "clk", rstn := none, body := edgeBody }] }

#guard edge.okB == false
#guard edgeBody.ffOkB edge.design == false

end Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree
