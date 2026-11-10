/-
Step 11 clean-room evidence for casez and casex in `always_ff`.

The semantic tier retains both parser-shaped CaseStmt nodes and the legacy
cycle witness matches the four-state oracle.  E-core-1's edge executor still
keeps case bodies at its explicit 12.5 boundary; this file does not alter the
shared Kernel definitions.
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

private def stimulus (sel d : String) : SvState :=
  [("clk", LVec.ofNat 1 1), ("sel", LVec.lit sel), ("d", LVec.lit d)]

private def trace : Res (List SvState) :=
  run2 casezCasexAlwaysFfStep11.sem σ_src 256 [
    stimulus "0000" "1001",
    stimulus "0001" "1000",
    stimulus "00z1" "0111",
    stimulus "01xz" "0110",
    stimulus "1x00" "0101",
    stimulus "1z11" "0100",
    stimulus "zzzz" "0011",
    stimulus "xxxx" "0010"]

#guard match trace with
  | .ok [s0, s1, s2, s3, s4, s5, s6, s7] =>
      SvState.showSignal s0 "qz" == "0011" && SvState.showSignal s0 "qx" == "0110" &&
      SvState.showSignal s1 "qz" == "0010" && SvState.showSignal s1 "qx" == "0101" &&
      SvState.showSignal s2 "qz" == "0010" && SvState.showSignal s2 "qx" == "0101" &&
      SvState.showSignal s3 "qz" == "0001" && SvState.showSignal s3 "qx" == "0100" &&
      SvState.showSignal s4 "qz" == "0101" && SvState.showSignal s4 "qx" == "0101" &&
      SvState.showSignal s5 "qz" == "0100" && SvState.showSignal s5 "qx" == "0100" &&
      SvState.showSignal s6 "qz" == "0011" && SvState.showSignal s6 "qx" == "0011" &&
      SvState.showSignal s7 "qz" == "0011" && SvState.showSignal s7 "qx" == "0010"
  | _ => false

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
