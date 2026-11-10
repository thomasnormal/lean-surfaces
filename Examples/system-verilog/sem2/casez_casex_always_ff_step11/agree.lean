/-
Step 11 clean-room evidence for casez and casex in `always_ff`.

The unchanged loaded CaseStmt nodes execute in E. The kernel checks all
Icarus/Xcelium rows, and R-EDGE covers every legal process-atomic schedule.
-/
import Examples.«system-verilog».sem2.case_always_ff_step11.agree

namespace Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

load_design_sv2 casezCasexAlwaysFfStep11
  from "Examples/system-verilog/sem2/casez_casex_always_ff_step11/casez_casex_always_ff_step11.sv.json"

local macro "normalize_wildcard_fixture" : tactic => `(tactic|
  simp only [casezCasexAlwaysFfStep11.sem,
    PDesign.instantiateGDAlias2, PDesign.instantiateGD2, PDesign.instantiateG2,
    PDesign.instantiate2, PDesign.instantiate2From,
    casezCasexAlwaysFfStep11.pdesign, expandList2, List.map, instProcess2,
    instStmt2, instStmts2, instItems2, instPats2, fitExpr2.eq_def, instExpr2,
    caseWidth2, List.foldl, selfWidth2, Design2.aliasGuard, Array.toList_map])

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

def wildcardEdge : Elab1 := fromAlwaysFF casezCasexAlwaysFfStep11.sem

#guard wildcardEdge.okB
#guard wildcardEdge.oneWriterB
#guard wildcardEdge.noEdgeB

theorem wildcard_profile : EdgeProfile wildcardEdge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold wildcardEdge fromAlwaysFF
    normalize_wildcard_fixture
    decide +kernel

theorem wildcard_all_schedules (ch : Choice) {s : Store}
    (hT : wildcardEdge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 wildcardEdge ch { store := s, active := [0], nba := [], k := k } c' ∧
      wildcardEdge.base.view c'.store =
        commitNba2 (wildcardEdge.base.view s) (wildcardEdge.queue s [0]) :=
  rEdge wildcard_profile ch hT (by decide) (by
    unfold wildcardEdge fromAlwaysFF
    normalize_wildcard_fixture
    decide +kernel) k

def wildcardInputs : List SvState :=
  [[("sel", .ofNat 4 0), ("d", .ofNat 4 9)],
   [("sel", .ofNat 4 1), ("d", .ofNat 4 8)],
   [("sel", ⟨#[.l1, .lz, .l0, .l0]⟩), ("d", .ofNat 4 7)],
   [("sel", ⟨#[.lz, .lx, .l1, .l0]⟩), ("d", .ofNat 4 6)],
   [("sel", ⟨#[.l0, .l0, .lx, .l1]⟩), ("d", .ofNat 4 5)],
   [("sel", ⟨#[.l1, .l1, .lz, .l1]⟩), ("d", .ofNat 4 4)],
   [("sel", ⟨#[.lz, .lz, .lz, .lz]⟩), ("d", .ofNat 4 3)],
   [("sel", ⟨#[.lx, .lx, .lx, .lx]⟩), ("d", .ofNat 4 2)],
   [("sel", ⟨#[.l0, .l0, .lx, .l1]⟩), ("d", ⟨#[.l1, .l0, .lz, .lx]⟩)],
   [("sel", ⟨#[.l1, .l1, .lz, .l1]⟩), ("d", ⟨#[.lz, .lz, .lz, .lz]⟩)],
   [("sel", .ofNat 4 8), ("d", ⟨#[.lx, .lx, .lx, .lx]⟩)],
   [("sel", ⟨#[.lz, .lz, .lz, .lz]⟩), ("d", .ofNat 4 10)]]

def wildcardNames : List String := ["qz", "qx"]

def wildcardSimulatorRows : List (List String) :=
  [["xxxx", "xxxx"], ["0011", "0110"], ["0010", "0101"],
   ["0010", "0101"], ["0001", "0100"], ["0101", "0101"],
   ["0100", "0100"], ["0011", "0011"], ["0011", "0010"],
   ["xz01", "xz01"], ["zzzz", "zzzz"], ["xxxx", "xxxx"], ["1010", "1010"]]

/-- Kernel computation checks startup, every original row, and the added
x/z data and overlapping-wildcard first-match rows against E. -/
theorem wildcard_agrees :
    (trace wildcardEdge wildcardNames (Config1.init wildcardEdge) wildcardInputs).map
      (showRow wildcardEdge wildcardNames (Config1.init wildcardEdge) :: ·) =
      some wildcardSimulatorRows := by
  unfold wildcardEdge fromAlwaysFF
  normalize_wildcard_fixture
  decide +kernel

#print axioms wildcard_profile
#print axioms wildcard_all_schedules
#print axioms wildcard_agrees

end Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree
