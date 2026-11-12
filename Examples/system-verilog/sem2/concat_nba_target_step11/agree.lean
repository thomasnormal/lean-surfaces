/-
Canonical E-core-1 receipt for a source-shaped packed concatenation NBA.
The two windows are static and disjoint, so `Lhs2.edgeWindows` places both
pieces of one sampled RHS in the NBA queue; no target is lowered or split in
the source envelope.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Obs
import Examples.«system-verilog».sem2.case_always_ff_step11.agree

namespace Examples.«system-verilog».sem2.concat_nba_target_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

load_design_sv2 concatNbaTargetStep11
  from "Examples/system-verilog/sem2/concat_nba_target_step11/concat_nba_target_step11.sv.json"

local macro "normalize_concat_fixture" : tactic => `(tactic|
  simp only [concatNbaTargetStep11.sem,
    PDesign.instantiateGDAlias2, PDesign.instantiateGD2, PDesign.instantiateG2,
    PDesign.instantiate2, PDesign.instantiate2From,
    concatNbaTargetStep11.pdesign, expandList2,
    List.map, instProcess2, instStmt2, instStmts2, instItems2, instPats2,
    fitExpr2.eq_def, instExpr2, caseWidth2, List.foldl, selfWidth2,
    Design2.aliasGuard, Array.toList_map])

#guard concatNbaTargetStep11.pdesign.others == []
#guard !concatNbaTargetStep11.sem.hasUnsupported
#guard match concatNbaTargetStep11.sem.processes.toList with
  | [LeanModels.Sv.Process2.alwaysFF "clk" (.block #[.nbaAssign
      (.concat [.slice "q" 4 4, .slice "q" 0 4]) (.ident "d")]) ] => true
  | _ => false

def edge : Elab1 := fromAlwaysFF concatNbaTargetStep11.sem

#guard edge.procs.size == 1
#guard edge.okB && edge.oneWriterB && edge.noEdgeB

theorem profile : EdgeProfile edge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold edge fromAlwaysFF
    normalize_concat_fixture
    decide +kernel

theorem all_schedules (ch : Choice) {s : Store}
    (hT : edge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 edge ch { store := s, active := [0], nba := [], k := k } c' ∧
      edge.base.view c'.store = commitNba2 (edge.base.view s) (edge.queue s [0]) :=
  rEdge profile ch hT (by decide) (by
    unfold edge fromAlwaysFF
    normalize_concat_fixture
    decide +kernel) k

def names : List String := ["q"]
def inputs : List SvState :=
  [[("clk", .ofNat 1 0), ("d", .ofNat 8 165)],
   [("clk", .ofNat 1 1)],
   [("clk", .ofNat 1 0), ("d", .ofNat 8 60)],
   [("clk", .ofNat 1 1)],
   [("clk", .ofNat 1 0), ("d", .lit "x101zz01")],
   [("clk", .ofNat 1 1)]]

def simulatorRows : List (List String) :=
  [["xxxxxxxx"], ["xxxxxxxx"], ["10100101"], ["10100101"],
   ["00111100"], ["00111100"], ["x101zz01"]]

def trace : Config1 → List SvState → Option (List (List String))
  | _, [] => some []
  | c, entry :: rest => do
      let c' ← close edge c entry
      let rows ← trace c' rest
      pure (showRow edge names c' :: rows)

theorem agrees :
    (trace (Config1.init edge) inputs).map
      (showRow edge names (Config1.init edge) :: ·) = some simulatorRows := by
  unfold edge fromAlwaysFF trace close showRow names inputs simulatorRows
  normalize_concat_fixture
  native_decide

#print axioms profile
#print axioms all_schedules
#print axioms agrees

end Examples.«system-verilog».sem2.concat_nba_target_step11.agree
