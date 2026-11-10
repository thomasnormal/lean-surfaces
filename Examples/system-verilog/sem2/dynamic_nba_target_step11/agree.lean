/-
Step 11: source-shaped dynamic packed NBA targets execute in E.
The source nodes are retained; queue offsets and RHS values are sampled at
issue time, with kernel-checked traces and universal process-atomic schedules.
-/
import Examples.«system-verilog».sem2.plain_always_posedge_step11.agree

namespace Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree
open Examples.«system-verilog».sem2.plain_always_posedge_step11.agree

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

load_design_sv2 dynamicNbaTargetStep11
  from "Examples/system-verilog/sem2/dynamic_nba_target_step11/dynamic_nba_target_step11.sv.json"
load_design_sv2 dynamicNbaIssueStep11
  from "Examples/system-verilog/sem2/dynamic_nba_target_step11/dynamic_nba_issue_step11.sv.json"

local macro "normalize_dynamic_fixture" : tactic => `(tactic|
  simp only [dynamicNbaTargetStep11.sem, dynamicNbaIssueStep11.sem,
    PDesign.instantiateGDAlias2, PDesign.instantiateGD2, PDesign.instantiateG2,
    PDesign.instantiate2, PDesign.instantiate2From,
    dynamicNbaTargetStep11.pdesign, dynamicNbaIssueStep11.pdesign, expandList2,
    List.map, instProcess2, instStmt2, instStmts2, instItems2, instPats2,
    instLhs2, instLhsLeaf2, instIndex2,
    fitExpr2.eq_def, instExpr2.eq_def, caseWidth2, List.foldl, selfWidth2, rigidMax2,
    Design2.aliasGuard, Array.toList_map])

#guard match dynamicNbaTargetStep11.sem.processes.toList with
  | [.alwaysFF "clk" (.block #[.ifStmt (.ident "en")
      (.nbaAssign (.index "q" (.ident "idx") 1) (.ident "d")) none])] => true
  | _ => false
#guard !dynamicNbaTargetStep11.sem.hasUnsupported
#guard !dynamicNbaIssueStep11.sem.hasUnsupported
#guard dynamicNbaIssueStep11.pdesign.others == []

def targetEdge : Elab1 := requireEdge dynamicNbaTargetStep11.sem
def issueEdge : Elab1 := requireEdge dynamicNbaIssueStep11.sem

#guard targetEdge.okB && targetEdge.oneWriterB && targetEdge.noEdgeB
#guard issueEdge.okB && issueEdge.oneWriterB && issueEdge.noEdgeB

-- A runtime select reserves its whole longest static prefix. The generic
-- checks must reject a second writer even when that writer uses a static bit.
#guard !( { targetEdge with procs := (targetEdge.procs.push
    { clk := "clk", rstn := none,
      body := .nbaAssign (.slice "q" 2 1) (.lit (.ofNat 1 0)) }) } ).oneWriterB
#guard !( { targetEdge with procs := #[
    { clk := "clk", rstn := none,
      body := .nbaAssign (.index "clk" (.ident "idx") 1) (.ident "d") }] } ).noEdgeB
#guard !(Lhs2.index "q" (.unsupported "fixture" "index") 1).edgeOkB targetEdge.design
#guard !(Lhs2.index "missing" (.ident "idx") 1).edgeOkB targetEdge.design
#guard !(Lhs2.index "q" (.ident "idx") 0).edgeOkB targetEdge.design
#guard !(Lhs2.concat [.index "q" (.ident "idx") 1]).edgeOkB targetEdge.design

-- Invalid selections still evaluate their RHS; a loud error cannot be hidden.
#guard match execFF targetEdge.design [("idx", LVec.lit "xxx")]
    (.nbaAssign (.index "q" (.ident "idx") 1) (.unsupported "fixture" "rhs")) with
  | .error _ => true | .ok _ => false

theorem target_profile : EdgeProfile targetEdge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold targetEdge requireEdge
    normalize_dynamic_fixture
    decide +kernel

theorem issue_profile : EdgeProfile issueEdge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold issueEdge requireEdge
    normalize_dynamic_fixture
    decide +kernel

theorem target_all_schedules (ch : Choice) {s : Store}
    (hT : targetEdge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 targetEdge ch { store := s, active := [0], nba := [], k := k } c' ∧
      targetEdge.base.view c'.store =
        commitNba2 (targetEdge.base.view s) (targetEdge.queue s [0]) :=
  rEdge target_profile ch hT (by decide) (by
    unfold targetEdge requireEdge
    normalize_dynamic_fixture
    decide +kernel) k

theorem issue_all_schedules (ch : Choice) {s : Store}
    (hT : issueEdge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 issueEdge ch { store := s, active := [0, 1], nba := [], k := k } c' ∧
      issueEdge.base.view c'.store =
        commitNba2 (issueEdge.base.view s) (issueEdge.queue s [0, 1]) :=
  rEdge issue_profile ch hT (by decide) (by
    unfold issueEdge requireEdge
    normalize_dynamic_fixture
    decide +kernel) k

def targetNames : List String := ["q"]
private def input (idx d en : String) : SvState :=
  [("idx", LVec.lit idx), ("d", LVec.lit d), ("en", LVec.lit en)]
def targetInputs : List SvState :=
  [input "000" "1" "1", input "011" "0" "1", input "x0x" "1" "1",
   input "z01" "0" "1", input "100" "1" "1", input "001" "0" "0"]
def targetRows : List (List String) :=
  [["xxxx"], ["xxx1"], ["0xx1"], ["0xx1"], ["0xx1"], ["0xx1"], ["0xx1"]]

theorem target_agrees :
    (trace targetEdge targetNames (Config1.init targetEdge) targetInputs).map
      (showRow targetEdge targetNames (Config1.init targetEdge) :: ·) = some targetRows := by
  unfold targetEdge requireEdge
  normalize_dynamic_fixture
  decide +kernel

def issueNames : List String := ["cursor", "q", "signed_q", "old_q", "words", "old_words"]
private def issueInput (reset idx idx2 sidx d : String) : SvState :=
  [("reset", LVec.lit reset), ("idx", LVec.lit idx), ("idx2", LVec.lit idx2),
   ("sidx", LVec.lit sidx), ("d", LVec.lit d)]
def issueInputs : List SvState :=
  [issueInput "1" "000" "000" "000" "00",
   issueInput "0" "011" "001" "001" "10",
   issueInput "0" "010" "010" "010" "10",
   issueInput "0" "001" "000" "111" "zz",
   issueInput "0" "x0x" "z01" "xxx" "01",
   issueInput "0" "z01" "x10" "z01" "xz",
   issueInput "0" "100" "111" "100" "11",
   issueInput "0" "000" "011" "011" "x0",
   issueInput "0" "011" "000" "000" "0z",
   issueInput "0" "001" "001" "001" "01",
   issueInput "1" "000" "000" "000" "00",
   issueInput "0" "000" "000" "000" "10"]
def issueSlots : List (SvState × Bool) :=
  issueInputs.flatMap fun entry =>
    [(SvState.set entry "clk" (.ofNat 1 0), false), ([("clk", .ofNat 1 1)], true)]
def issueRows : List (List String) :=
  [["xx", "xxxx", "xxxx", "xxxx", "xxxxxxxx", "xxxxxxxx"],
   ["00", "1010", "0101", "0000", "10010110", "xxxxxxxx"],
   ["11", "1000", "0101", "1010", "10010110", "10010110"],
   ["10", "0000", "0001", "1000", "10100110", "10010110"],
   ["01", "0zzz", "0001", "0000", "1010zz10", "10100110"],
   ["0x", "0z1z", "0001", "0zzz", "1010zz10", "1010zz10"],
   ["01", "0z1z", "0001", "0z1z", "1010zz10", "1010zz10"],
   ["00", "0z1z", "0001", "0z1z", "1010zz10", "1010zz10"],
   ["00", "0z1x", "0001", "0z1z", "1010zzx0", "1010zz10"],
   ["11", "0z1z", "000z", "0z1x", "0z10zzx0", "1010zzx0"],
   ["01", "1z1z", "001z", "0z1z", "0z1001x0", "0z10zzx0"],
   ["00", "1010", "0101", "0000", "10010110", "0z1001x0"],
   ["00", "1010", "0100", "1010", "10010110", "10010110"]]

/-- The source's two processes retain old-state sampling; runtime windows
and the data they carry are not recomputed in the NBA region. -/
theorem issue_agrees :
    (sampledSlots issueEdge issueNames (Config1.init issueEdge) issueSlots).map
      (showRow issueEdge issueNames (Config1.init issueEdge) :: ·) = some issueRows := by
  unfold issueEdge requireEdge
  normalize_dynamic_fixture
  decide +kernel

#print axioms target_profile
#print axioms issue_profile
#print axioms target_all_schedules
#print axioms issue_all_schedules
#print axioms target_agrees
#print axioms issue_agrees

end Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree
