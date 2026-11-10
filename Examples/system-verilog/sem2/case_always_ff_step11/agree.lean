/-
Step 11 clean-room evidence for plain `case` in `always_ff`.

The parser-shaped Design2 view retains two CaseStmt nodes under one edge body.
E executes the unchanged loaded body, and its low/high-slot trace agrees with
all eight Icarus/Xcelium rows. R-EDGE covers every legal process schedule.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core1Obs

namespace Examples.«system-verilog».sem2.case_always_ff_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

load_design_sv2 case_always_ff_step11
  from "Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv.json"

load_design_sv2 case_always_ff_order_step11
  from "Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_order_step11.sv.json"

-- Rewrite the loader's well-founded generate expansion at its empty-list
-- equation before kernel computation; no design or statement is copied.
local macro "normalize_case_fixture" : tactic => `(tactic|
  simp only [case_always_ff_step11.sem, case_always_ff_order_step11.sem,
    PDesign.instantiateGDAlias2, PDesign.instantiateGD2, PDesign.instantiateG2,
    PDesign.instantiate2, PDesign.instantiate2From,
    case_always_ff_step11.pdesign, case_always_ff_order_step11.pdesign, expandList2,
    List.map, instProcess2, instStmt2, instStmts2, instItems2, instPats2,
    fitExpr2.eq_def, instExpr2, caseWidth2, List.foldl, selfWidth2,
    Design2.aliasGuard, Array.toList_map])

#guard case_always_ff_step11.pdesign.others == []
#guard !case_always_ff_step11.sem.hasUnsupported
#guard match case_always_ff_step11.sem.processes.toList with
  | [LeanModels.Sv.Process2.alwaysFF "clk" (.block body)] => body.size == 2
  | _ => false

/-- Source-kind-preserving transport of the loaded always_ff bodies into E. -/
def fromAlwaysFF (d : Design2) : Elab1 where
  decls := d.decls
  procs := (d.processes.toList.map fun
    | .alwaysFF clk body => { clk := clk, rstn := none, body := body }
    | _ => { clk := "", rstn := none,
             body := .unsupported "process" "expected the fixture's always_ff" }).toArray
  name := d.name

def edge : Elab1 := fromAlwaysFF case_always_ff_step11.sem

#guard edge.procs.size == 1
#guard edge.okB
#guard edge.oneWriterB
#guard edge.noEdgeB

theorem profile : EdgeProfile edge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold edge fromAlwaysFF
    normalize_case_fixture
    decide +kernel

/-- The loaded case body runs under every legal process-atomic schedule, for
every typed store, not just the concrete differential inputs. -/
theorem all_schedules (ch : Choice) {s : Store} (hT : edge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 edge ch { store := s, active := [0], nba := [], k := k } c' ∧
      edge.base.view c'.store = commitNba2 (edge.base.view s) (edge.queue s [0]) :=
  rEdge profile ch hT (by decide) (by
    unfold edge fromAlwaysFF
    normalize_case_fixture
    decide +kernel) k

def showRow (E : Elab1) (names : List String) (c : Config1) : List String :=
  names.map (SvState.showSignal (E.base.view c.store))

/-- A test instrument: a closed result is related to E by `close_sound`. -/
def close (E : Elab1) (c : Config1) (entry : SvState) : Option Config1 :=
  match exec1 E σ_src 8 (Config1.nextSlot E c entry) with
  | .closed c' => some c'
  | .refused _ | .outOfBudget _ => none

theorem close_sound {E : Elab1} {c c' : Config1} {entry : SvState}
    (h : close E c entry = some c') :
    SlotCloses1 E σ_src (Config1.nextSlot E c entry) c' := by
  unfold close at h
  split at h
  · rename_i c₁ hc
    cases h
    exact exec1_sound hc
  · cases h
  · cases h

/-- Alternate a clock-low input slot and a clock-high edge slot. -/
def trace (E : Elab1) (names : List String) :
    Config1 → List SvState → Option (List (List String))
  | _, [] => some []
  | c, entry :: rest => do
      let lo ← close E c (SvState.set entry "clk" (.ofNat 1 0))
      let hi ← close E lo [("clk", .ofNat 1 1)]
      let rows ← trace E names hi rest
      pure (showRow E names hi :: rows)

def inputs : List SvState :=
  [[("sel", ⟨#[.l0, .l0]⟩), ("d", ⟨#[.l1, .l0, .lz, .lx]⟩)],
   [("sel", ⟨#[.l1, .l0]⟩), ("d", ⟨#[.lz, .lz, .lz, .lz]⟩)],
   [("sel", ⟨#[.lx, .l1]⟩), ("d", .ofNat 4 0)],
   [("sel", ⟨#[.lz, .l1]⟩), ("d", .ofNat 4 15)],
   [("sel", ⟨#[.l1, .lz]⟩), ("d", .ofNat 4 1)],
   [("sel", ⟨#[.l0, .lx]⟩), ("d", .ofNat 4 0)],
   [("sel", ⟨#[.lz, .lz]⟩), ("d", .ofNat 4 0)]]

def simulatorRows : List (List String) :=
  [["xxxx", "xxxx"], ["xz01", "xz01"], ["1010", "1101"], ["1011", "1101"],
   ["1111", "1101"], ["1100", "1101"], ["1111", "1101"], ["1111", "1101"]]

/-- Kernel computation of E's trace equals every pinned simulator row,
including startup. No compiled evaluator is trusted by this proof. -/
theorem agrees :
    (trace edge ["q", "q_default"] (Config1.init edge) inputs).map
      (showRow edge ["q", "q_default"] (Config1.init edge) :: ·) =
      some simulatorRows := by
  unfold edge fromAlwaysFF
  normalize_case_fixture
  decide +kernel

def orderEdge : Elab1 := fromAlwaysFF case_always_ff_order_step11.sem

#guard !case_always_ff_order_step11.sem.hasUnsupported
#guard orderEdge.okB
#guard orderEdge.oneWriterB
#guard orderEdge.noEdgeB

theorem order_profile : EdgeProfile orderEdge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold orderEdge fromAlwaysFF
    normalize_case_fixture
    decide +kernel

def orderInputs : List SvState :=
  [[("sel", .ofNat 2 0), ("d", .ofNat 4 5)],
   [("sel", .ofNat 2 1), ("d", ⟨#[.lz, .lz, .lz, .lz]⟩)],
   [("sel", ⟨#[.lx, .l1]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx]⟩)],
   [("sel", ⟨#[.l1, .lz]⟩), ("d", ⟨#[.l1, .l0, .lz, .lx]⟩)],
   [("sel", .ofNat 2 3), ("d", .ofNat 4 6)],
   [("sel", .ofNat 2 0), ("d", .ofNat 4 10)]]

def orderNames : List String := ["q", "q_hold", "q_empty", "q_nested"]

def orderSimulatorRows : List (List String) :=
  [["xxxx", "xxxx", "xxxx", "xxxx"],
   ["0101", "0101", "xxxx", "0101"],
   ["zzzz", "0101", "zzzz", "0011"],
   ["1011", "0101", "xxxx", "0011"],
   ["1100", "0101", "xz01", "0011"],
   ["1111", "0101", "0110", "0011"],
   ["1010", "1010", "0110", "0010"]]

/-- Duplicate and comma labels use the first hit; an empty matching body
does not run the default; absent defaults hold; nested NBAs preserve order. -/
theorem order_agrees :
    (trace orderEdge orderNames (Config1.init orderEdge) orderInputs).map
      (showRow orderEdge orderNames (Config1.init orderEdge) :: ·) =
      some orderSimulatorRows := by
  unfold orderEdge fromAlwaysFF
  normalize_case_fixture
  decide +kernel

#print axioms profile
#print axioms all_schedules
#print axioms close_sound
#print axioms agrees
#print axioms order_profile
#print axioms order_agrees

end Examples.«system-verilog».sem2.case_always_ff_step11.agree
