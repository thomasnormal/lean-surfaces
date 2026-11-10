/-
Step 11 clean-room evidence for a plain `always @(posedge clk)`.

The source kind is retained through E's edge elaborator. The unchanged loaded
bodies execute in E, and their kernel-checked traces match both simulators.
-/
import LeanModels.Sv.Kernel.Core1Elab
import Examples.«system-verilog».sem2.case_always_ff_step11.agree

namespace Examples.«system-verilog».sem2.plain_always_posedge_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

load_design_sv2 plainAlwaysPosedgeStep11
  from "Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv.json"

load_design_sv2 plainAlwaysKindsStep11
  from "Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_kinds_step11.sv.json"

local macro "normalize_plain_fixture" : tactic => `(tactic|
  simp only [plainAlwaysPosedgeStep11.sem, plainAlwaysKindsStep11.sem,
    PDesign.instantiateGDAlias2, PDesign.instantiateGD2, PDesign.instantiateG2,
    PDesign.instantiate2, PDesign.instantiate2From,
    plainAlwaysPosedgeStep11.pdesign, plainAlwaysKindsStep11.pdesign, expandList2,
    List.map, instProcess2, instStmt2, instStmts2, instItems2, instPats2,
    fitExpr2.eq_def, instExpr2.eq_def, caseWidth2, List.foldl, selfWidth2, rigidMax2,
    Design2.aliasGuard, Array.toList_map])

#guard plainAlwaysPosedgeStep11.pdesign.others == []
#guard !plainAlwaysPosedgeStep11.sem.hasUnsupported
#guard match plainAlwaysPosedgeStep11.sem.processes.toList with
  | [.alwaysPlain "clk" (.block body)] => body.size == 2
  | _ => false

/-- Fixture adapter: an elaboration failure remains a loud body, so it cannot
pass the profile or trace checks below. -/
def requireEdge (d : Design2) : Elab1 :=
  match Elab1.ofEdgeDesign2 d with
  | .ok E => E
  | .error msg =>
      { decls := d.decls
        name := d.name
        procs := #[{ clk := "", rstn := none, body := .unsupported "edge elaboration" msg }] }

def plainEdge : Elab1 := requireEdge plainAlwaysPosedgeStep11.sem
def kindsEdge : Elab1 := requireEdge plainAlwaysKindsStep11.sem

#guard match Elab1.ofEdgeDesign2 plainAlwaysPosedgeStep11.sem with
  | .ok _ => true | .error _ => false
#guard match Elab1.ofEdgeDesign2 plainAlwaysKindsStep11.sem with
  | .ok _ => true | .error _ => false
#guard plainEdge.procs.toList.map FF.style == [.alwaysPlain]
#guard kindsEdge.procs.toList.map FF.style == [.alwaysPlain, .alwaysFF]
#guard plainEdge.okB && plainEdge.oneWriterB && plainEdge.noEdgeB
#guard kindsEdge.okB && kindsEdge.oneWriterB && kindsEdge.noEdgeB

-- Unsupported processes are never filtered out of an otherwise valid design.
#guard match Elab1.ofEdgeDesign2 { plainAlwaysPosedgeStep11.sem with
    processes := plainAlwaysPosedgeStep11.sem.processes.push (.alwaysComb (.block #[])) } with
  | .error msg => msg.startsWith "9.2:" | .ok _ => false
#guard match Elab1.ofEdgeDesign2 { plainAlwaysPosedgeStep11.sem with
    processes := #[.alwaysPlain "clk" (.blockingAssign (.ident "q") (.lit (.ofNat 4 0)))] } with
  | .error msg => msg.startsWith "9.2.2.1/9.2.2.4:" | .ok _ => false
#guard match Elab1.ofEdgeDesign2 { plainAlwaysPosedgeStep11.sem with
    processes := #[.alwaysPlain "missing" (.block #[])] } with
  | .error msg => msg.startsWith "9.4.2:" | .ok _ => false

theorem plain_profile : EdgeProfile plainEdge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold plainEdge requireEdge
    normalize_plain_fixture
    decide +kernel

theorem kinds_profile : EdgeProfile kindsEdge := by
  apply EdgeProfile.ofChecks
  all_goals
    try unfold AllFour
    unfold kindsEdge requireEdge
    normalize_plain_fixture
    decide +kernel

theorem plain_all_schedules (ch : Choice) {s : Store}
    (hT : plainEdge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 plainEdge ch { store := s, active := [0], nba := [], k := k } c' ∧
      plainEdge.base.view c'.store =
        commitNba2 (plainEdge.base.view s) (plainEdge.queue s [0]) :=
  rEdge plain_profile ch hT (by decide) (by
    unfold plainEdge requireEdge
    normalize_plain_fixture
    decide +kernel) k

theorem kinds_all_schedules (ch : Choice) {s : Store}
    (hT : kindsEdge.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 kindsEdge ch { store := s, active := [0, 1], nba := [], k := k } c' ∧
      kindsEdge.base.view c'.store =
        commitNba2 (kindsEdge.base.view s) (kindsEdge.queue s [0, 1]) :=
  rEdge kinds_profile ch hT (by decide) (by
    unfold kindsEdge requireEdge
    normalize_plain_fixture
    decide +kernel) k

def plainNames : List String := ["q", "q_copy"]
def plainInputs : List SvState :=
  [[("en", .ofNat 1 0), ("d", .ofNat 4 9)],
   [("en", .ofNat 1 1), ("d", .ofNat 4 6)],
   [("en", ⟨#[.lx]⟩), ("d", .ofNat 4 3)],
   [("en", ⟨#[.lz]⟩), ("d", ⟨#[.lz, .lz, .lz, .lz]⟩)],
   [("en", .ofNat 1 1), ("d", ⟨#[.l1, .l0, .lz, .lx]⟩)]]
def plainSimulatorRows : List (List String) :=
  [["xxxx", "xxxx"], ["1010", "1001"], ["0110", "0110"],
   ["1010", "0011"], ["1010", "zzzz"], ["xz01", "xz01"]]

/-- Kernel computation includes startup and every original oracle row. -/
theorem plain_agrees :
    (trace plainEdge plainNames (Config1.init plainEdge) plainInputs).map
      (showRow plainEdge plainNames (Config1.init plainEdge) :: ·) =
      some plainSimulatorRows := by
  unfold plainEdge requireEdge
  normalize_plain_fixture
  decide +kernel

def kindsNames : List String := ["q", "q_old", "q_case"]
def kindsInputs : List SvState :=
  [[("sel", .ofNat 2 0), ("d", .ofNat 4 0)],
   [("sel", ⟨#[.lx, .l1]⟩), ("d", .ofNat 4 3)],
   [("sel", ⟨#[.lz, .l1]⟩), ("d", ⟨#[.l1, .l0, .lz, .lx]⟩)],
   [("sel", .ofNat 2 0), ("d", ⟨#[.lz, .lz, .lz, .lz]⟩)],
   [("sel", .ofNat 2 3), ("d", .ofNat 4 10)],
   [("sel", .ofNat 2 0), ("d", .ofNat 4 6)]]

/-- Test instrumentation for explicit clock transitions. Every slot uses
the same `close` instrument and its `close_sound` theorem. -/
def sampledSlots (E : Elab1) (names : List String) :
    Config1 → List (SvState × Bool) → Option (List (List String))
  | _, [] => some []
  | c, (entry, sample) :: rest => do
      let c' ← close E c entry
      let rows ← sampledSlots E names c' rest
      pure (if sample then showRow E names c' :: rows else rows)

/-- A test-executor cache. Undeclared and non-flat variables retain the
original store; declared values are evaluated once into a list. -/
@[noinline] def storeFromValues (values : List Val) (fallback : Store) : Store :=
  fun x => match x.path with
    | [] => match values[x.decl]? with
      | some v => v
      | none => fallback x
    | _ :: _ => fallback x

theorem storeFromValues_eq (E : Elab1) (s : Store) :
    storeFromValues ((List.range E.decls.size).map fun i => s { decl := i }) s = s := by
  funext ⟨path, i⟩
  cases path with
  | cons a rest => rfl
  | nil =>
      by_cases hi : i < E.decls.size <;>
        simp [storeFromValues, hi]

/-- Returning a record forces the list before the next slot's store reads;
the cached store is extensionally identical even outside the declared scope. -/
@[noinline] def cacheConfig (E : Elab1) (c : Config1) : Config1 :=
  let values := (List.range E.decls.size).map fun i => c.store { decl := i }
  { c with store := storeFromValues values c.store }

theorem cacheConfig_eq (E : Elab1) (c : Config1) : cacheConfig E c = c := by
  cases c
  simp only [cacheConfig, storeFromValues_eq]

def cachedClose (E : Elab1) (c : Config1) (entry : SvState) : Option Config1 :=
  (close E c entry).map (cacheConfig E)

theorem cachedClose_eq (E : Elab1) (c : Config1) (entry : SvState) :
    cachedClose E c entry = close E c entry := by
  unfold cachedClose
  cases hc : close E c entry with
  | none => rfl
  | some c' => simp only [Option.map_some, cacheConfig_eq]

def sampledSlotsCached (E : Elab1) (names : List String) :
    Config1 → List (SvState × Bool) → Option (List (List String))
  | _, [] => some []
  | c, (entry, sample) :: rest => do
      let c' ← cachedClose E c entry
      let rows ← sampledSlotsCached E names c' rest
      pure (if sample then showRow E names c' :: rows else rows)

theorem sampledSlotsCached_eq (E : Elab1) (names : List String) (c : Config1)
    (entries : List (SvState × Bool)) :
    sampledSlotsCached E names c entries = sampledSlots E names c entries := by
  induction entries generalizing c with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨event, sample⟩
      simp only [sampledSlotsCached, sampledSlots, cachedClose_eq]
      cases hc : close E c event with
      | none => rfl
      | some c' => simp only [ih]

def kindsSlots : List (SvState × Bool) :=
  kindsInputs.flatMap (fun entry =>
    [(SvState.set entry "clk" (.ofNat 1 0), false), ([("clk", .ofNat 1 1)], true)]) ++
  [([("clk", .ofNat 1 0)], false),
   ([("clk", ⟨#[.lx]⟩), ("sel", .ofNat 2 0), ("d", .ofNat 4 9)], true),
   ([("clk", ⟨#[.lz]⟩), ("d", .ofNat 4 1)], true),
   ([("clk", .ofNat 1 1), ("d", .ofNat 4 5)], true),
   ([("clk", ⟨#[.lx]⟩), ("d", .ofNat 4 15)], true),
   ([("clk", .ofNat 1 1), ("d", ⟨#[.lz, .lz, .lz, .lz]⟩)], true),
   ([("clk", .ofNat 1 0)], false),
   ([("clk", ⟨#[.lz]⟩), ("d", .ofNat 4 3)], true)]

def kindsSimulatorRows : List (List String) :=
  [["xxxx", "xxxx", "xxxx"], ["1111", "xxxx", "0000"],
   ["1100", "1111", "1010"], ["xx10", "1100", "0101"],
   ["xxxx", "xx10", "zzzz"], ["0101", "xxxx", "0101"],
   ["1001", "0101", "0110"],
   ["0110", "1001", "1001"], ["0110", "1001", "1001"],
   ["1010", "0110", "0101"], ["1010", "0110", "0101"],
   ["xxxx", "1010", "zzzz"], ["1100", "xxxx", "0011"]]

/-- Both source styles read the same pre-edge state. The plain body's last
NBA wins, and its plain-case node keeps exact x/z matching. -/
theorem kinds_agrees :
    (sampledSlots kindsEdge kindsNames (Config1.init kindsEdge) kindsSlots).map
      (showRow kindsEdge kindsNames (Config1.init kindsEdge) :: ·) =
      some kindsSimulatorRows := by
  unfold kindsEdge requireEdge
  normalize_plain_fixture
  decide +kernel

#print axioms plain_profile
#print axioms kinds_profile
#print axioms plain_all_schedules
#print axioms kinds_all_schedules
#print axioms plain_agrees
#print axioms kinds_agrees
#print axioms storeFromValues_eq
#print axioms cacheConfig_eq
#print axioms cachedClose_eq
#print axioms sampledSlotsCached_eq

end Examples.«system-verilog».sem2.plain_always_posedge_step11.agree
