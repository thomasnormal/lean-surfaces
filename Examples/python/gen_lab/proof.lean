/-
Proof module for `Examples/python/gen_lab/spec.lean` (three-file example
layout) — created by landing **L2** of
docs/generator-tier-architecture.md, whose gate is exactly this file:
gen_lab carried 73 differential rows and no `proof.lean`, because until
LeanModels/Python/VCGen.lean there was no vocabulary in which a generator
could be SPECIFIED. Everything here is stated in that vocabulary
(`GenYields`/`GenYieldsPrefix`/`GenEmits`) over the ingested module and
proved from its frame rules.

Two of the three claims gen_lab's docstring names stop being rows and
become theorems:

* **the drain** — `upto(n)` yields exactly `0, 1, …, n-1`, SYMBOLICALLY in
  `n`, over an arbitrary world;
* **laziness is real** — `naturals()` is infinite (it has no `GenYields`
  at all) and yet hands over a prefix of EVERY length and is left in one
  fixed resumption configuration. A design that pre-expanded a generator
  into a list could not state this, let alone prove it.

The third — a generator is heap IDENTITY — stays a `#py_check` row, and
the last section records the measurement that says why: promoting a
CONCRETE run to a theorem costs a checked kernel reduction, which this
interpreter cannot afford at 4096 fuel.

MEASURED, and recorded because it is a general trap: stating the program
shape as ONE existential over twelve source spans
(`∃ s₁ … s₁₂, uptoBody = [ … ]`, closed by `rfl`) cost 5½ minutes of
elaboration on its own — twelve metavariables unified at once against a
whnf of the 271 KB module literal. Projecting the pieces out one at a time
(`uptoWhileS`, `uptoTest`, …) and pinning each with its own small
existential is the same claim an order of magnitude faster, and it reads
better: the statements below mention the PROJECTIONS, so they say "the
shipped `upto`" rather than "some program with these spans".
-/
import LeanModels

namespace Examples.python.gen_lab.proof

open LeanModels LeanModels.Python
open scoped Run

load_program gen_lab from "Examples/python/gen_lab/gen_lab.json"

/-! ## The two generator bodies, taken apart

Never retyped: every definition below projects out of `gen_lab`, so a
changed PROGRAM stops the `rfl`s and the proofs fail loudly, while a
re-extracted envelope that only moves spans changes nothing. -/

private def nowhere : Span := ⟨0, 0, 0, 0⟩

/-- `upto`'s body as `callIn`'s generator arm stores it. -/
def uptoBody : List Stmt :=
  match findFunction gen_lab "upto" with
  | some f => f.body.toList
  | none => []

/-- `naturals`'s body, likewise. -/
def natBody : List Stmt :=
  match findFunction gen_lab "naturals" with
  | some f => f.body.toList
  | none => []

private def stmt0 (ss : List Stmt) : Stmt :=
  match ss with | s :: _ => s | _ => .pass nowhere

private def stmt1 (ss : List Stmt) : Stmt :=
  match ss with | _ :: s :: _ => s | _ => .pass nowhere

private def testOf (s : Stmt) : Expr :=
  match s with | .whileLoop t _ _ _ => t | _ => .constant .none nowhere

private def bodyOf (s : Stmt) : List Stmt :=
  match s with | .whileLoop _ b _ _ => b.toList | _ => []

/-- `i = 0`. -/
def uptoAssign : Stmt := stmt0 uptoBody
/-- `while i < n: …`. -/
def uptoWhileS : Stmt := stmt1 uptoBody
/-- `i < n`. -/
def uptoTest : Expr := testOf uptoWhileS
/-- The loop body. -/
def uptoLoopBody : List Stmt := bodyOf uptoWhileS
/-- `yield i`. -/
def uptoYield : Stmt := stmt0 uptoLoopBody
/-- `i += 1`. -/
def uptoBump : Stmt := stmt1 uptoLoopBody

/-- `i = 0`. -/
def natAssign : Stmt := stmt0 natBody
/-- `while True: …`. -/
def natWhileS : Stmt := stmt1 natBody
/-- `True`. -/
def natTest : Expr := testOf natWhileS
/-- The loop body. -/
def natLoopBody : List Stmt := bodyOf natWhileS
/-- `yield i`. -/
def natYield : Stmt := stmt0 natLoopBody
/-- `i += 1`. -/
def natBump : Stmt := stmt1 natLoopBody

/-! ### The structure, pinned by `rfl` (no metavariables) -/

theorem uptoBody_split : uptoBody = [uptoAssign, uptoWhileS] := rfl
theorem uptoLoopBody_split : uptoLoopBody = [uptoYield, uptoBump] := rfl
theorem uptoAssign_plan : genPlan uptoAssign = .delegate := rfl
theorem uptoWhile_plan :
    genPlan uptoWhileS = .whileHere uptoTest uptoLoopBody [] := rfl

theorem natBody_split : natBody = [natAssign, natWhileS] := rfl
theorem natLoopBody_split : natLoopBody = [natYield, natBump] := rfl
theorem natAssign_plan : genPlan natAssign = .delegate := rfl
theorem natWhile_plan :
    genPlan natWhileS = .whileHere natTest natLoopBody [] := rfl

/-! ### The spelling of each piece, pinned by its own small existential —
the source spans are the only thing left free. -/

theorem uptoAssign_lit :
    ∃ s₁ s₂ s₃, uptoAssign = .assign #[.name "i" s₁] (.constant (.int 0) s₂) s₃ :=
  ⟨_, _, _, rfl⟩

theorem uptoTest_lit :
    ∃ s₄ s₅ s₆, uptoTest = .compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆ :=
  ⟨_, _, _, rfl⟩

theorem uptoYield_lit : ∃ s₇ s₈, uptoYield = .yieldStmt (.name "i" s₇) s₈ :=
  ⟨_, _, rfl⟩

theorem uptoBump_lit :
    ∃ s₉ s₁₀ s₁₁,
      uptoBump = .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ :=
  ⟨_, _, _, rfl⟩

theorem natAssign_lit :
    ∃ s₁ s₂ s₃, natAssign = .assign #[.name "i" s₁] (.constant (.int 0) s₂) s₃ :=
  ⟨_, _, _, rfl⟩

theorem natTest_lit : ∃ s₄, natTest = .constant (.bool true) s₄ := ⟨_, rfl⟩

theorem natYield_lit : ∃ s₅ s₆, natYield = .yieldStmt (.name "i" s₅) s₆ :=
  ⟨_, _, rfl⟩

theorem natBump_lit :
    ∃ s₇ s₈ s₉,
      natBump = .augAssign (.name "i" s₇) .add (.constant (.int 1) s₈) s₉ :=
  ⟨_, _, _, rfl⟩

/-! ## The configurations the interpreter builds -/

/-- The frame stack a freshly created `upto(n)` carries — literally
`callIn`'s `[.block f.body.toList]`. -/
def uptoCont : GenCont := [.block uptoBody]

/-- …and `naturals()`'s. -/
def natCont : GenCont := [.block natBody]

/-- The locals `callIn`'s generator arm builds for `upto(n)` — literally
its `mkCallEnv f.params args`. -/
def uptoEntry (n : Int) : REnv :=
  match findFunction gen_lab "upto" with
  | some f => mkCallEnv f.params #[.int n]
  | none => []

/-- …and for `naturals()`, which takes no arguments. -/
def natEntry : REnv :=
  match findFunction gen_lab "naturals" with
  | some f => mkCallEnv f.params #[]
  | none => []

/-- `upto`'s frame once the loop counter exists. -/
def uptoEnv (n i : Int) : REnv := [("n", .int n), ("i", .int i)]

/-- `naturals`'s frame. -/
def natEnv (i : Int) : REnv := [("i", .int i)]

/-- Where `naturals()` is left suspended after EVERY yield: the `i += 1`
that has not run yet, the loop frame, and the empty block the `while` push
left below it. Independent of how many values it has already handed
over — which is itself part of the claim. -/
def natResume : GenCont :=
  [.block [natBump], .whileLoop natTest natLoopBody [], .block []]

/-- The consecutive integers a counting generator hands over. -/
def intsFrom (i : Int) : Nat → List RVal
  | 0 => []
  | c + 1 => .int i :: intsFrom (i + 1) c

@[simp] theorem intsFrom_zero (i : Int) : intsFrom i 0 = [] := rfl

@[simp] theorem intsFrom_succ (i : Int) (c : Nat) :
    intsFrom i (c + 1) = .int i :: intsFrom (i + 1) c := rfl

theorem uptoCont_eq : uptoCont = [.block uptoBody] := rfl
theorem natCont_eq : natCont = [.block natBody] := rfl
theorem uptoEntry_eq (n : Int) : uptoEntry n = [("n", .int n)] := rfl
theorem natEntry_eq : natEntry = [] := rfl

/-! ## The small facts the frame rules consume -/

/-- Threshold form of one decided statement run. -/
private theorem run_at_least {s : Stmt} {st st' : FrameState} {fuel : Nat}
    (h : execStmt gen_lab fuel st s = .ok st' .next) :
    ∃ t, ∀ F ≥ t, execStmt gen_lab F st s = .ok st' .next :=
  ⟨fuel, fun F hF => execStmt_mono h (by simp) F hF⟩

/-- Build a statement triple from one decided symbolic run (the shape
`GenEmits.blockDelegate` consumes). -/
private theorem stmtTriple_of_run {s : Stmt} {st st' : FrameState} {fuel : Nat}
    {Q : FrameState → Prop} (hrun : execStmt gen_lab fuel st s = .ok st' .next)
    (hQ : Q st') : PyStmtTriple gen_lab (fun x => x = st) s (PyPost.ofNext Q) := by
  intro x hx
  subst hx
  exact ⟨fuel, fun F hF => by rw [execStmt_mono hrun (by simp) F hF]; exact hQ⟩

private theorem truthy_bool (w : World) (b : Bool) :
    truthyH w.heap (.bool b) = .ok b := by simp [truthyH, truthy]

/-- Reading the loop counter out of the frame. -/
private theorem evals_i (w : World) (env : REnv) (i : Int) (sp : Span)
    (henv : Env.lookup env "i" = some (RVal.int i)) :
    EvalsTo gen_lab ⟨w, env⟩ (.name "i" sp) (.int i) := by
  refine EvalsTo.of_eval (fuel := 4) ?_
  py_simp [henv]

/-- `upto`'s loop test, at an arbitrary counter and bound. -/
private theorem evals_test (w : World) (n i : Int) (s₄ s₅ s₆ : Span) :
    EvalsTo gen_lab ⟨w, uptoEnv n i⟩
      (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
      (.bool (decide (i < n))) := by
  refine EvalsTo.of_eval (fuel := 8) ?_
  py_simp [uptoEnv]
  by_cases h : i < n <;> simp [h]

/-! ## `upto`: the drain, symbolically in `n`

`GenEmits` rather than `GenYields` for the loop, because the `while` frame
sits ABOVE the empty block its push left behind — the frame-polymorphic
form is what lets the two be spliced by `List.append`. -/

theorem upto_loop (w : World) (n : Int) :
    ∀ (c : Nat) (i : Int), i + (c : Int) = n →
      GenEmits gen_lab ⟨w, uptoEnv n i⟩ [.whileLoop uptoTest uptoLoopBody []]
        (intsFrom i c) ⟨w, uptoEnv n n⟩ := by
  obtain ⟨s₄, s₅, s₆, htest⟩ := uptoTest_lit
  obtain ⟨s₇, s₈, hyield⟩ := uptoYield_lit
  obtain ⟨s₉, s₁₀, s₁₁, hbump⟩ := uptoBump_lit
  rw [htest, uptoLoopBody_split, hyield, hbump]
  intro c
  induction c with
  | zero =>
    intro i hi
    have hin : i = n := by simpa using hi
    subst hin
    refine GenEmits.silent (st₁ := ⟨w, uptoEnv i i⟩)
      (pre₁ := [GenFrame.block []]) (fun k => ?_) ?_
    · simpa using genSilent_whileFalse (m := gen_lab) (k := k)
        (evals_test w i i s₄ s₅ s₆) (by rw [truthy_bool]; simp)
    · exact GenEmits.silent (pre₁ := ([] : GenCont))
        (fun k => by simpa using genSilent_blockNil) GenEmits.nil
  | succ c ih =>
    intro i hi
    have hlt : i < n := by omega
    have hnext : (i + 1) + (c : Int) = n := by omega
    -- the test is true: push the body
    refine GenEmits.silent
      (pre₁ := [GenFrame.block
        [ .yieldStmt (.name "i" s₇) s₈,
          .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ],
        GenFrame.whileLoop (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
          [ .yieldStmt (.name "i" s₇) s₈,
            .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ] []])
      (fun k => by
        simpa using genSilent_whileTrue (m := gen_lab) (k := k)
          (evals_test w n i s₄ s₅ s₆) (by rw [truthy_bool]; simp [hlt]))
      ?_
    -- the yield
    rw [intsFrom_succ]
    refine GenEmits.cons
      (pre₁ := [GenFrame.block
        [.augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁],
        GenFrame.whileLoop (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
          [ .yieldStmt (.name "i" s₇) s₈,
            .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ] []])
      (fun k => by
        simpa using genSteps_yieldHere (m := gen_lab)
          (k := GenFrame.whileLoop
            (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
            [ .yieldStmt (.name "i" s₇) s₈,
              .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ] [] :: k)
          (s := .yieldStmt (.name "i" s₇) s₈)
          (ss := [.augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁])
          rfl (evals_i w (uptoEnv n i) i s₇ rfl))
      ?_
    -- `i += 1` delegates to the ordinary statement executor
    refine GenEmits.silent
      (pre₁ := [GenFrame.block [],
        GenFrame.whileLoop (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
          [ .yieldStmt (.name "i" s₇) s₈,
            .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ] []])
      (fun k => by
        simpa using genSilent_delegate (m := gen_lab)
          (k := GenFrame.whileLoop
            (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
            [ .yieldStmt (.name "i" s₇) s₈,
              .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ] [] :: k)
          (s := .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁)
          (ss := ([] : List Stmt)) rfl
          (run_at_least (fuel := 8) (st := ⟨w, uptoEnv n i⟩)
            (st' := ⟨w, uptoEnv n (i + 1)⟩) (by py_simp [uptoEnv])))
      ?_
    refine GenEmits.silent
      (pre₁ := [GenFrame.whileLoop
        (.compare (.name "i" s₄) #[.lt] #[.name "n" s₅] s₆)
        [ .yieldStmt (.name "i" s₇) s₈,
          .augAssign (.name "i" s₉) .add (.constant (.int 1) s₁₀) s₁₁ ] []])
      (fun k => by simpa using genSilent_blockNil) ?_
    exact ih (i + 1) hnext

/-- **THE FIRST GENERATOR THEOREM IN THIS REPO.**

`upto(n)`, suspended exactly as `callIn` leaves it, yields the integers
`0, 1, …, n-1` and then finishes — for every `n`, in every world.

Symbolic in the count, symbolic in the world, and stated over the frame
stack the interpreter actually builds (`uptoCont` is `callIn`'s
`[.block f.body.toList]`, `uptoEntry` its `mkCallEnv`). Before
LeanModels/Python/VCGen.lean this sentence had no `Prop` to be. -/
theorem upto_yields (w : World) (c : Nat) :
    GenYields gen_lab ⟨w, uptoEntry (c : Int)⟩ uptoCont (intsFrom 0 c)
      ⟨w, uptoEnv (c : Int) (c : Int)⟩ := by
  obtain ⟨s₁, s₂, s₃, hassign⟩ := uptoAssign_lit
  refine GenEmits.toYields ?_
  rw [uptoCont_eq, uptoBody_split, uptoEntry_eq, hassign]
  -- `i = 0` delegates through a statement triple (the user-facing form)
  refine GenEmits.blockDelegate (P := fun x => x = ⟨w, [("n", .int (c : Int))]⟩)
    rfl (stmtTriple_of_run (fuel := 8) (st' := ⟨w, uptoEnv (c : Int) 0⟩)
      (by py_simp [uptoEnv]) ?_) rfl
  -- the `while` becomes a frame, and the loop lemma runs it out
  refine GenEmits.silent
    (pre₁ := [GenFrame.whileLoop uptoTest uptoLoopBody [], GenFrame.block []])
    (fun k => by
      simpa using genSilent_whileHere (m := gen_lab) (k := k)
        (ss := ([] : List Stmt)) (s := uptoWhileS) uptoWhile_plan)
    ?_
  have hpop : GenEmits gen_lab ⟨w, uptoEnv (c : Int) (c : Int)⟩
      [GenFrame.block []] [] ⟨w, uptoEnv (c : Int) (c : Int)⟩ :=
    GenEmits.silent (pre₁ := ([] : GenCont))
      (fun k => by simpa using genSilent_blockNil) GenEmits.nil
  simpa using GenEmits.trans (upto_loop w (c : Int) c 0 (by omega)) hpop

/-! ## `naturals`: laziness, as a theorem

`naturals()` never finishes, so it has no `GenYields` — that is not a gap,
it is the fact. What it does have is a prefix of every length with the
machine still suspended afterwards, which is precisely the property
sunfish's beta cutoff depends on. -/

theorem naturals_loop (w : World) (k : GenCont) :
    ∀ (c : Nat) (i : Int),
      GenYieldsPrefix gen_lab ⟨w, natEnv i⟩
        (.whileLoop natTest natLoopBody [] :: k)
        (intsFrom i (c + 1)) ⟨w, natEnv (i + (c : Int))⟩
        (.block [natBump] :: .whileLoop natTest natLoopBody [] :: k) := by
  obtain ⟨s₄, htest⟩ := natTest_lit
  obtain ⟨s₅, s₆, hyield⟩ := natYield_lit
  obtain ⟨s₇, s₈, s₉, hbump⟩ := natBump_lit
  rw [htest, natLoopBody_split, hyield, hbump]
  intro c
  induction c with
  | zero =>
    intro i
    rw [intsFrom_succ, intsFrom_zero]
    refine GenYieldsPrefix.silent (v := .int i) (vs := [])
      (genSilent_whileTrue (m := gen_lab) (tv := .bool true)
        (EvalsTo.of_eval (fuel := 4) (by py_simp)) (by rw [truthy_bool])) ?_
    refine GenYieldsPrefix.cons
      (genSteps_yieldHere (m := gen_lab) (s := .yieldStmt (.name "i" s₅) s₆)
        rfl (evals_i w (natEnv i) i s₅ rfl)) ?_
    simpa using GenYieldsPrefix.nil
  | succ c ih =>
    intro i
    rw [intsFrom_succ]
    refine GenYieldsPrefix.silent (v := .int i)
      (genSilent_whileTrue (m := gen_lab) (tv := .bool true)
        (EvalsTo.of_eval (fuel := 4) (by py_simp)) (by rw [truthy_bool])) ?_
    refine GenYieldsPrefix.cons
      (genSteps_yieldHere (m := gen_lab) (s := .yieldStmt (.name "i" s₅) s₆)
        rfl (evals_i w (natEnv i) i s₅ rfl)) ?_
    have hstepBump : GenSilent gen_lab ⟨w, natEnv i⟩
        (GenFrame.block
            [.augAssign (.name "i" s₇) .add (.constant (.int 1) s₈) s₉]
          :: GenFrame.whileLoop (.constant (.bool true) s₄)
              [ .yieldStmt (.name "i" s₅) s₆,
                .augAssign (.name "i" s₇) .add (.constant (.int 1) s₈) s₉ ] []
          :: k)
        ⟨w, natEnv (i + 1)⟩
        (GenFrame.block []
          :: GenFrame.whileLoop (.constant (.bool true) s₄)
              [ .yieldStmt (.name "i" s₅) s₆,
                .augAssign (.name "i" s₇) .add (.constant (.int 1) s₈) s₉ ] []
          :: k) :=
      genSilent_delegate
        (s := .augAssign (.name "i" s₇) .add (.constant (.int 1) s₈) s₉) rfl
        (run_at_least (fuel := 8) (st := ⟨w, natEnv i⟩)
          (st' := ⟨w, natEnv (i + 1)⟩) (by py_simp [natEnv]))
    have harith : (i + 1) + (c : Int) = i + ((c : Int) + 1) := by omega
    have hih := ih (i + 1)
    rw [harith] at hih
    refine GenYieldsPrefix.silent (v := .int (i + 1))
      (GenSilent.trans hstepBump genSilent_blockNil) ?_
    rw [intsFrom_succ] at hih
    simpa using hih

/-- **Laziness, as a theorem.** `naturals()` — the generator whose Python
body is `while True: yield i; i += 1` — hands over a prefix of EVERY
length and is left suspended in one fixed configuration, ready for the
next consumer.

What is not here is the point: there is no `GenYields` for `naturals`,
because it never finishes, and an eager list-producing representation of a
generator could not have a statement of this shape at all. -/
theorem naturals_prefix (w : World) (c : Nat) :
    GenYieldsPrefix gen_lab ⟨w, natEntry⟩ natCont (intsFrom 0 (c + 1))
      ⟨w, natEnv (c : Int)⟩ natResume := by
  obtain ⟨s₁, s₂, s₃, hassign⟩ := natAssign_lit
  rw [natCont_eq, natEntry_eq, natBody_split, hassign, natResume, intsFrom_succ]
  -- `i = 0` delegates
  refine GenYieldsPrefix.silent (v := .int 0)
    (genSilent_delegate (s := .assign #[.name "i" s₁] (.constant (.int 0) s₂) s₃)
      rfl (run_at_least (fuel := 8) (st := ⟨w, ([] : REnv)⟩)
        (st' := ⟨w, natEnv 0⟩) (by py_simp [natEnv]))) ?_
  -- the `while True` becomes a frame
  refine GenYieldsPrefix.silent (v := .int 0)
    (genSilent_whileHere (m := gen_lab) (ss := ([] : List Stmt))
      (s := natWhileS) natWhile_plan) ?_
  rw [← intsFrom_succ]
  simpa using naturals_loop w [GenFrame.block []] c 0

/-! ## Non-vacuity: the symbolic theorems against the kernel

`upto_yields` at `n = 5`, run through `drainGen` in the kernel, is the
generator behind the `total(5) = 10` differential row seen directly; the
`stepGenN` line is `naturals_prefix` at four values. -/

private def w0 : World := ⟨#[], [], [], []⟩

#guard drainGen gen_lab 256 ⟨w0, uptoEntry 5⟩ uptoCont
  == .ok ⟨w0, uptoEnv 5 5⟩ [.int 0, .int 1, .int 2, .int 3, .int 4]

#guard stepGenN gen_lab 256 ⟨w0, natEntry⟩ natCont 4
  == .ok ⟨w0, natEnv 3⟩ ([.int 0, .int 1, .int 2, .int 3], natResume)

/-! ## The rows, promoted — and the one route that is NOT taken

`upto_yields` at `c = 5` is the generator behind the `total(5) = 10`
differential row, as a theorem rather than a check, and it comes free:
the symbolic theorem is instantiated, no interpreter run is elaborated.

What is deliberately NOT here is a kernel promotion of the concrete
surface rows (`gen_lab.aliased(4) ==> 1` by `CallsTo.intro 4096 (by rfl)`).
It was tried and it does not pay: elaborator/kernel reduction of a
4096-fuel run of this module blows past a million heartbeats, which is the
boundary already measured and recorded for this interpreter
(`Examples/python/sunfish/pins_clock.lean`: `#guard`'s evaluator is
untrusted and ~1000× faster than a checked reduction, and one 2-node probe
exceeded 16 minutes of `decide +kernel`). The identity rows therefore stay
`#py_check` pins at the trust level of the whole existing pin battery, and
the theorems here are the symbolic ones — which is the better trade
anyway: `upto_yields` covers every `n`, and no concrete row does. -/

theorem upto5_yields (w : World) :
    GenYields gen_lab ⟨w, uptoEntry 5⟩ uptoCont
      [.int 0, .int 1, .int 2, .int 3, .int 4] ⟨w, uptoEnv 5 5⟩ := by
  simpa using upto_yields w 5

theorem naturals4_prefix (w : World) :
    GenYieldsPrefix gen_lab ⟨w, natEntry⟩ natCont
      [.int 0, .int 1, .int 2, .int 3] ⟨w, natEnv 3⟩ natResume := by
  simpa using naturals_prefix w 3

end Examples.python.gen_lab.proof
