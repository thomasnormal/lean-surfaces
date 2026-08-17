/-
Proof module for `Examples/python/gen_lab/spec.lean` (three-file example
layout) — created by landing **L2** of
docs/generator-tier-architecture.md, whose gate is exactly this file:
gen_lab carried 73 differential rows and no `proof.lean`, because until
LeanModels/Python/VCGen.lean there was no vocabulary in which a generator
could be SPECIFIED. Everything here is stated in that vocabulary
(`GenYields`/`GenYieldsPrefix`/`GenEmits`) over the ingested module and
proved from its frame rules.

All three claims gen_lab's docstring names are theorems here — the first
two since L2, the third since L3's tail:

* **the drain** — `upto(n)` yields exactly `0, 1, …, n-1`, SYMBOLICALLY in
  `n`, over an arbitrary world;
* **laziness is real** — `naturals()` is infinite (it has no `GenYields`
  at all) and yet hands over a prefix of EVERY length and is left in one
  fixed resumption configuration. A design that pre-expanded a generator
  into a list could not state this, let alone prove it.
* **`break` SUSPENDS, and a generator is heap IDENTITY** —
  `two_phase_calls`, in the L3 section: one object, two loops, the second
  resuming at the configuration the first abandoned. Symbolic in `n`.

What is still not here is a kernel promotion of a CONCRETE surface row
(`aliased(4) ==> 1` by `rfl` at 4096 fuel); the last section of the L2
material records the measurement that says why, and the symbolic route
above is the better trade anyway.

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
anyway: `upto_yields` covers every `n`, and no concrete row does. (The
identity CLAIM is not left to the rows: `two_phase_calls` in the L3 section
proves it symbolically. What stays out is promoting a concrete run.) -/

theorem upto5_yields (w : World) :
    GenYields gen_lab ⟨w, uptoEntry 5⟩ uptoCont
      [.int 0, .int 1, .int 2, .int 3, .int 4] ⟨w, uptoEnv 5 5⟩ := by
  simpa using upto_yields w 5

theorem naturals4_prefix (w : World) :
    GenYieldsPrefix gen_lab ⟨w, natEntry⟩ natCont
      [.int 0, .int 1, .int 2, .int 3] ⟨w, natEnv 3⟩ natResume := by
  simpa using naturals_prefix w 3

/-! # L3: the CONSUMER side

Landing **L3** of docs/generator-tier-architecture.md, whose gate is this
section. Everything above specifies a suspended MACHINE. Below, `upto` is
CALLED — which allocates a heap object (`EvalsIn.genCall`) — and then
CONSUMED by a `for` statement (`PyStmtTriple.forGen`), and the whole
function `total(n)` gets an arrow-form spec. That is the first theorem in
this repo about a function that consumes a generator.

The four object-level step lemmas below are where the machine meets the
heap. Note the shape they take: `uptoWorld w n k` — the world with the
object in configuration `k` — is `w.heap.push (uptoObj n k)` at EVERY
round, never a growing tower of writes, because `stepIter`'s two writes
land on the slot the allocation just made (`Heap.update_push_size`). -/

/-! ## `upto` as a suspended OBJECT -/

private def yieldE (s : Stmt) : Expr :=
  match s with | .yieldStmt e _ => e | _ => .constant .none nowhere

theorem uptoYield_plan : genPlan uptoYield = .yieldHere (yieldE uptoYield) := rfl
theorem uptoYield_expr : ∃ sp, yieldE uptoYield = .name "i" sp := ⟨_, rfl⟩
theorem uptoBump_plan : genPlan uptoBump = .delegate := rfl

/-- `upto`'s own `FunctionDefn`, projected (never retyped). -/
def uptoF : FunctionDefn :=
  match findFunction gen_lab "upto" with
  | some f => f
  | none => default

theorem uptoF_found : findFunction gen_lab "upto" = some uptoF := rfl

/-- Where `upto` is left suspended after EVERY yield — the `i += 1` that
has not run yet, the loop frame, and the empty block the `while` push left
below it. Independent of how many values it has handed over. -/
def uptoResume : GenCont :=
  [.block [uptoBump], .whileLoop uptoTest uptoLoopBody [], .block []]

private theorem evals_uptoTest (w : World) (n i : Int) :
    EvalsTo gen_lab ⟨w, uptoEnv n i⟩ uptoTest (.bool (decide (i < n))) := by
  obtain ⟨s₄, s₅, s₆, htest⟩ := uptoTest_lit
  rw [htest]
  exact evals_test w n i s₄ s₅ s₆

private theorem evals_uptoYieldE (w : World) (n i : Int) :
    EvalsTo gen_lab ⟨w, uptoEnv n i⟩ (yieldE uptoYield) (.int i) := by
  obtain ⟨sp, h⟩ := uptoYield_expr
  rw [h]
  exact evals_i w (uptoEnv n i) i sp rfl

/-- The FIRST resumption of a freshly created `upto(n)`: run `i = 0`, push
the loop, take the true branch, yield `0`. -/
theorem upto_first (w : World) (n : Int) (h : 0 < n) :
    GenSteps gen_lab ⟨w, uptoEntry n⟩ uptoCont (some (.int 0, uptoResume))
      ⟨w, uptoEnv n 0⟩ := by
  obtain ⟨s₁, s₂, s₃, hassign⟩ := uptoAssign_lit
  rw [uptoCont_eq, uptoBody_split]
  refine GenSteps.silent (st₁ := ⟨w, uptoEnv n 0⟩) (k₁ := .block [uptoWhileS] :: [])
    (genSilent_delegate (s := uptoAssign) (ss := [uptoWhileS]) (k := []) rfl
      (run_at_least (fuel := 8) (st := ⟨w, uptoEntry n⟩) (st' := ⟨w, uptoEnv n 0⟩)
        (by rw [hassign, uptoEntry_eq]; py_simp [uptoEnv]))) ?_
  refine GenSteps.silent
    (k₁ := .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    (genSilent_whileHere (s := uptoWhileS) (ss := ([] : List Stmt)) (k := [])
      uptoWhile_plan) ?_
  refine GenSteps.silent
    (k₁ := .block uptoLoopBody :: .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    (genSilent_whileTrue (evals_uptoTest w n 0)
      (by rw [truthy_bool]; simp [h])) ?_
  rw [uptoResume, uptoLoopBody_split]
  exact genSteps_yieldHere (s := uptoYield) (ss := [uptoBump]) uptoYield_plan
    (evals_uptoYieldE w n 0)

/-- A LATER resumption: `i += 1`, re-test, yield. -/
theorem upto_resume_step (w : World) (n i : Int) (h : i + 1 < n) :
    GenSteps gen_lab ⟨w, uptoEnv n i⟩ uptoResume
      (some (.int (i + 1), uptoResume)) ⟨w, uptoEnv n (i + 1)⟩ := by
  rw [uptoResume]
  refine GenSteps.silent (st₁ := ⟨w, uptoEnv n (i + 1)⟩)
    (k₁ := .block [] :: .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    (genSilent_delegate (s := uptoBump) (ss := ([] : List Stmt)) uptoBump_plan
      (run_at_least (fuel := 8) (st := ⟨w, uptoEnv n i⟩)
        (st' := ⟨w, uptoEnv n (i + 1)⟩)
        (by obtain ⟨s₉, s₁₀, s₁₁, hbump⟩ := uptoBump_lit
            rw [hbump]; py_simp [uptoEnv]))) ?_
  refine GenSteps.silent
    (k₁ := .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    genSilent_blockNil ?_
  refine GenSteps.silent
    (k₁ := .block uptoLoopBody :: .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    (genSilent_whileTrue (evals_uptoTest w n (i + 1))
      (by rw [truthy_bool]; simp [h])) ?_
  rw [uptoLoopBody_split]
  exact genSteps_yieldHere (s := uptoYield) (ss := [uptoBump]) uptoYield_plan
    (evals_uptoYieldE w n (i + 1))

/-- A freshly created `upto(n)` with nothing to give (`n ≤ 0`): the test is
false on the first look, the stack unwinds, the step reports exhaustion. -/
theorem upto_first_done (w : World) (n : Int) (h : ¬ (0 < n)) :
    GenSteps gen_lab ⟨w, uptoEntry n⟩ uptoCont Option.none ⟨w, uptoEnv n 0⟩ := by
  obtain ⟨s₁, s₂, s₃, hassign⟩ := uptoAssign_lit
  rw [uptoCont_eq, uptoBody_split]
  refine GenSteps.silent (st₁ := ⟨w, uptoEnv n 0⟩) (k₁ := .block [uptoWhileS] :: [])
    (genSilent_delegate (s := uptoAssign) (ss := [uptoWhileS]) (k := []) rfl
      (run_at_least (fuel := 8) (st := ⟨w, uptoEntry n⟩) (st' := ⟨w, uptoEnv n 0⟩)
        (by rw [hassign, uptoEntry_eq]; py_simp [uptoEnv]))) ?_
  refine GenSteps.silent
    (k₁ := .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    (genSilent_whileHere (s := uptoWhileS) (ss := ([] : List Stmt)) (k := [])
      uptoWhile_plan) ?_
  refine GenSteps.silent (k₁ := .block [] :: .block [] :: [])
    (genSilent_whileFalse (evals_uptoTest w n 0)
      (by rw [truthy_bool]; simp [h])) ?_
  refine GenSteps.silent (k₁ := .block [] :: []) genSilent_blockNil ?_
  exact GenSteps.silent (k₁ := ([] : GenCont)) genSilent_blockNil genSteps_nil

/-- The LAST resumption: `i += 1` takes the counter to the bound, the test
is false, the stack unwinds, the step reports exhaustion. -/
theorem upto_resume_done (w : World) (n i : Int) (h : ¬ (i + 1 < n)) :
    GenSteps gen_lab ⟨w, uptoEnv n i⟩ uptoResume Option.none
      ⟨w, uptoEnv n (i + 1)⟩ := by
  rw [uptoResume]
  refine GenSteps.silent (st₁ := ⟨w, uptoEnv n (i + 1)⟩)
    (k₁ := .block [] :: .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    (genSilent_delegate (s := uptoBump) (ss := ([] : List Stmt)) uptoBump_plan
      (run_at_least (fuel := 8) (st := ⟨w, uptoEnv n i⟩)
        (st' := ⟨w, uptoEnv n (i + 1)⟩)
        (by obtain ⟨s₉, s₁₀, s₁₁, hbump⟩ := uptoBump_lit
            rw [hbump]; py_simp [uptoEnv]))) ?_
  refine GenSteps.silent
    (k₁ := .whileLoop uptoTest uptoLoopBody [] :: .block [] :: [])
    genSilent_blockNil ?_
  refine GenSteps.silent (k₁ := .block [] :: .block [] :: [])
    (genSilent_whileFalse (evals_uptoTest w n (i + 1))
      (by rw [truthy_bool]; simp [h])) ?_
  refine GenSteps.silent (k₁ := .block [] :: []) genSilent_blockNil ?_
  exact GenSteps.silent (k₁ := ([] : GenCont)) genSilent_blockNil genSteps_nil

/-! ## …and as a heap OBJECT

`uptoObj n k` is the object after `k` values have been handed over: the
CREATED frame at `k = 0`, the suspended one afterwards. `uptoWorld` puts it
where `EvalsIn.genCall` puts it — at the end of the heap — and the two
`stepIter` writes keep it there. -/

/-- The object after `k` yields. -/
def uptoObj (n : Int) : Nat → Obj
  | 0 => .generator "upto" (uptoEntry n) uptoCont .created
  | k + 1 => .generator "upto" (uptoEnv n (k : Int)) uptoResume .suspended

/-- The world holding it, at the address a fresh call answers. -/
def uptoWorld (w : World) (n : Int) (k : Nat) : World :=
  { w with heap := w.heap.push (uptoObj n k) }

/-- The world after exhaustion: CLOSED, continuation dropped (which is what
makes every later consumer see zero values — `gen_lab.drain_then_more`). -/
def uptoWorldDone (w : World) (n : Int) (k : Nat) : World :=
  { w with heap := w.heap.push (.generator "upto" (uptoEnv n (k : Int)) [] .closed) }

/-- **One step of the OBJECT**: at configuration `k` with values left, it
yields `k` and moves to configuration `k + 1`. `IterSteps.pureStep` does
the heap bookkeeping — this generator's own resumption touches only its
frame, so its two `stepIter` writes collapse onto the slot the allocation
made. -/
theorem upto_iter (w : World) (n : Int) (k : Nat) (h : (k : Int) < n) :
    IterSteps gen_lab (uptoWorld w n k) w.heap.size (some (.int (k : Int)))
      (uptoWorld w n (k + 1)) := by
  cases k with
  | zero =>
    exact IterSteps.pureStep (Heap.get?_push_size _ _) (Or.inl rfl)
      (Heap.update_push_size _ _ _) (upto_first _ n (by exact_mod_cast h))
      (Heap.update_push_size _ _ _)
  | succ j =>
    exact IterSteps.pureStep (Heap.get?_push_size _ _) (Or.inr rfl)
      (Heap.update_push_size _ _ _)
      (upto_resume_step _ n (j : Int) (by omega)) (Heap.update_push_size _ _ _)

/-- **The exhausting step**: at configuration `k` with nothing left, the
object reports `none` and is CLOSED — continuation dropped, which is what
makes every later consumer see zero values. -/
theorem upto_iter_done (w : World) (n : Int) (k : Nat) (h : ¬ ((k : Int) < n)) :
    IterSteps gen_lab (uptoWorld w n k) w.heap.size Option.none
      (uptoWorldDone w n k) := by
  cases k with
  | zero =>
    exact IterSteps.pureDone (Heap.get?_push_size _ _) (Or.inl rfl)
      (Heap.update_push_size _ _ _) (upto_first_done _ n (by exact_mod_cast h))
      (Heap.update_push_size _ _ _)
  | succ j =>
    exact IterSteps.pureDone (Heap.get?_push_size _ _) (Or.inr rfl)
      (Heap.update_push_size _ _ _)
      (upto_resume_done _ n (j : Int) (by omega)) (Heap.update_push_size _ _ _)

/-! ## `total(n)`: a function that CONSUMES a generator

```python
def total(n):
    s = 0
    for x in upto(n):
        s += x
    return s
```

Everything L3 built meets here: the call ALLOCATES (`EvalsIn.genCall`), the
`for` STEPS (`PyStmtTriple.forGen`), and the result is an ARROW-form spec —
the first in this repo for a function whose meaning runs through a
generator. Symbolic in `n`; the `total(5) = 10` differential row is an
instance of it. -/

/-- `total`'s own `FunctionDefn` and body, projected (never retyped). -/
def totalF : FunctionDefn :=
  match findFunction gen_lab "total" with
  | some f => f
  | none => default

/-- `total`'s body as the call bridge presents it. -/
def totalBody : List Stmt := totalF.body.toList

private def stmt2 (ss : List Stmt) : Stmt :=
  match ss with | _ :: _ :: s :: _ => s | _ => .pass nowhere

private def iterOf (s : Stmt) : Expr :=
  match s with | .forStmt _ it _ _ _ => it | _ => .constant .none nowhere

private def targetOf (s : Stmt) : Expr :=
  match s with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere

private def forBodyOf (s : Stmt) : Array Stmt :=
  match s with | .forStmt _ _ b _ _ => b | _ => #[]

/-- `s = 0`. -/
def totalAssign : Stmt := stmt0 totalBody
/-- `for x in upto(n): …`. -/
def totalFor : Stmt := stmt1 totalBody
/-- `return s`. -/
def totalRet : Stmt := stmt2 totalBody
/-- `upto(n)` — the CALL that allocates. -/
def totalIter : Expr := iterOf totalFor
/-- `x`. -/
def totalTarget : Expr := targetOf totalFor
/-- `s += x`. -/
def totalLoopBody : Array Stmt := forBodyOf totalFor

theorem totalBody_split : totalBody = [totalAssign, totalFor, totalRet] := rfl

theorem totalFor_lit :
    ∃ sp, totalFor = .forStmt totalTarget totalIter totalLoopBody #[] sp := ⟨_, rfl⟩

theorem totalIter_lit :
    ∃ s₁ s₂ s₃,
      totalIter = .call (.name "upto" s₁) #[.name "n" s₂] #[] Option.none s₃ :=
  ⟨_, _, _, rfl⟩

theorem totalTarget_lit : ∃ sp, totalTarget = .name "x" sp := ⟨_, rfl⟩

theorem totalRet_lit : ∃ s₁ s₂, totalRet = .ret (some (.name "s" s₁)) s₂ :=
  ⟨_, _, rfl⟩

theorem totalAssign_lit :
    ∃ s₁ s₂ s₃, totalAssign = .assign #[.name "s" s₁] (.constant (.int 0) s₂) s₃ :=
  ⟨_, _, _, rfl⟩

theorem totalLoopBody_lit :
    ∃ s₁ s₂ s₃,
      totalLoopBody = #[.augAssign (.name "s" s₁) .add (.name "x" s₂) s₃] :=
  ⟨_, _, _, rfl⟩

/-- The object a call to `upto` allocates IS the configuration the step
lemmas speak about — `genObj`'s stored continuation is `[.block body]`,
which is `uptoCont`. -/
theorem genObj_upto (n : Int) : genObj "upto" uptoF #[.int n] = uptoObj n 0 := rfl

/-- The sum `total` accumulates, recursively (the Python lane is core-only:
no closed form, no `ring`). -/
def sumUpto : Nat → Int
  | 0 => 0
  | k + 1 => sumUpto k + (k : Int)

/-- The values not yet handed over, spec-side. -/
def natsFrom (i : Nat) : Nat → List Nat
  | 0 => []
  | c + 1 => i :: natsFrom (i + 1) c

/-- `total`'s frame after `k` values: `x` does not exist until the loop
binds it the first time, which is the one place the state of a generator
loop is not uniform in `k`. -/
def totalLocals (N : Nat) : Nat → REnv
  | 0 => [("n", .int (N : Int)), ("s", .int 0)]
  | k + 1 =>
    [("n", .int (N : Int)), ("s", .int (sumUpto (k + 1))), ("x", .int (k : Int))]

/-- …and with the loop target just bound. -/
def totalLocalsX (N k : Nat) : REnv :=
  [("n", .int (N : Int)), ("s", .int (sumUpto k)), ("x", .int (k : Int))]

theorem totalLocals_set (N k : Nat) :
    Env.set (totalLocals N k) "x" (.int (k : Int)) = totalLocalsX N k := by
  cases k <;> rfl

private theorem totalLocals_s (N : Nat) :
    Env.lookup (totalLocals N N) "s" = some (.int (sumUpto N)) := by
  cases N <;> rfl

private theorem evals_name (w : World) (env : REnv) (x : String) (v : RVal)
    (sp : Span) (henv : Env.lookup env x = some v) :
    EvalsTo gen_lab ⟨w, env⟩ (.name x sp) v := by
  refine EvalsTo.of_eval (fuel := 4) ?_
  py_simp [henv]

/-- **The loop invariant**: `k` values consumed and `c` to go, the OBJECT in
configuration `k`, the frame carrying the running sum. The generator's state
lives in the invariant — which is what makes the rule sound without a
heap-stability side condition. -/
abbrev totalInv (w : World) (N : Nat) (rest : List Nat) (st : FrameState) : Prop :=
  ∃ k c : Nat, k + c = N ∧ rest = natsFrom k c ∧
    st = ⟨uptoWorld w (N : Int) k, totalLocals N k⟩

/-- `total`'s whole body, as a triple over an arbitrary entry world. -/
theorem total_body_triple (w : World) (N : Nat) :
    PyTriple gen_lab (fun st => st = ⟨w, [("n", .int (N : Int))]⟩) totalBody
      (.ofRet fun rv _ => rv = RVal.int (sumUpto N)) := by
  obtain ⟨s₁, s₂, s₃, hassign⟩ := totalAssign_lit
  obtain ⟨spf, hfor⟩ := totalFor_lit
  obtain ⟨r₁, r₂, hret⟩ := totalRet_lit
  obtain ⟨t₁, htarget⟩ := totalTarget_lit
  obtain ⟨c₁, c₂, c₃, hiterlit⟩ := totalIter_lit
  obtain ⟨b₁, b₂, b₃, hloop⟩ := totalLoopBody_lit
  rw [totalBody_split]
  -- `s = 0`
  refine PyTriple.run_seq (f := 8) (pre := [totalAssign])
    (rest := [totalFor, totalRet]) (E' := ⟨w, totalLocals N 0⟩) ?_ ?_
  · rw [hassign]
    py_simp [totalLocals]
  refine PyTriple.seq (R := fun st => ∃ w', st = ⟨w', totalLocals N N⟩) ?_ ?_
  · -- **the generator `for`**
    rw [hfor]
    refine PyStmtTriple.forGen (α := Nat) (a := w.heap.size)
      (fun i => .int (i : Int)) (totalInv w N) (natsFrom 0 N) rfl ?_ ?_ ?_
    · -- the call allocates, and what it allocates is `uptoObj n 0`
      rintro st rfl
      refine ⟨⟨uptoWorld w (N : Int) 0, totalLocals N 0⟩, "upto", uptoEntry (N : Int),
        uptoCont, .created, ?_, Heap.get?_push_size _ _, ⟨0, N, by omega, rfl, rfl⟩⟩
      rw [hiterlit]
      have hcall := EvalsIn.genCall (m := gen_lab) (st := ⟨w, totalLocals N 0⟩)
        (fname := "upto") (f := uptoF) (argEs := #[.name "n" c₂])
        (vs := [.int (N : Int)]) (sp := c₁) (sp' := c₃)
        rfl rfl rfl rfl uptoF_found rfl rfl rfl rfl
        (EvalsToList.cons (evals_name w (totalLocals N 0) "n" (.int (N : Int)) c₂ rfl)
          EvalsToList.nil)
      simpa [uptoWorld, genObj_upto] using hcall
    · -- exhaustion: nothing left, so the object must report `none`
      intro st hI
      obtain ⟨k, c, hkc, hrest, hst⟩ := hI
      cases c with
      | succ c' => simp [natsFrom] at hrest
      | zero =>
        have hkN : k = N := by omega
        rw [hkN] at hst
        subst hst
        exact ⟨uptoWorldDone w (N : Int) N,
          upto_iter_done w (N : Int) N (by omega), _, rfl⟩
    · -- one value: the object yields it, the body adds it
      intro x rest st hI
      obtain ⟨k, c, hkc, hrest, hst⟩ := hI
      cases c with
      | zero => simp [natsFrom] at hrest
      | succ c' =>
        rw [natsFrom] at hrest
        obtain ⟨hx, hr⟩ : x = k ∧ rest = natsFrom (k + 1) c' := by
          simpa using hrest
        subst hst
        subst hr
        rw [hx]
        refine ⟨uptoWorld w (N : Int) (k + 1),
          Env.set (totalLocals N k) "x" (.int (k : Int)),
          upto_iter w (N : Int) k (by omega), by rw [htarget]; rfl, ?_⟩
        have hrun : execStmts gen_lab 8
            (⟨uptoWorld w (N : Int) (k + 1), totalLocalsX N k⟩ : FrameState)
            totalLoopBody.toList
            = .ok ⟨uptoWorld w (N : Int) (k + 1), totalLocals N (k + 1)⟩ .next := by
          rw [hloop]
          py_simp [totalLocalsX, totalLocals, sumUpto]
        refine PyTriple.of_exec ?_
        rintro st' rfl
        refine ⟨8, ?_⟩
        rw [totalLocals_set, hrun]
        exact ⟨k + 1, c', by omega, rfl, rfl⟩
  · -- `return s`
    refine PyTriple.single ?_
    rw [hret]
    refine PyStmtTriple.retExpr (v := .int (sumUpto N)) ?_ ?_
    · rintro st ⟨w', rfl⟩
      exact evals_name w' (totalLocals N N) "s" (.int (sumUpto N)) r₁ (totalLocals_s N)
    · rintro st ⟨w', rfl⟩
      rfl

/-- **`total(n)` = 0 + 1 + ⋯ + (n−1)** — the first arrow-form spec in this
repo for a function that consumes a generator, symbolic in `n`.

Every L3 object is on the path: `EvalsIn.genCall` turns `upto(n)` into a
heap value whose remaining output is known, `PyStmtTriple.forGen` steps it
with a remainder-indexed invariant that carries the object, and the
per-round `IterSteps` obligations are `upto_iter`/`upto_iter_done`. -/
theorem total_calls (N : Nat) :
    CallsTo gen_lab "total" #[.int (N : Int)] (.int (sumUpto N)) :=
  PyTriple.callsTo_ofRet (f := totalF) rfl rfl rfl rfl rfl
    (total_body_triple _ N)

/-! ### Non-vacuity: the symbolic theorem against the differential row -/

#guard sumUpto 5 == 10
#guard callFunction gen_lab "total" #[.int 5] 4096 == .ok (.int 10)

/-- The `total(5) = 10` row's content as a theorem — an INSTANCE of the
symbolic one, with no interpreter run elaborated. -/
theorem total5_calls : CallsTo gen_lab "total" #[.int 5] (.int 10) := by
  have h := total_calls 5
  rw [show ((5 : Nat) : Int) = 5 from rfl,
    show sumUpto 5 = 10 from by first | rfl | decide] at h
  exact h

/-! ## `two_phase(n)`: ONE object, two consumers — and the LAZY half

```python
def two_phase(n):
    g = upto(n)
    a = -1
    for x in g:
        a = x
        break
    b = -1
    for y in g:
        b = y
        break
    return a * 100 + b
```

`total` drains its generator, so its invariant is satisfiable at the empty
remainder and the exhaustion obligation does real work. This theorem is the
other half of the rule, the one VCGen.lean's section header claims and
nothing exercised until now: **both loops carry an invariant that is `False`
at the empty remainder.** Each escapes by `break` after one value, so the
`hexit` obligation — "at the empty remainder the object reports exhaustion"
— is discharged VACUOUSLY, and the generator is never asked to finish. That
is exactly how an infinite generator would be consumed; `upto(n)` is used
here because it is the object already specified above.

The other thing it pins is IDENTITY. The second loop's `hiter` observes the
SAME address the first loop left behind, in configuration 1 rather than 0,
which is why `b = 1` and not `0`. gen_lab's docstring calls that claim
"`break` SUSPENDS" and had it only as a differential row; it is a theorem
now, symbolically in `n` for every `n ≥ 2`.

`g = upto(n)` is the statement the pure assignment rule cannot bind (the
RHS allocates), so it goes through `PyStmtTriple.assignNameIn`. -/

/-- `two_phase`'s own `FunctionDefn` and body, projected (never retyped). -/
def twoPhaseF : FunctionDefn :=
  match findFunction gen_lab "two_phase" with
  | some f => f
  | none => default

/-- `two_phase`'s body as the call bridge presents it. -/
def twoPhaseBody : List Stmt := twoPhaseF.body.toList

private def stmt3 (ss : List Stmt) : Stmt :=
  match ss with | _ :: _ :: _ :: s :: _ => s | _ => .pass nowhere

private def stmt4 (ss : List Stmt) : Stmt :=
  match ss with | _ :: _ :: _ :: _ :: s :: _ => s | _ => .pass nowhere

private def stmt5 (ss : List Stmt) : Stmt :=
  match ss with | _ :: _ :: _ :: _ :: _ :: s :: _ => s | _ => .pass nowhere

private def rhsOf (s : Stmt) : Expr :=
  match s with | .assign _ e _ => e | _ => .constant .none nowhere

private def retE (s : Stmt) : Expr :=
  match s with | .ret (some e) _ => e | _ => .constant .none nowhere

/-- `g = upto(n)` — the statement that ALLOCATES. -/
def tpBindG : Stmt := stmt0 twoPhaseBody
/-- `a = -1`. -/
def tpInitA : Stmt := stmt1 twoPhaseBody
/-- `for x in g: a = x; break`. -/
def tpForX : Stmt := stmt2 twoPhaseBody
/-- `b = -1`. -/
def tpInitB : Stmt := stmt3 twoPhaseBody
/-- `for y in g: b = y; break` — the SECOND consumer of the same object. -/
def tpForY : Stmt := stmt4 twoPhaseBody
/-- `return a * 100 + b`. -/
def tpRet : Stmt := stmt5 twoPhaseBody

/-- `upto(n)`. -/
def tpCall : Expr := rhsOf tpBindG
/-- `g`, in the first loop's iterable position. -/
def tpIterX : Expr := iterOf tpForX
/-- `x`. -/
def tpTargetX : Expr := targetOf tpForX
/-- `a = x; break`. -/
def tpBodyX : Array Stmt := forBodyOf tpForX
/-- `g` again — the same name, and therefore the same object. -/
def tpIterY : Expr := iterOf tpForY
/-- `y`. -/
def tpTargetY : Expr := targetOf tpForY
/-- `b = y; break`. -/
def tpBodyY : Array Stmt := forBodyOf tpForY
/-- `a * 100 + b`. -/
def tpRetE : Expr := retE tpRet

theorem twoPhaseBody_split :
    twoPhaseBody = [tpBindG, tpInitA, tpForX, tpInitB, tpForY, tpRet] := rfl

theorem tpBindG_lit : ∃ s₁ s₂, tpBindG = .assign #[.name "g" s₁] tpCall s₂ :=
  ⟨_, _, rfl⟩

theorem tpCall_lit :
    ∃ s₁ s₂ s₃,
      tpCall = .call (.name "upto" s₁) #[.name "n" s₂] #[] Option.none s₃ :=
  ⟨_, _, _, rfl⟩

theorem tpInitA_lit :
    ∃ s₁ s₂ s₃ s₄,
      tpInitA = .assign #[.name "a" s₁] (.unaryOp .usub (.constant (.int 1) s₂) s₃) s₄ :=
  ⟨_, _, _, _, rfl⟩

theorem tpInitB_lit :
    ∃ s₁ s₂ s₃ s₄,
      tpInitB = .assign #[.name "b" s₁] (.unaryOp .usub (.constant (.int 1) s₂) s₃) s₄ :=
  ⟨_, _, _, _, rfl⟩

theorem tpForX_lit :
    ∃ sp, tpForX = .forStmt tpTargetX tpIterX tpBodyX #[] sp := ⟨_, rfl⟩

theorem tpForY_lit :
    ∃ sp, tpForY = .forStmt tpTargetY tpIterY tpBodyY #[] sp := ⟨_, rfl⟩

theorem tpIterX_lit : ∃ sp, tpIterX = .name "g" sp := ⟨_, rfl⟩
theorem tpIterY_lit : ∃ sp, tpIterY = .name "g" sp := ⟨_, rfl⟩
theorem tpTargetX_lit : ∃ sp, tpTargetX = .name "x" sp := ⟨_, rfl⟩
theorem tpTargetY_lit : ∃ sp, tpTargetY = .name "y" sp := ⟨_, rfl⟩

theorem tpBodyX_lit :
    ∃ s₁ s₂ s₃ s₄,
      tpBodyX = #[.assign #[.name "a" s₁] (.name "x" s₂) s₃, .brk s₄] :=
  ⟨_, _, _, _, rfl⟩

theorem tpBodyY_lit :
    ∃ s₁ s₂ s₃ s₄,
      tpBodyY = #[.assign #[.name "b" s₁] (.name "y" s₂) s₃, .brk s₄] :=
  ⟨_, _, _, _, rfl⟩

theorem tpRet_lit : ∃ sp, tpRet = .ret (some tpRetE) sp := ⟨_, rfl⟩

theorem tpRetE_lit :
    ∃ s₁ s₂ s₃ s₄ s₅,
      tpRetE = .binOp (.binOp (.name "a" s₁) .mult (.constant (.int 100) s₂) s₃)
        .add (.name "b" s₄) s₅ :=
  ⟨_, _, _, _, _, rfl⟩

/-- `two_phase`'s frame at the seven points the proof names: after
`g = upto(n)` (0), after `a = -1` (1), with `x` bound (2), after `a = x`
(3), after `b = -1` (4), with `y` bound (5), after `b = y` (6). The
generator address `A` is in every one of them — one object, two
consumers. -/
def tpEnv (N : Nat) (A : Addr) : Nat → REnv
  | 0 => [("n", .int (N : Int)), ("g", .ref A)]
  | 1 => [("n", .int (N : Int)), ("g", .ref A), ("a", .int (-1))]
  | 2 => [("n", .int (N : Int)), ("g", .ref A), ("a", .int (-1)), ("x", .int 0)]
  | 3 => [("n", .int (N : Int)), ("g", .ref A), ("a", .int 0), ("x", .int 0)]
  | 4 => [("n", .int (N : Int)), ("g", .ref A), ("a", .int 0), ("x", .int 0),
          ("b", .int (-1))]
  | 5 => [("n", .int (N : Int)), ("g", .ref A), ("a", .int 0), ("x", .int 0),
          ("b", .int (-1)), ("y", .int 1)]
  | 6 => [("n", .int (N : Int)), ("g", .ref A), ("a", .int 0), ("x", .int 0),
          ("b", .int 1), ("y", .int 1)]
  | _ => []

/-- **The first loop's invariant, and the point of the theorem**: at the
empty remainder it is `False` — `[] = [0]` has no proof. So the exhaustion
obligation is discharged vacuously and the loop never asks `upto(n)` to
finish; it takes one value and escapes. -/
abbrev tpInv1 (w : World) (N : Nat) (rest : List Nat) (st : FrameState) : Prop :=
  rest = [0] ∧ st = ⟨uptoWorld w (N : Int) 0, tpEnv N w.heap.size 1⟩

/-- The second loop's invariant — the same shape, over the object in
configuration ONE. That index is the whole `break`-suspends claim: the
first loop left the object there, and this loop starts from it. -/
abbrev tpInv2 (w : World) (N : Nat) (rest : List Nat) (st : FrameState) : Prop :=
  rest = [1] ∧ st = ⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 4⟩

/-- `two_phase`'s whole body, as a triple over an arbitrary entry world. -/
theorem two_phase_body_triple (w : World) (N : Nat) (hN : 2 ≤ N) :
    PyTriple gen_lab (fun st => st = ⟨w, [("n", .int (N : Int))]⟩) twoPhaseBody
      (.ofRet fun rv _ => rv = RVal.int 1) := by
  obtain ⟨g₁, g₂, hbind⟩ := tpBindG_lit
  obtain ⟨c₁, c₂, c₃, hcall⟩ := tpCall_lit
  obtain ⟨a₁, a₂, a₃, a₄, hinitA⟩ := tpInitA_lit
  obtain ⟨b₁, b₂, b₃, b₄, hinitB⟩ := tpInitB_lit
  obtain ⟨fx, hforX⟩ := tpForX_lit
  obtain ⟨fy, hforY⟩ := tpForY_lit
  obtain ⟨ix, hiterX⟩ := tpIterX_lit
  obtain ⟨iy, hiterY⟩ := tpIterY_lit
  obtain ⟨tx, htargetX⟩ := tpTargetX_lit
  obtain ⟨ty, htargetY⟩ := tpTargetY_lit
  obtain ⟨x₁, x₂, x₃, x₄, hbodyX⟩ := tpBodyX_lit
  obtain ⟨y₁, y₂, y₃, y₄, hbodyY⟩ := tpBodyY_lit
  obtain ⟨r₀, hret⟩ := tpRet_lit
  obtain ⟨r₁, r₂, r₃, r₄, r₅, hretE⟩ := tpRetE_lit
  rw [twoPhaseBody_split]
  -- `g = upto(n)` — the RHS ALLOCATES, so the pure assign rule cannot bind it
  refine PyTriple.seq
    (R := fun st => st = (⟨uptoWorld w (N : Int) 0, tpEnv N w.heap.size 0⟩ : FrameState))
    ?_ ?_
  · rw [hbind]
    refine PyStmtTriple.assignNameIn ?_
    rintro st rfl
    refine ⟨.ref w.heap.size,
      ⟨uptoWorld w (N : Int) 0, [("n", .int (N : Int))]⟩, ?_, rfl⟩
    rw [hcall]
    have hev := EvalsIn.genCall (m := gen_lab)
      (st := (⟨w, [("n", .int (N : Int))]⟩ : FrameState))
      (fname := "upto") (f := uptoF) (argEs := #[.name "n" c₂])
      (vs := [.int (N : Int)]) (sp := c₁) (sp' := c₃)
      rfl rfl rfl rfl uptoF_found rfl rfl rfl rfl
      (EvalsToList.cons
        (evals_name w [("n", .int (N : Int))] "n" (.int (N : Int)) c₂ rfl)
        EvalsToList.nil)
    simpa [uptoWorld, genObj_upto] using hev
  -- `a = -1`
  refine PyTriple.run_seq (f := 8) (pre := [tpInitA])
    (rest := [tpForX, tpInitB, tpForY, tpRet])
    (E' := ⟨uptoWorld w (N : Int) 0, tpEnv N w.heap.size 1⟩) ?_ ?_
  · rw [hinitA]
    py_simp [tpEnv]
  refine PyTriple.seq
    (R := fun st => st = (⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 3⟩ : FrameState))
    ?_ ?_
  · -- the FIRST loop: one value, then `break`
    rw [hforX]
    refine PyStmtTriple.forGen (α := Nat) (a := w.heap.size)
      (fun i => .int (i : Int)) (tpInv1 w N) [0] rfl ?_ ?_ ?_
    · rintro st rfl
      refine ⟨⟨uptoWorld w (N : Int) 0, tpEnv N w.heap.size 1⟩, "upto",
        uptoEntry (N : Int), uptoCont, .created, ?_, Heap.get?_push_size _ _,
        rfl, rfl⟩
      rw [hiterX]
      exact EvalsIn.of_evalsTo
        (evals_name _ (tpEnv N w.heap.size 1) "g" (.ref w.heap.size) ix rfl)
    · -- VACUOUS: the invariant is `False` at the empty remainder
      rintro st ⟨hnil, -⟩
      exact absurd hnil (by simp)
    · rintro x rest st ⟨hcons, hst⟩
      obtain ⟨rfl, rfl⟩ : x = 0 ∧ rest = [] := by simpa using hcons
      subst hst
      refine ⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 2,
        upto_iter w (N : Int) 0 (by omega), by rw [htargetX]; rfl, ?_⟩
      have hrun : execStmts gen_lab 8
          (⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 2⟩ : FrameState)
          tpBodyX.toList
          = .ok ⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 3⟩ .brk := by
        rw [hbodyX]
        py_simp [tpEnv]
      refine PyTriple.of_exec ?_
      rintro st' rfl
      exact ⟨8, by rw [hrun]; rfl⟩
  -- `b = -1`
  refine PyTriple.run_seq (f := 8) (pre := [tpInitB]) (rest := [tpForY, tpRet])
    (E' := ⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 4⟩) ?_ ?_
  · rw [hinitB]
    py_simp [tpEnv]
  refine PyTriple.seq
    (R := fun st => st = (⟨uptoWorld w (N : Int) 2, tpEnv N w.heap.size 6⟩ : FrameState))
    ?_ ?_
  · -- the SECOND loop: the SAME object, resumed where the first left it
    rw [hforY]
    refine PyStmtTriple.forGen (α := Nat) (a := w.heap.size)
      (fun i => .int (i : Int)) (tpInv2 w N) [1] rfl ?_ ?_ ?_
    · rintro st rfl
      refine ⟨⟨uptoWorld w (N : Int) 1, tpEnv N w.heap.size 4⟩, "upto",
        uptoEnv (N : Int) 0, uptoResume, .suspended, ?_, Heap.get?_push_size _ _,
        rfl, rfl⟩
      rw [hiterY]
      exact EvalsIn.of_evalsTo
        (evals_name _ (tpEnv N w.heap.size 4) "g" (.ref w.heap.size) iy rfl)
    · rintro st ⟨hnil, -⟩
      exact absurd hnil (by simp)
    · rintro y rest st ⟨hcons, hst⟩
      obtain ⟨rfl, rfl⟩ : y = 1 ∧ rest = [] := by simpa using hcons
      subst hst
      refine ⟨uptoWorld w (N : Int) 2, tpEnv N w.heap.size 5,
        upto_iter w (N : Int) 1 (by omega), by rw [htargetY]; rfl, ?_⟩
      have hrun : execStmts gen_lab 8
          (⟨uptoWorld w (N : Int) 2, tpEnv N w.heap.size 5⟩ : FrameState)
          tpBodyY.toList
          = .ok ⟨uptoWorld w (N : Int) 2, tpEnv N w.heap.size 6⟩ .brk := by
        rw [hbodyY]
        py_simp [tpEnv]
      refine PyTriple.of_exec ?_
      rintro st' rfl
      exact ⟨8, by rw [hrun]; rfl⟩
  -- `return a * 100 + b`
  refine PyTriple.single ?_
  rw [hret]
  refine PyStmtTriple.retExpr (v := .int 1) ?_ ?_
  · rintro st rfl
    rw [hretE]
    refine EvalsTo.of_eval (fuel := 8) ?_
    py_simp [tpEnv]
  · rintro st rfl
    rfl

/-- **`two_phase(n) = 1` for every `n ≥ 2`** — the first theorem in this repo
about a generator that is ABANDONED and then RESUMED. Both loops carry an
invariant that is `False` at the empty remainder (`PyStmtTriple.forGen`'s
lazy half, VCGen.lean §L3), and the second loop's `hiter` reads the object
at configuration 1, which is `break`-suspends as a theorem. -/
theorem two_phase_calls (N : Nat) (hN : 2 ≤ N) :
    CallsTo gen_lab "two_phase" #[.int (N : Int)] (.int 1) :=
  PyTriple.callsTo_ofRet (f := twoPhaseF) rfl rfl rfl rfl rfl
    (two_phase_body_triple _ N hN)

/-! ### Non-vacuity: the symbolic theorem against the differential row -/

#guard callFunction gen_lab "two_phase" #[.int 5] 4096 == .ok (.int 1)

/-- The `two_phase(5) = 1` row's content as a theorem — an INSTANCE of the
symbolic one, with no interpreter run elaborated. -/
theorem two_phase5_calls : CallsTo gen_lab "two_phase" #[.int 5] (.int 1) := by
  have h := two_phase_calls 5 (by omega)
  rwa [show ((5 : Nat) : Int) = 5 from rfl] at h

end Examples.python.gen_lab.proof
