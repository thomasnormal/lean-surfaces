import LeanModels.Python.VC2

/-!
# py_vcgen layer-2 tests: the recursion pattern and the `@[py_spec]` registry

The recursion scheme (the pattern Acceptance applies to `fib`-shaped gallery
functions), proved end-to-end on a hand-built `fact` module:

* **Induct on the MATH variable** (house rule — never on fuel): the goal is
  the arrow-form spec `CallsTo factM "fact" #[.int n] (.int (factorial n))`.
* **Bridge into the triple layer** per case with `PyTriple.callsTo_ofRet`
  (VC2.lean); the `findFunction`/`argsOk`/`localsOk`/arity guards close by
  `rfl` at the literal module.
* **The IH is a local `CallsTo` fact** at the smaller argument, consumed by
  `PyTriple.call` exactly as a registered `@[py_spec]` lemma would be — the
  call rules take the callee fact as an ordinary hypothesis, so recursion
  needs no fixpoint rule and no attribute plumbing: `CallsTo`'s `∃ fuel`
  ties the knot, `fuelMono` splices the runs.
* Leaf `EvalsTo` obligations close by `rfl` where the run is
  constructor-concrete, by `py_simp [factM, factFn]` where a symbolic
  branch or a `Nat`→`Int` cast is involved.

`fact_plus_one_spec` is the non-recursive half of the story: its callee fact
is the `@[py_spec]`-registered `fact_spec` itself, consumed through the same
`PyTriple.call` — registered lemmas and local hypotheses are
interchangeable, exactly as the registry design (VC2.lean) prescribes. The
`#eval` check pins the registry round-trip (`Lean.labelled`), and the final
`example` pins the backward bridge (`CallsTo.toTriple`).
-/

namespace LeanModels.Python.VCTests

private def sp : Span := default

/-- Spec-side factorial (core Lean has none; local to the tests). -/
private def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#guard factorial 5 = 120

/-- `def fact(n): if n <= 0: return 1 ⏎ r = fact(n - 1) ⏎ return n * r` —
the minimal recursive function with the recursive call in `x = f(e)`
position (what `PyStmtTriple.call` matches). -/
private def factFn : FunctionDefn where
  name := "fact"
  params := #[⟨"n", sp⟩]
  argsOk := true
  body := #[
    .ifStmt (.compare (.name "n" sp) #[.ltE] #[.constant (.int 0) sp] sp)
      #[.ret (some (.constant (.int 1) sp)) sp] #[] sp,
    .assign #[.name "r" sp]
      (.call (.name "fact" sp)
        #[.binOp (.name "n" sp) .sub (.constant (.int 1) sp) sp] Option.none sp) sp,
    .ret (some (.binOp (.name "n" sp) .mult (.name "r" sp) sp)) sp]
  span := sp

/-- `def fact_plus_one(n): y = fact(n) ⏎ return y + 1` — a non-recursive
caller whose callee spec comes from the `@[py_spec]` registry. -/
private def factPlusOneFn : FunctionDefn where
  name := "fact_plus_one"
  params := #[⟨"n", sp⟩]
  argsOk := true
  body := #[
    .assign #[.name "y" sp]
      (.call (.name "fact" sp) #[.name "n" sp] Option.none sp) sp,
    .ret (some (.binOp (.name "y" sp) .add (.constant (.int 1) sp) sp)) sp]
  span := sp

private def factM : Module := { functions := #[factFn, factPlusOneFn], topLevel := #[] }

#py_check factM.fact(5) = 120
#py_check factM.fact_plus_one(4) = 25

/-- **The recursion pattern**: `fact(n) ==> n!` by induction on `n` (the
math variable). Base case: one concrete run. Step case: bridge to the
whole-body triple (`PyTriple.callsTo_ofRet`), walk the body with
`.seq`/`.ifStmt`/`.call`/`.ret`, and feed the induction hypothesis — a
*local* `CallsTo` fact at `k` — to `PyTriple.call` where a registered spec
would otherwise go. -/
@[py_spec] theorem fact_spec (n : Nat) :
    CallsTo factM "fact" #[.int n] (.int (factorial n)) := by
  induction n with
  | zero =>
    exact ⟨8, by py_simp [callFunction, factM, factFn, factPlusOneFn, factorial]⟩
  | succ k ih =>
    refine PyTriple.callsTo_ofRet (f := factFn) rfl rfl rfl rfl ?_
    refine PyTriple.seq (R := fun env => env = [("n", .int (k + 1 : Nat))])
      (.ifStmt (Pt := fun _ => False)
        (Pf := fun env => env = [("n", .int (k + 1 : Nat))])
        ?_ (fun _ h => h.elim) (.nil fun _ h => h)) ?_
    · -- the test `n <= 0` is false at n = k + 1
      rintro env rfl
      refine ⟨.bool false, .of_eval (fuel := 4) ?_,
        fun h => by simp [truthy] at h, fun _ => rfl⟩
      py_simp [factM, factFn]
    · -- r = fact(n - 1): the IH is the callee fact
      refine PyTriple.call
        (R := fun env =>
          env = [("n", .int (k + 1 : Nat)), ("r", .int (factorial k))])
        ?_ (.single (.ret ?_))
      · rintro env rfl
        exact ⟨rfl, [.int (k : Nat)], .int (factorial k),
          .cons (.of_eval (fuel := 3) (by py_simp [factM, factFn])) .nil, ih, rfl⟩
      · -- return n * r
        rintro env rfl
        refine ⟨.int ((↑(k + 1) : Int) * ↑(factorial k)),
          .of_eval (fuel := 3) rfl, ?_⟩
        simp [PyPost.ofRet, factorial, Int.natCast_mul]

/-- Consuming a REGISTERED spec: `fact_plus_one(n) ==> n! + 1`, with
`fact_spec` (the `@[py_spec]` lemma above) as the callee fact of
`PyTriple.call` — the exact shape the future vcgen produces after a
registry lookup. -/
theorem fact_plus_one_spec (n : Nat) :
    CallsTo factM "fact_plus_one" #[.int n] (.int (factorial n + 1)) := by
  refine PyTriple.callsTo_ofRet (f := factPlusOneFn) rfl rfl rfl rfl ?_
  refine PyTriple.call
    (R := fun env => env = [("n", .int n), ("y", .int (factorial n))])
    ?_ (.single (.ret ?_))
  · rintro env rfl
    exact ⟨rfl, [.int (n : Nat)], .int (factorial n),
      .cons (.of_eval (fuel := 2) rfl) .nil, fact_spec n, rfl⟩
  · rintro env rfl
    refine ⟨.int ((↑(factorial n) : Int) + 1), .of_eval (fuel := 3) rfl, ?_⟩
    simp [PyPost.ofRet]

/-- Non-vacuity of the backward bridge: an arrow fact transports to the
whole-body triple (`CallsTo.toTriple`) — this is how a proof *assumes* a
callee's arrow spec and keeps working in the triple vocabulary. -/
example : PyTriple factM
    (fun env => env = mkCallEnv factFn.params #[.int (3 : Nat)]) factFn.body.toList
    { next := fun _ => Val.int (factorial 3 : Nat) = .none,
      ret := fun w _ => w = .int (factorial 3 : Nat) } :=
  (fact_spec 3).toTriple rfl

-- The registry round-trip: `@[py_spec]`-marked lemmas are retrievable via
-- `Lean.labelled` (what the future vcgen calls to look up a callee's spec).
-- Loud elaboration failure if the registration is lost.
open Lean in
#eval show CoreM Unit from do
  let specs ← Lean.labelled `py_spec
  unless specs.contains ``fact_spec do
    throwError "@[py_spec] registry does not contain fact_spec"

end LeanModels.Python.VCTests
