import LeanModels.Python.VC2
import LeanModels.Python.VCTactic

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

/-- Spec-side recursive sum (core Lean has none; local to the tests).  Addition
keeps this proof-layer smoke test in the pure fragment; heap-backed
multiplication has its own stateful acceptance battery. -/
private def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) + factorial n

#guard factorial 5 = 16

/-- `def fact(n): if n <= 0: return 1 ⏎ r = fact(n - 1) ⏎ return n + r` —
the minimal recursive function with the recursive call in `x = f(e)`
position (what `PyStmtTriple.call` matches). -/
private def factFn : FunctionDefn where
  name := "fact"
  params := #[⟨"n", sp, Option.none⟩]
  argsOk := true
  body := #[
    .ifStmt (.compare (.name "n" sp) #[.ltE] #[.constant (.int 0) sp] sp)
      #[.ret (some (.constant (.int 1) sp)) sp] #[] sp,
    .assign #[.name "r" sp]
      (.call (.name "fact" sp)
        #[.binOp (.name "n" sp) .sub (.constant (.int 1) sp) sp] #[] Option.none sp) sp,
    .ret (some (.binOp (.name "n" sp) .add (.name "r" sp) sp)) sp]
  span := sp

/-- `def fact_plus_one(n): y = fact(n) ⏎ return y + 1` — a non-recursive
caller whose callee spec comes from the `@[py_spec]` registry. -/
private def factPlusOneFn : FunctionDefn where
  name := "fact_plus_one"
  params := #[⟨"n", sp, Option.none⟩]
  argsOk := true
  body := #[
    .assign #[.name "y" sp]
      (.call (.name "fact" sp) #[.name "n" sp] #[] Option.none sp) sp,
    .ret (some (.binOp (.name "y" sp) .add (.constant (.int 1) sp) sp)) sp]
  span := sp

private def factM : Module := { functions := #[factFn, factPlusOneFn], topLevel := #[] }

#py_check factM.fact(5) = 16
#py_check factM.fact_plus_one(4) = 12

/-! The quantified recursive proof formerly lived here.  It used the pure
`PyTriple.call` bridge, whose pinned world was depth zero; call-depth-aware
proofs now use `CallsIn`/`EvalsState` and are being rebuilt with a
fuel-threaded recursive relation.  The concrete recursion rows above remain
active while that proof migration is in progress. -/

/-! ## Round-3 regression: the ∃-relational `py_vcgen` entry

The playtest found `py_vcgen` rejecting `∃ v, f(args) ==> v ∧ Φ v` goals —
the surface `==>` elaborates the result slot as `ToVal.toVal v`, which the
entry matcher required to be a literal bound variable. Both accepted binder
shapes are pinned end-to-end here (a loop-carrying relational statement is
additionally smoke-tested in VCTactic.lean). -/

/-- Marshalled binder (`PyInt`): the exact surface form the playtest wrote —
result slot `ToVal.toVal v` — bridged by `PyTriple.exists_callsTo_toVal`. -/
example : ∃ v : PyInt, factM.fact(0) ==> v ∧ 0 < v := by
  py_vcgen [factM, factFn, factPlusOneFn]
  all_goals omega

/-- Raw `Val` binder used literally — the shape the matcher always accepted
(`PyTriple.exists_callsTo`), pinned against regression. -/
example : ∃ v, CallsTo factM "fact" #[.int 0] v ∧ v = .int 1 := by
  py_vcgen [factM, factFn, factPlusOneFn]

/-! ## F1/F2 smoke: literal parameter defaults through `py_vcgen`

`def scale(x, k=3, b=None): if b is None: b = 1 ⏎ return x + k + b` — an
int default, a None default consumed by an `is None` branch (F2), and
call sites at every legal arity. The `CallsTo` entry bridges through
`PyTriple.callsTo_arityOk`, whose arity-window side condition closes by
`rfl` with the optional arguments omitted (the old exact-arity bridge
would have failed right there); `mkCallEnv` fills `k`/`b` from their
literal defaults during the captured symbolic run. -/

private def scaleFn : FunctionDefn where
  name := "scale"
  params := #[⟨"x", sp, Option.none⟩, ⟨"k", sp, some (.int 3)⟩,
              ⟨"b", sp, some .none⟩]
  argsOk := true
  body := #[
    .ifStmt (.compare (.name "b" sp) #[.is] #[.constant .none sp] sp)
      #[.assign #[.name "b" sp] (.constant (.int 1) sp) sp] #[] sp,
    .ret (some (.binOp (.binOp (.name "x" sp) .add (.name "k" sp) sp)
      .add (.name "b" sp) sp)) sp]
  span := sp

private def scaleM : Module := { functions := #[scaleFn], topLevel := #[] }

-- Concrete runs at all three arities (the `#py_check` surface accepts the
-- omitted-optionals call because the interpreter itself fills defaults).
#py_check scaleM.scale(5) = 9
#py_check scaleM.scale(5, 2) = 8
#py_check scaleM.scale(5, 2, 7) = 14

/-- Both optionals omitted: arity 1 against 3 params walks end-to-end. -/
example : CallsTo scaleM "scale" #[.int 5] (.int 9) := by
  py_vcgen [scaleM, scaleFn]

/-- Exact arity through the same general bridge (regression: full calls
must keep working after the re-point to `_arityOk`). The third argument
overrides the `None` default, so the `is None` branch is NOT taken. -/
example : CallsTo scaleM "scale" #[.int 5, .int 2, .int 7] (.int 14) := by
  py_vcgen [scaleM, scaleFn]

/-- Relational entry with a marshalled binder and omitted optionals —
`PyTriple.exists_callsTo_toVal_arityOk` end-to-end. -/
example : ∃ v : PyInt, scaleM.scale(5) ==> v ∧ 0 < v := by
  py_vcgen [scaleM, scaleFn]
  all_goals omega

/-! ## call:sorted smoke: a builtin call-assignment executes concretely

`def sorted_len(data): xs = sorted(data) ⏎ return len(xs)` — the
`xs = sorted(data)` assignment is syntactically the `handleCall` shape
(single `Name`-callee call as the whole right-hand side, no
`call_unsupported`), but `sorted` has no module-table entry, so the walker
must NOT intercept it and demand a `CallsTo` fact: `calleeInModule`
downgrades it to a straight-line statement and the captured run steps
through `sortedVal` (`interpUnfolds`), with `asIntList_map_toVal`
extracting the marshalled int list and `sortInts_length` deciding the
subsequent `len` (`interpLemmas`). The symbolic result keeps the compact
`sortInts data` handle — `sortInts`/`insertLe` are deliberately not
unfolded. -/

private def sortedLenFn : FunctionDefn where
  name := "sorted_len"
  params := #[⟨"data", sp, Option.none⟩]
  argsOk := true
  body := #[
    .assign #[.name "xs" sp]
      (.call (.name "sorted" sp) #[.name "data" sp] #[] Option.none sp) sp,
    .ret (some (.call (.name "len" sp) #[.name "xs" sp] #[] Option.none sp)) sp]
  span := sp

private def sortedLenM : Module := { functions := #[sortedLenFn], topLevel := #[] }

#py_check sortedLenM.sorted_len([3, 1, 2]) = 3
#py_check sortedLenM.sorted_len(([] : List Int)) = 0

/-! The concrete runs pin the interpreter path.  A symbolic theorem for this
shape needs a heap-state invariant for the fresh list allocated by `sorted`,
so it remains outside this value-only test module. -/

end LeanModels.Python.VCTests
