import LeanModels

/-!
# walrus_lab — the WALRUS operator (checks-only example)

`(x := e)` in general expression position: evaluate `e`, BIND `x` in the
frame that is running, answer the same value (docs/memory-model.md §the
walrus operator). Pinned two ways, like every lab: differential rows in
`harness/cases.json` and the `#py_check`/`#guard` checks here.

The claims worth naming:

* **The binding OUTLIVES the expression** — `w_basic` reads `m` in the
  branch below the test that bound it, `w_reuse` reads `b` twice in the
  same statement and once after it.
* **It binds in EVALUATION order, not textual order** — `w_order`'s
  second operand sees the first one's binding; `w_call_arg` binds inside
  a call argument and reads it after the call returned.
* **A short-circuited walrus never binds** — `w_short_circuit(0)` is
  CPython's `UnboundLocalError`, not a silent zero, because the `and`
  stopped before the walrus ran.
* **The comprehension flavour keeps its own lowering** — a genexp is its
  own scope and PEP 572 leaks the binding to the ENCLOSING one, so the
  extractor emits `NamedExpr` only OUTSIDE a comprehension and hoists a
  filter's leftmost walrus into the synthesized body instead (pass 7,
  §the walrus filter). `w_genexp_filter` is the shipped ordering line's
  shape.

No `proof.lean`: checks-only, like `kw_lab`/`closure_lab`.
-/

open LeanModels LeanModels.Python

load_program walrus_lab from "Examples/python/walrus_lab/walrus_lab.json"

/-! ### the binding outlives the expression -/

#py_check walrus_lab.w_basic(3) = 6
#py_check walrus_lab.w_basic(1) = -2
#py_check walrus_lab.w_reuse(4) = 105

/-! ### evaluation order, and a call argument -/

#py_check walrus_lab.w_order(2) = 9
#py_check walrus_lab.w_call_arg(7) = 404
#py_check walrus_lab.w_call_arg(1) = -2

/-! ### the loop-condition idiom -/

#py_check walrus_lab.w_while(4) = 6
#py_check walrus_lab.w_while(1) = 0

/-! ### a short-circuited walrus never binds — CPython's UnboundLocalError,
which this tier answers as the `NameError` its exception model carries -/

#py_check walrus_lab.w_short_circuit(5) = 1
#guard (match callFunction walrus_lab "w_short_circuit" #[.int 0] 10000 with
  | .exn (.nameError "q") => true | _ => false)

/-! ### the comprehension flavour: hoisted, not re-scoped -/

#guard callFunction walrus_lab "w_genexp_filter" #[.int 1, .int 3, .int (-2)] 10000 ==
  .ok (.list #[.tuple #[.int 9, .int 3], .tuple #[.int 4, .int (-2)],
               .tuple #[.int 1, .int 1]])
