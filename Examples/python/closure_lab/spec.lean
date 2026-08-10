import LeanModels

/-!
# closure_lab — H7 nested defs and closures (checks-only example)

Concrete regressions for the snapshot tier (docs/memory-model.md
§nested defs and closures), pinned two ways: differential rows in
`harness/cases.json` and the `#py_check`/`#guard` checks here.

The claims worth naming:

* **Snapshot-at-def IS the cell inside the admitted fragment** — captures
  are never rebound after the def, so `basic`/`chain`/`escape` agree with
  CPython, the escape row across the creator's dead frame included.
* **A generator closure reads captures at RESUME time** — `gen_closure`
  (consumed by `for`), `gen_closure_sorted` (drained), `gen_closure_any`
  (short-circuited) all ride the H4 stepper with the snapshot in the
  stored locals.
* **Closures are heap IDENTITY** — two equal-bodied closures are `False`
  under `==` (exact: function equality is identity in CPython); truthy;
  `len` the faithful `TypeError`.
* **The boundary of the tier is pinned by the rows that would expose
  it** — `rebound_after` is CPython's cell semantics observable
  (`rebound_after(5)` is 6 there; a snapshot would forge 5): REFUSED at
  extraction, never translated. `nonlocal`, a def inside a loop, and a
  call before the def (CPython's UnboundLocalError) refuse likewise.

No `proof.lean`: checks-only, like `kw_lab`/`drain_lab`.
-/

open LeanModels LeanModels.Python

load_program closure_lab from "Examples/python/closure_lab/closure_lab.json"

/-! ### the snapshot agrees with the cell inside the fragment -/

#py_check closure_lab.basic(2) = 11
#py_check closure_lab.param_only(5) = 10
#py_check closure_lab.with_default(2) = 29
#py_check closure_lab.chain(4) = 50
#py_check closure_lab.escape(3) = 9

/-! ### identity, truthiness, the faithful TypeError -/

#py_check closure_lab.identity_pair(1) =
  (Val.tuple #[.bool false, .bool true, .bool true])
#py_check closure_lab.truthy_closure(0) = 1
#py_check closure_lab.len_of_closure() raises
  (.typeError "object of type 'function' has no len()")

/-! ### generator closures: resume-time capture reads -/

#py_check closure_lab.gen_closure(3) = 55
#guard callFunction closure_lab "gen_closure_sorted" #[.int 7] 10000 ==
  .ok (.list #[.int 2, .int 2, .int 1, .int 1, .int 1, .int 0, .int 0])
#py_check closure_lab.gen_closure_any(3) = true
#py_check closure_lab.gen_closure_any(9) = false

/-! ### the loud frontier — the rows that would expose snapshot-vs-cell -/

#guard (match callFunction closure_lab "rebound_after" #[.int 5] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "uses_nonlocal" #[.int 4] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "def_in_loop" #[.int 3] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "early_call" #[.int 1] 10000 with
  | .unsupported _ => true | _ => false)
