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
* **A capture the frame REBINDS after the def is a real CELL** — the
  rows that used to expose snapshot-vs-cell now AGREE with CPython:
  `rebound_after(5)` is 6 (a snapshot would forge 5), `cell_read_twice`
  reads the same cell across a rebinding, `two_closures_one_cell` shows
  one cell per FRAME, `cell_unbound_at_def` starts empty (the shipped
  `guard`'s shape) and `gen_cell_before_call` is `moves()`' shape.
* **The boundary of the CELL tier is pinned by the rows that would
  expose it** — the cell is read from the DEFINING frame at the call, so
  an ESCAPING closure (`cell_escapes`) refuses; a generator reads cells
  at RESUME while the tier reads at the CALL, so a rebinding at or after
  the first call (`gen_cell_after_call`) refuses. `nonlocal`, a def
  inside a loop, and a call before the def (CPython's UnboundLocalError)
  refuse as before.

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

/-! ### H7 CELLS — a capture the frame rebinds after the def -/

#py_check closure_lab.rebound_after(5) = 6
#py_check closure_lab.cell_read_twice(2) = 220
#py_check closure_lab.two_closures_one_cell(3) = 48
#py_check closure_lab.cell_unbound_at_def(2) = 12
#py_check closure_lab.gen_cell_before_call(2) = 13

/-! ### the loud frontier — what the cell mechanism does NOT cover -/

#guard (match callFunction closure_lab "cell_escapes" #[.int 5] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "gen_cell_after_call" #[.int 1] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "uses_nonlocal" #[.int 4] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "def_in_loop" #[.int 3] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction closure_lab "early_call" #[.int 1] 10000 with
  | .unsupported _ => true | _ => false)

/-! ### H7 lambdas: the Position.move `put` shape -/

#py_check closure_lab.lam_basic("abcde", 2, "Z") = "XbZde"
#py_check closure_lab.lam_capture(3) = 11
#py_check closure_lab.lam_rebound(5) = 6

/-! ### bound() arc pass 2: recursion FROM a generator frame through the
captured self (the bound() shape). Each depth executes its own
`def kids():` — a fresh closure, a fresh generator — and the cutoff
abandons the drain mid-yield: `nodes` proves the pruned subtrees never
ran ((2, 4) under cut=2 vs (9, 13) under cut=100 at the same depth). -/

#py_check closure_lab.gen_rec(1, 2) = (Val.tuple #[.int 2, .int 3])
#py_check closure_lab.gen_rec(2, 2) = (Val.tuple #[.int 2, .int 4])
#py_check closure_lab.gen_rec(2, 100) = (Val.tuple #[.int 9, .int 13])

/-! the refusal the admission excludes: a nested def calling ITSELF by
its own name — the name is an enclosing local bound BY the def, so the
census refuses (CPython's cell resolves the recursion and answers 3) -/

#guard (match callFunction closure_lab "rec_nested_name" #[.int 3] 10000 with
  | .unsupported _ => true | _ => false)
