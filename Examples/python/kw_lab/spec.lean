import LeanModels

/-!
# kw_lab — call-site keyword arguments (H6, checks-only example)

Concrete regressions for the keyword tier (docs/memory-model.md
§call-site keyword arguments), pinned two ways: differential rows in
`harness/cases.json` (every function runs against CPython 3.9) and the
`#py_check`/`#guard` non-vacuity checks here (kernel-evaluated).

The claims worth naming:

* **Binding is by NAME onto a COMPLETE positional array** — `callIn`'s
  covenant signature never changes. `kw_plain` fills a HOLE from a
  literal default; `kw_all`/`kw_swap` bind out of parameter order.
* **Evaluation order is CPython's** — positionals, then keyword VALUES
  left to right. `kw_order`/`kw_pos_order` observe it through WHICH
  exception fires.
* **The binding `TypeError`s are faithful** — unexpected keyword,
  multiple values, missing required argument — and they fire only on an
  `argsOk` parameter table; an untrusted table refuses loudly instead.
* **The `rotate(nullmove=True)` shape works** — a keyword call on a
  namedtuple-subclass method (`method_kw`), `self` prepended before the
  merge.
* **The loud frontier is pinned** — namedtuple keyword CONSTRUCTION
  and builtin keywords refuse loudly, never guess; `sorted(reverse=)`
  is LIVE (the H6 draining tier).

No `proof.lean`: checks-only, like `gen_lab`/`iter_lab`/`cls_lab`.
-/

open LeanModels LeanModels.Python

load_program kw_lab from "Examples/python/kw_lab/kw_lab.json"

/-! ### keyword merges onto module functions -/

#py_check kw_lab.kw_plain(1) = 129
#py_check kw_lab.kw_plain(7) = 729
#py_check kw_lab.kw_all(3) = 333
#py_check kw_lab.kw_swap(4) = -3
#py_check kw_lab.base(5) = 523

/-! ### evaluation order, observed through exceptions -/

#py_check kw_lab.kw_order(0) raises .zeroDivisionError
#py_check kw_lab.kw_order(1) raises (.nameError "nope")
#py_check kw_lab.kw_pos_order(0) raises .zeroDivisionError
#py_check kw_lab.kw_pos_order(2) raises (.nameError "nope")

/-! ### the faithful binding TypeErrors -/

#py_check kw_lab.kw_unexpected(1) raises
  (.typeError "base() got an unexpected keyword argument 'd'")
#py_check kw_lab.kw_multiple(1) raises
  (.typeError "base() got multiple values for argument 'a'")
#py_check kw_lab.kw_missing(5) raises
  (.typeError "two_req() missing 1 required positional argument: 'b'")

/-! ### the rotate(nullmove=True) shape: ntuple-subclass method keywords -/

#py_check kw_lab.method_kw(2) = 1
#py_check kw_lab.method_kw_default(2) = 13
#py_check kw_lab.tag_kw() = "a-b"

/-! ### callable check AFTER arguments, on a shadowed name -/

#py_check kw_lab.shadow_kw(7) raises
  (.typeError "'int' object is not callable")

/-! ### the loud frontier (never a guessed error class) -/

#guard (match callFunction kw_lab "ntuple_kw" #[.int 4] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction kw_lab "builtin_kw" #[] 10000 with
  | .unsupported _ => true | _ => false)
#guard callFunction kw_lab "sorted_kw" #[.int 5] 10000 ==
  .ok (.list #[.int 5, .int 3, .int 1])

/-! ### H7+: instance-method keywords (the self.bound(root=True) shape) -/

#py_check kw_lab.method_kw_instance(5) = 7
#py_check kw_lab.method_kw_instance_err(1) raises
  (.typeError "Counter.bump() got multiple values for argument 'by'")
