import LeanModels

/-!
# cls_lab — the H3 acceptance set (checks-only example)

Concrete regressions for the class tier (docs/memory-model.md §H3:
classes), pinned three ways:

* differential rows in `harness/cases.json` (every function below runs
  against CPython 3.9);
* `#py_check`/`#guard` non-vacuity checks here (kernel-evaluated);
* the boundary-invisible cases — returning an instance refuses loudly,
  instance heap well-formedness — as raw `#guard`s and a WF `example`,
  because `CallsTo` erases the world.

The headline behaviors: instantiation runs `__init__` through `callIn`
with `self` as an ordinary first argument (methods are flattened
functions — no new call machinery); `self.x = v` mutates the instance
IN PLACE, visible through every alias; a user method named like a
builtin method (`Cell.get`) dispatches through the CLASS, never the
dict/list method tier; default-object protocol is faithful BECAUSE the
dunder guard makes classes with extra dunders uninstantiable (`Weird`);
inheritance is loudly out of tier (`Sub(Cell)`); a missing attribute is
the faithful `AttributeError` raised BEFORE arguments evaluate. No
`proof.lean`: checks-only, like `dict_lab`/`list_lab` — the stateful
`CallsIn` theorems live in `Examples/python/sf_searcher`.
-/

open LeanModels LeanModels.Python

load_program cls_lab from "Examples/python/cls_lab/cls_lab.json"

/-! ### instantiation, methods, mutable self -/

#py_check cls_lab.make_get(7) = 7
#py_check cls_lab.set_then_get(1, 9) = (Val.tuple #[.int 9, .int 9])
#py_check cls_lab.bump_twice(5) = 7
#py_check cls_lab.store_before_read(1) = (Val.tuple #[.int 2, .int 1])

/-! ### aliasing and identity: one object through two names; two
instances of one class are distinct (default `__eq__` = identity) -/

#py_check cls_lab.alias_mutation(1, 8) =
  (Val.tuple #[.int 8, .int 8, .bool true, .bool false])
#py_check cls_lab.two_instances(4) =
  (Val.tuple #[.bool false, .bool false, .bool true, .bool true])

/-! ### default-object truthiness: an instance is always `True` -/

#py_check cls_lab.instance_truthy(0) = 1

/-! ### heap containers as instance attributes (the Searcher shape):
`self.items.append(…)`, `self.meta[k] = v` through attribute reads -/

#py_check cls_lab.bag_flow(2, 3) =
  (Val.tuple #[.int 3, .int 3, .int 1, .bool true])

/-! ### `__init__`-less classes; arity through the flattened `__init__` -/

#py_check cls_lab.no_init_ping() = 42
#py_check cls_lab.no_init_arity() raises
  (.typeError "NoInit() takes no arguments")
#guard callFunction cls_lab "init_arity" #[.int 1] 4096
  matches .exn (.typeError _)

/-! ### the faithful `AttributeError` frontier (read, call, store) -/

#py_check cls_lab.missing_attr(1) raises .attributeError
#py_check cls_lab.missing_method(1) raises .attributeError
#py_check cls_lab.store_attr_on_dict(1) raises .attributeError

/-! ### default protocol refusals are faithful `TypeError`s (the dunder
guard means no `__len__`/`__getitem__`/`__iter__` can exist) -/

#guard callFunction cls_lab "len_of_instance" #[.int 1] 4096
  matches .exn (.typeError _)
#guard callFunction cls_lab "subscript_instance" #[.int 1] 4096
  matches .exn (.typeError _)
#guard callFunction cls_lab "iterate_instance" #[.int 1] 4096
  matches .exn (.typeError _)

/-! ### the loud frontier: extra dunders, inheritance, class-as-value,
attribute access on scalars (ints DO have attributes — never a fake
`AttributeError`) -/

#guard callFunction cls_lab "weird_eq" #[.int 1] 4096 matches .unsupported _
#guard callFunction cls_lab "sub_inherits" #[.int 1] 4096
  matches .unsupported _
#guard callFunction cls_lab "class_as_value" #[] 4096 matches .unsupported _
#guard callFunction cls_lab "attr_on_int" #[.int 1] 4096
  matches .unsupported _

/-! ### the boundary: an instance cannot cross it (no observation form) -/

#guard (Run.toPublic 4096
  (Run.ok ({ heap := #[.instance 0 #[("x", .int 1)]], globals := [] } : World)
    (RVal.ref 0))) matches .unsupported _

/-! ### representation: the three flattened `Cell` methods resolve under
qualified names; plain-name resolution never sees them -/

#guard (findFunction cls_lab "Cell.__init__").isSome
#guard (findFunction cls_lab "Cell.get").isSome
#guard (findFunction cls_lab "Cell.bump2").isSome
#guard (findFunction cls_lab "get").isNone
#guard (findClass cls_lab "Cell") matches some (0, _)
#guard (findClass cls_lab "Bag") matches some (1, _)
#guard hasExtraDunder
  { name := "W", ok := true, methods := #["__init__", "__eq__"], span := default }
#guard !hasExtraDunder
  { name := "C", ok := true, methods := #["__init__", "get", "set"], span := default }

/-! ### heap well-formedness (slice): an instance whose attribute refs a
heap list -/

example : Heap.WF #[.list #[.int 2], .instance 0 #[("items", .ref 0)]] := by
  intro a hlt
  have h2 : a < 2 := by simpa using hlt
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl <;> simp [Obj.WF, RVal.WFList, RVal.WF]
