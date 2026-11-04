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
simple same-module inheritance (`Sub(Cell)`) reuses the base methods; a missing attribute is
the faithful `AttributeError` raised BEFORE arguments evaluate. No
`proof.lean`: checks-only, like `dict_lab`/`list_lab` — the stateful
`CallsIn` theorems about a sunfish-shaped `Searcher` moved to the sunfish
repository with the other sunfish proofs (Examples/python/README.md).
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

/-! ### literal custom equality, inheritance, and class-as-value -/

#py_check cls_lab.weird_eq(1) =
  (Val.tuple #[.int 1, .bool true, .bool true, .bool true])
#py_check cls_lab.sub_inherits(1) = 1
#py_check cls_lab.object_base_truthy() = true
#py_check cls_lab.class_as_value() = 0
#guard callFunction cls_lab "attr_on_int" #[.int 1] 4096
  matches .exn .attributeError

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

/-! ### bound() arc pass 2: recursion through the receiver — direct
(`self.down`) and mutual (`self.odd`/`self.even`) method recursion,
the same `.ref` re-entering `callIn` at every depth, one shared
`nodes` counter mutating across the nest -/

#py_check cls_lab.method_rec(4) = (Val.tuple #[.int 4, .int 5])
#py_check cls_lab.method_rec(0) = (Val.tuple #[.int 0, .int 1])
#py_check cls_lab.method_mutual(5) = (Val.tuple #[.bool true, .bool false])
#py_check cls_lab.method_mutual(2) = (Val.tuple #[.bool false, .bool true])

/-! ### pass 4 (docs/memory-model.md §bound() end-to-end): attribute
`+=` (sunfish's `self.nodes += 1` — the load fires BEFORE the value
evaluates, so `aug_attr_missing`'s division by zero never runs) and
tuple targets with ATTRIBUTE elements (`Searcher.__init__`'s
`self.a, self.b = …`; the RHS reads before any store). The loud
frontier: a list-valued attribute's `+=` (in-place mutation); dict
subscript elements now use the same left-to-right heap store path. -/

#py_check cls_lab.aug_attr(3) = 6
#py_check cls_lab.aug_attr(0) = 0
#py_check cls_lab.aug_attr_missing(1) raises .attributeError
#py_check cls_lab.unpack_attrs(7) = 708
#py_check cls_lab.unpack_attrs_mixed(4) = 904
#py_check cls_lab.unpack_attrs_swap(9) = 209
#py_check cls_lab.unpack_arity(1) raises
  (.valueError "not enough values to unpack (expected 2, got 1)")

#py_check cls_lab.aug_attr_list(1) = 1
#py_check cls_lab.aug_attr_list(0) = 1
#py_check cls_lab.unpack_subscript_elem(1) = (Val.tuple #[.int 1, .int 1])

/-! ### pass 5: CHAINED assignment, split at ingestion
(docs/memory-model.md §search()'s first blockers): `t1 = t2 = v` ⇢
`t1 = v; t2 = t1` when `t1` is a plain name — CPython's DUP_TOP with
the dup read back from the name. `chain_rebind_receiver` pins the
ORDER claim: the second store's receiver reads the NEW `x` (an int),
so the faithful AttributeError fires after the rebind, exactly as
CPython. `chain_attr_first` pins the synthetic-temporary lowering for an
attribute-first chain. -/

#py_check cls_lab.chain_names(5) = 18
#py_check cls_lab.chain_attr(5) = (Val.tuple #[.int 10, .int 10])
#py_check cls_lab.chain_rebind_receiver(4) raises .attributeError

#py_check cls_lab.chain_attr_first(5) = 6

#py_check cls_lab.bytes_index_instance() raises
  (.typeError "byte indices must be integers or slices, not Cell")
#py_check cls_lab.bytes_contains_instance() raises
  (.typeError "a bytes-like object is required, not 'Cell'")

/-! ### `__slots__`: declared fields, augmented stores, left-to-right tuple
stores, and the explicit `__dict__` escape hatch -/

#py_check cls_lab.slot_read(7) = 7
#py_check cls_lab.slot_store(7) = 8
#py_check cls_lab.slot_aug(7) = 9
#py_check cls_lab.slot_reject(7) raises .attributeError
#py_check cls_lab.slot_tuple_reject(7) raises .attributeError
#py_check cls_lab.slot_dict(7) = (Val.tuple #[.int 7, .int 8])

#guard (findClass cls_lab "SlotCell").isSome
#guard (findClass cls_lab "SlotDict").isSome
