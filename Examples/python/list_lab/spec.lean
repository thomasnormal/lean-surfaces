import LeanModels

/-!
# list_lab — the H2 acceptance set (checks-only example)

Concrete regressions for the list tier (docs/memory-model.md §H2:
lists to the heap), pinned three ways:

* differential rows in `harness/cases.json` (every function below runs
  against CPython 3.9);
* `#py_check`/`#guard` non-vacuity checks here (kernel-evaluated);
* the boundary-invisible cases — fuel behavior, exception-state
  retention, heap well-formedness, `freezeH` snapshot/cycle/sharing —
  as raw `#guard`s and a WF `example` below, because `CallsTo` erases
  the world.

The headline behaviors `Val.listV` could never express: two references
to one list seeing each other's writes (`alias_write`, `callee_mutates`,
`shared_tail`), in-place methods (`append_pop`), the LIVE index cursor
of `for` (`loop_mutate_during`, `loop_append_grows`, `loop_pop_skips` —
never a snapshot), and module-level list tables mutated across nested
calls within one public call (`bump_twice`). No `proof.lean`:
checks-only, like `dict_lab`.
-/

open LeanModels LeanModels.Python

load_program list_lab from "Examples/python/list_lab/list_lab.json"

/-! ### aliasing and in-place mutation — the H2 acceptance behavior -/

#py_check list_lab.alias_write() = 5
#py_check list_lab.alias_append_len(4) = 2
#py_check list_lab.callee_mutates(9) = 9
#py_check list_lab.shared_tail() = 9

/-! ### identity: two literals differ; `is` self; `==` by value -/

#py_check list_lab.fresh_identity() =
  (Val.tuple #[.bool false, .bool true, .bool true])

/-! ### reads: negative indexing, IndexError (read/store), unpacking -/

#py_check list_lab.neg_index() = 40
#py_check list_lab.index_error(1) = 2
#py_check list_lab.index_error(-2) = 1
#py_check list_lab.index_error(5) raises .indexError
#py_check list_lab.index_error(-3) raises .indexError
#py_check list_lab.store_error() raises .indexError
#py_check list_lab.unpack_list() = 12

/-! ### methods: append/pop (pop-empty faithful) -/

#py_check list_lab.append_pop(10) = (Val.tuple #[.int 12, .int 10, .int 1])
#py_check list_lab.pop_empty() raises .indexError

/-! ### membership, equality (nested, cross-type, cyclic), truthiness -/

#py_check list_lab.membership(2) = (Val.tuple #[.bool true, .bool false])
#py_check list_lab.membership(7) = (Val.tuple #[.bool false, .bool true])
#py_check list_lab.eq_nested() = true
#py_check list_lab.eq_mixed() = false
#py_check list_lab.eq_selfref() = true
#py_check list_lab.eq_two_cycles() raises .recursionError
#py_check list_lab.truthy_list() = 2

/-! ### the live index cursor: mutation/growth/shrink during `for` -/

#py_check list_lab.loop_sum() = 10
#py_check list_lab.loop_mutate_during() = 103
#py_check list_lab.loop_append_grows() = 3
#py_check list_lab.loop_pop_skips() = 2

/-! ### `.insert` (the §2.5 residue — docs/memory-model.md
§`list.insert`): CPython's clamping index rule (negative from the end,
floored at 0; beyond-end appends — never IndexError), `None` returned,
aliasing-visible growth, the two faithful `TypeError`s, and the pure
`insort_right` fallback verbatim (the memo-2.5 discharge shape) -/

#py_check list_lab.ins_at(0, 9) = (Val.list #[.int 9, .int 1, .int 2, .int 3])
#py_check list_lab.ins_at(1, 9) = (Val.list #[.int 1, .int 9, .int 2, .int 3])
#py_check list_lab.ins_at(3, 9) = (Val.list #[.int 1, .int 2, .int 3, .int 9])
#py_check list_lab.ins_at(100, 9) =
  (Val.list #[.int 1, .int 2, .int 3, .int 9])
#py_check list_lab.ins_at(-1, 9) = (Val.list #[.int 1, .int 2, .int 9, .int 3])
#py_check list_lab.ins_at(-3, 9) = (Val.list #[.int 9, .int 1, .int 2, .int 3])
#py_check list_lab.ins_at(-100, 9) =
  (Val.list #[.int 9, .int 1, .int 2, .int 3])
-- the bool index is `__index__`-coerced (True inserts at 1)
#guard callFunction list_lab "ins_at" #[.bool true, .int 9] 4096
  == .ok (.list #[.int 1, .int 9, .int 2, .int 3])
#py_check list_lab.ins_empty(7) = (Val.list #[.int 7])
#py_check list_lab.ins_alias(5) = 5
#py_check list_lab.ins_ret() = (Val.none)
#py_check list_lab.ins_badidx() raises
  (.typeError "'str' object cannot be interpreted as an integer")
#py_check list_lab.ins_arity() raises
  (.typeError "insert expected 2 arguments, got 1")
#py_check list_lab.ins_insort(4) =
  (Val.list #[.int 1, .int 3, .int 4, .int 5, .int 7])
#py_check list_lab.ins_insort(0) =
  (Val.list #[.int 0, .int 1, .int 3, .int 5, .int 7])
#py_check list_lab.ins_insort(9) =
  (Val.list #[.int 1, .int 3, .int 5, .int 7, .int 9])

/-! ### builtins over heap lists: `sorted` allocates fresh, `max`/`min` -/

#py_check list_lab.sorted_fresh() = (Val.tuple #[.int 1, .int 3, .bool false])
#py_check list_lab.max_min_list() = (Val.tuple #[.int 4, .int 1])

/-! ### lists inside dicts; lists as dict keys stay unhashable -/

#py_check list_lab.list_in_dict(5) = (Val.tuple #[.int 3, .int 6])
#py_check list_lab.dict_unhashable_key() raises
  (.typeError "unhashable type: 'list'")

/-! ### G1 module tables: shared within one public call, fresh across two -/

#py_check list_lab.read_table(0) = 1
#py_check list_lab.read_table(-1) = 3
#py_check list_lab.bump_table() = 2
#py_check list_lab.bump_twice() = 3

/-! ### the boundary: returned lists freeze to snapshots; cycles refuse -/

#py_check list_lab.return_list(1) =
  (Val.list #[.int 1, .int 2, .list #[.int 3]])
#guard callFunction list_lab "return_self_cycle" #[] 4096 matches .unsupported _

/-! ### fuel behavior: exhaustion is `.timeout`, never a semantic answer;
list-equality cycle detection is fuel-INDEPENDENT -/

#guard callFunction list_lab "eq_selfref" #[] 2 == .timeout
#guard heapEq #[.list #[.int 1], .list #[.int 1]] 1 [] (.ref 0) (.ref 1)
  == .timeout
#guard heapEq #[.list #[.int 1], .list #[.int 1]] 8 [] (.ref 0) (.ref 1)
  == .ok true
#guard heapEq #[.list #[.int 0, .ref 0], .list #[.int 0, .ref 1]] 8 []
  (.ref 0) (.ref 1) == .exn .recursionError
#guard heapEq #[.list #[.int 1], .dict #[(.int 1, .int 1)] 0] 8 []
  (.ref 0) (.ref 1) == .ok false

/-! ### `freezeH` directly: snapshot, nesting, sharing (a DAG duplicates),
cycle refusal (fuel-independent), exhaustion `.timeout` -/

#guard RVal.freezeH #[.list #[.int 1]] 64 [] (.ref 0) == .ok (.list #[.int 1])
#guard RVal.freezeH #[.list #[.ref 1], .list #[.int 2]] 64 [] (.ref 0)
  == .ok (.list #[.list #[.int 2]])
#guard RVal.freezeH #[.list #[.ref 1, .ref 1], .list #[.int 2]] 64 [] (.ref 0)
  == .ok (.list #[.list #[.int 2], .list #[.int 2]])
#guard RVal.freezeH #[.list #[.int 1, .ref 0]] 64 [] (.ref 0)
  matches .unsupported _
#guard RVal.freezeH #[.list #[.int 1]] 1 [] (.ref 0) == .timeout

/-! ### exception-state retention: the store before the raise survives in
the `.exn` world (pinned at `callIn`; heap slot 0 is the G1 `TABLE`) -/

#guard (match callIn list_lab 4096 (initWorld list_lab) "store_exc_state"
          #[.int 3] with
        | .exn w .zeroDivisionError =>
          w.heap == #[.list #[.int 1, .int 2, .int 3], .list #[.int 3]]
        | _ => false)

/-! ### heap well-formedness (slice): a list heap with an internal ref -/

example : Heap.WF #[.list #[.int 2], .list #[.int 1, .ref 0]] := by
  intro a hlt
  have h2 : a < 2 := by simpa using hlt
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl <;> simp [Obj.WF, RVal.WFList, RVal.WF]
