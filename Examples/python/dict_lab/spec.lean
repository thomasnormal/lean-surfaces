import LeanModels

/-!
# dict_lab — the H1-proper acceptance set (checks-only example)

Concrete regressions for the dict tier (docs/memory-model.md §H1
acceptance), pinned three ways:

* differential rows in `harness/cases.json` (every function below runs
  against CPython 3.9);
* `#py_check`/`#guard` non-vacuity checks here (kernel-evaluated);
* the boundary-invisible cases — fuel behavior (14), exception-state
  retention (16), heap well-formedness (18) — as raw `#guard`s and a WF
  `example` below, because `CallsTo` erases the world.

Live dict iteration (case 10) is NOT in the H1 inventory (no
snapshot-keys shortcut — the doc forbids it); `iter_dict` pins the loud
refusal. Case 15 (module-global dicts) lands with the G1 world-init
stage. No `proof.lean`: checks-only, like `tut_01`.
-/

open LeanModels LeanModels.Python

/- **`maxRecDepth`, and the number is measured.** `load_program` builds the
whole module as a LITERAL term through the derived `ToExpr` instances, so the
elaborator's recursion depth scales with the envelope, not with the proof.
`dict_lab` is the largest envelope in the tree — 611 KB and 101 functions,
against `gen_lab`'s 272 KB and 53 — and it crossed the default 512 somewhere
between 85 functions (§pycomplete-18, green) and 101 (§pycomplete-19).

The failure is worth naming because it does not look like itself: the recursion
limit is hit at THIS line, `dict_lab` is then added UNCOMPILED, and every one of
the ~44 downstream `#guard`/`#py_check` lines reports
*"depends on 'dict_lab', which is 'noncomputable'"* — a different failure class
pointing at a different file. The root error is the only one that names the
cause, and it is the FIRST one. -/
set_option maxRecDepth 65536

load_program dict_lab from "Examples/python/dict_lab/dict_lab.json"

/-! ### 1-2: aliasing, callee mutation through the shared world -/

#py_check dict_lab.alias_write(5) = 5
#py_check dict_lab.alias_write(0) = 0
#py_check dict_lab.caller_sees(1, 42) = 42
#py_check dict_lab.caller_sees("k", 7) = 7

/-! ### 3: identity — two literals differ, `is` self, `==` value -/

#py_check dict_lab.distinct_literals() =
  (Val.tuple #[.bool false, .bool true, .bool true])

/-! ### 4-5: bool/int key coercion; duplicate literal keys -/

#py_check dict_lab.bool_int_key() = (Val.tuple #[.int 1, .int 9, .int 9])
#py_check dict_lab.dup_literal_keys() =
  (Val.tuple #[.int 2, .str "b", .str "z"])

/-! ### 6-8: equality — order-blind, identity shortcut, cyclic raise -/

#py_check dict_lab.eq_ignores_order() = (Val.tuple #[.bool true, .bool false])
#py_check dict_lab.self_cycle_eq() = true
#py_check dict_lab.two_cycles_eq() raises .recursionError

/-! ### 9: unhashable keys raise before any scan (empty dict included) -/

#py_check dict_lab.unhashable_probe() raises (.typeError "unhashable type: 'list'")
#py_check dict_lab.unhashable_store() raises (.typeError "unhashable type: 'list'")

/-! ### 9c: the message names the OFFENDING COMPONENT, not the key

A WRONG FACT until 2026-08-16: `{(1, [2]): 0}` answered
`unhashable type: 'tuple'`, and CPython 3.9.19 says `'list'` —
`tuple.__hash__` hashes its elements, and the first element to raise is
the one whose message escapes. Measured live, all three, and the search
is depth-first left to right on both the store and the read path. -/

#py_check dict_lab.unhashable_in_tuple() raises
  (.typeError "unhashable type: 'list'")
#py_check dict_lab.unhashable_nested() raises
  (.typeError "unhashable type: 'list'")
#py_check dict_lab.unhashable_tuple_read() raises
  (.typeError "unhashable type: 'list'")

/-! ### 11: subscript-store evaluation order (RHS, primary, key) -/

#py_check dict_lab.eval_order_rhs() raises .zeroDivisionError
#py_check dict_lab.eval_order_key() raises (.nameError "e")

/-! ### 12: the boundary refuses heap objects in results, per referent -/

#guard callFunction dict_lab "ret_dict" #[] 4096 matches .unsupported _
#guard callFunction dict_lab "ret_tuple_with_dict" #[] 4096 matches .unsupported _

/-! ### reads: `.get`, truthiness, KeyError, len/in, tuple keys, nesting -/

#py_check dict_lab.get_hit(1) = 10
#py_check dict_lab.get_hit(2) = (Val.none)
#py_check dict_lab.get_hit("a") = 20
#py_check dict_lab.get_hit(true) = 10
#py_check dict_lab.get_default() = (Val.tuple #[.none, .int 5, .int 20])
#py_check dict_lab.truthiness() = (Val.tuple #[.int 10, .bool true, .bool false])
#py_check dict_lab.key_error() raises .keyError
#py_check dict_lab.len_in(1) =
  (Val.tuple #[.int 2, .bool true, .bool false, .bool false])
#py_check dict_lab.len_in(5) =
  (Val.tuple #[.int 2, .bool false, .bool true, .bool false])
#py_check dict_lab.tuple_keys() =
  (Val.tuple #[.str "a", .str "a", .bool false, .bool true])
#py_check dict_lab.nested_dicts() = 3
#py_check dict_lab.dict_eq_mixed() =
  (Val.tuple #[.bool true, .bool false, .bool true])
#py_check dict_lab.mate_style() = 69290

/-! ### out-of-tier stays loud: non-None immediate `is`, live iteration -/

#guard callFunction dict_lab "int_is" #[.int 1, .int 1] 4096 matches .unsupported _
#guard callFunction dict_lab "iter_dict" #[] 4096 matches .unsupported _

/-! ### 14: fuel exhaustion is `.timeout` — never a semantic answer — and
cycle detection is fuel-INDEPENDENT (`RecursionError` at tiny fuel too) -/

#guard callFunction dict_lab "self_cycle_eq" #[] 1 == .timeout
#guard heapEq #[.dict #[(.int 0, .int 5)] 1, .dict #[(.int 0, .int 5)] 1]
  1 [] (.ref 0) (.ref 1) == .timeout
#guard heapEq #[.dict #[(.int 0, .int 5)] 1, .dict #[(.int 0, .int 5)] 1]
  8 [] (.ref 0) (.ref 1) == .ok true
#guard heapEq #[.dict #[(.int 0, .ref 0)] 1, .dict #[(.int 0, .ref 1)] 1]
  3 [] (.ref 0) (.ref 1) == .exn .recursionError

/-! ### 16: mutations before an internal raise survive in the `.exn` state
(the public boundary erases the world, so this is pinned at `callIn`) -/

#guard (match callIn dict_lab 4096 (initWorld dict_lab) "store_exc_state"
          #[.int 3] with
        | .exn w .zeroDivisionError =>
          w.heap == #[.dict #[(.int 1, .int 3)] 1]
        | _ => false)

/-! ### 18 (slice): the retained heap is well-formed -/

example : Heap.WF #[.dict #[(.int 1, .int 3)] 1] := by
  intro a hlt
  have ha : a = 0 := by
    simpa [Nat.lt_one_iff] using hlt
  subst ha
  simp [Obj.WF, RVal.WFList, RVal.WF]

/-! ### pass 5: `.clear()` — the dict mutator (docs/memory-model.md
§search()'s first blockers). Aliasing-visible, `None`-returning,
faithful arity TypeError; keyword arguments stay loud like `.get`. -/

#py_check dict_lab.clear_len(5) = 0
#py_check dict_lab.clear_alias(5) = 0
#py_check dict_lab.clear_get(5) = -7
#py_check dict_lab.clear_refill(5) = (Val.tuple #[.int 1, .int 8])
#py_check dict_lab.clear_none(3) = true
#py_check dict_lab.clear_arity(1) raises
  (.typeError "clear() takes no arguments (1 given)")
