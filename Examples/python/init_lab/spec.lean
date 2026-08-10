import LeanModels

/-!
# init_lab — module-init execution (pass 3, checks-only example)

The live pipeline at lab scale (docs/memory-model.md §module-init
execution): the `.items()` shell mutates `tbl` through subscript stores,
the module-level lambda `pad` (ZERO captures — its body reads `base` and
the loop target `k` through the live globals at call time) is rebound
per iteration, `sum` folds a genexp of computed slices from the empty
tuple, and the post-loop `TOTAL`/`M` read the mutated state. The
STATICALLY-poisoned names (`tbl`'s stores, `k`, `pad`, `M`, `TOTAL`)
resolve through `World.globals` — the getters below pin the values
against CPython.

The hand-built module at the bottom pins the shell's faithful
`RuntimeError`: a body that INSERTS a key dies exactly like CPython's
dict_items iterator, and the pipeline ROLLS BACK — the table stays
poisoned, never half-mutated.
-/

open LeanModels LeanModels.Python

load_program init_lab from "Examples/python/init_lab/init_lab.json"

#py_check init_lab.get_a() =
  (Val.tuple #[.int 9, .int 0, .int 11, .int 0, .int 0, .int 12, .int 0])
#py_check init_lab.get_b() =
  (Val.tuple #[.int 9, .int 0, .int 103, .int 0, .int 0, .int 104, .int 0])
#py_check init_lab.get_total() = 11
#py_check init_lab.get_m() = 8
#py_check init_lab.get_k() = "b"
#py_check init_lab.call_pad(5) = (Val.tuple #[.int 0, .int 105, .int 0])

/-! ### The static/live split, pinned

`tbl`/`base` are fold-valued (the dict literals precede every exec
statement); the loop poisons `tbl` (stores), `k`, `row`, `pad`; the
post-divergence `TOTAL` (subscript reads) and `M` (reads the
while-bound `x`) are POISONED statically and VALUED in the live view —
the getters above already prove the live values; this pins the static
half. -/

#guard (lookupG (moduleGlobals init_lab).1 "TOTAL") == some Option.none
#guard (lookupG (moduleGlobals init_lab).1 "M") == some Option.none
#guard (lookupG (moduleGlobals init_lab).1 "pad") == some Option.none
#guard (Env.lookup (initWorld init_lab).globals "TOTAL") == some (RVal.int 11)
#guard (Env.lookup (initWorld init_lab).globals "M") == some (RVal.int 8)

/-! ### The items shell's faithful `RuntimeError` (hand-built)

`for kk, vv in d.items(): d["new"] = 5` — CPython raises
`RuntimeError: dictionary changed size during iteration` at the second
step. The shell reports exactly that; through the pipeline the failed
attempt ROLLS BACK and `d` stays poisoned (no half-mutation is ever
observable). -/

private def sp0 : Span := default

private def insLoop : Module :=
  { functions := #[], classes := #[], namedtuples := #[]
    topLevel := #[
      .assign #[.name "d" sp0]
        (.dict #[.constant (.str "a") sp0] #[.constant (.int 1) sp0] sp0) sp0,
      .forStmt (.tuple #[.name "kk" sp0, .name "vv" sp0] sp0)
        (.call (.attribute (.name "d" sp0) "items" sp0) #[] #[] Option.none sp0)
        #[.assign #[.subscript (.name "d" sp0) (.constant (.str "new") sp0) sp0]
            (.constant (.int 5) sp0) sp0] #[] sp0] }

#guard (match initFoldStep #[] [] (insLoop.topLevel.getD 1 (.pass sp0)) with
        | Option.none => true | _ => false)

#guard (match (let st := globalsStep #[] [] true false
                 (insLoop.topLevel.getD 0 (.pass sp0))
               initExecStmt { insLoop with topLevel := #[insLoop.topLevel.getD 0 (.pass sp0)] }
                 initExecFuel st.1 st.2.1 (insLoop.topLevel.getD 1 (.pass sp0))) with
        | .exn _ (.runtimeError _) => true
        | _ => false)

#guard (Env.lookup (initWorld insLoop).globals "d").isNone
