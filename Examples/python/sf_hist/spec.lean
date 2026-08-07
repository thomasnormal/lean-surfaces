/-
Examples/python/sf_hist — three-file example layout. sunfish's
history/list patterns at the H2 tier: the driving loop's `hist` list
threaded BY REFERENCE through the search machinery (`hist.append` in a
callee, `hist[-1]` reads, in-place score updates), stated with `CallsIn`
(the stateful judgment — the argument vectors carry `.ref`s into a known
before-world, exactly what the public `CallsTo` boundary cannot express
before the H2 boundary flip).

The headline is `poke_first`: the SAME function, called once with two
references to ONE list and once with references to two structurally-equal
but DISTINCT lists, returns different values — the write through `a`
is visible through `b` exactly when they alias. Under value semantics
(`Val.listV`) the two calls were indistinguishable; this pair is the H2
acceptance behavior as a theorem, including a value-symbolic form
(`poke_first_aliased_symbolic`: the aliased write erases the initial
value — ∀ n, the result is 99).
-/
import Examples.python.sf_hist.proof

open LeanModels LeanModels.Python

load_program sf_hist from "Examples/python/sf_hist/sf_hist.json"

/-! Non-vacuity: the public boundary runs the whole driving-loop shape
(`drive` seeds, pushes twice through nested calls sharing the world, and
reads back — values pinned against CPython 3.9). -/
#py_check sf_hist.drive(3) = (Val.tuple #[.int 3, .int 5])
#py_check sf_hist.drive(0) = (Val.tuple #[.int 3, .int 2])
#py_check sf_hist.drive(-2) = (Val.tuple #[.int 3, .int 0])

/-! The recorded H2 boundary gap, pinned loudly: a boundary-passed list
still thaws to the transitional VALUE form, so mutating it refuses
(never wrong) until the boundary flip (docs/memory-model.md §staging). -/
#guard callFunction sf_hist "push" #[.list #[.int 5], .int 6] 4096
  matches .unsupported _
#guard callFunction sf_hist "current" #[.list #[.int 5, .int 8]] 4096
  == .ok (.int 8)

/-! ### The stateful specs (`CallsIn` — before-world, after-world) -/

/-- One history entry (`[5]` at address 0). -/
private def wA : World := ⟨#[.list #[.int 5]], [], []⟩
/-- After `push(hist, 6)`. -/
private def wB : World := ⟨#[.list #[.int 5, .int 6]], [], []⟩

/-- The driving loop's append: `push(hist, 6)` grows the CALLER's list in
place — the length is returned, the mutation is in the world. -/
theorem push_callsIn :
    CallsIn sf_hist wA "push" #[.ref 0, .int 6] wB (.int 2) := by
  proofs

/-- `hist[-1]` reads the just-pushed entry — world untouched. -/
theorem current_callsIn :
    CallsIn sf_hist wB "current" #[.ref 0] wB (.int 6) := by
  proofs

/-- One list, aliased arguments. -/
private def wOne : World := ⟨#[.list #[.int 1, .int 2]], [], []⟩
private def wOne' : World := ⟨#[.list #[.int 99, .int 2]], [], []⟩
/-- Two structurally-equal but DISTINCT lists. -/
private def wTwo : World :=
  ⟨#[.list #[.int 1, .int 2], .list #[.int 1, .int 2]], [], []⟩
private def wTwo' : World :=
  ⟨#[.list #[.int 99, .int 2], .list #[.int 1, .int 2]], [], []⟩

/-- **Aliasing, positive half**: `a` and `b` are the SAME list — the
write through `a` is read back through `b` (result 99). -/
theorem poke_first_aliased :
    CallsIn sf_hist wOne "poke_first" #[.ref 0, .ref 0] wOne' (.int 99) := by
  proofs

/-- **Aliasing, negative half**: structurally equal but DISTINCT lists —
the same call reads `b` untouched (result 1). Together with the positive
half: identity is observable through mutation, the exact behavior value
semantics could never state. -/
theorem poke_first_distinct :
    CallsIn sf_hist wTwo "poke_first" #[.ref 0, .ref 1] wTwo' (.int 1) := by
  proofs

/-- Value-symbolic aliasing: whatever `n` sat in the aliased slot, the
write erases it — the result is 99 for EVERY initial value (symbolic
heap contents through the walker-independent `callIn` route). -/
theorem poke_first_aliased_symbolic (n : Int) :
    CallsIn sf_hist ⟨#[.list #[.int n, .int 0]], [], []⟩ "poke_first"
      #[.ref 0, .ref 0] ⟨#[.list #[.int 99, .int 0]], [], []⟩ (.int 99) := by
  proofs

/-- In-place mutator returning `None` (acceptance case 17 at lists):
`rotate_scores` negates every entry of the caller's list; its entire
meaning is the world pair. -/
theorem rotate_scores_callsIn :
    CallsIn sf_hist ⟨#[.list #[.int 1, .int (-2), .int 3]], [], []⟩
      "rotate_scores" #[.ref 0]
      ⟨#[.list #[.int (-1), .int 2, .int (-3)]], [], []⟩ .none := by
  proofs

/-- Any decided `rotate_scores` outcome IS that world pair
(`CallsIn.functional` — fuel monotonicity at the `callIn` conjunct). -/
theorem rotate_scores_functional {w' : World} {v : RVal}
    (h : CallsIn sf_hist ⟨#[.list #[.int 1, .int (-2), .int 3]], [], []⟩
      "rotate_scores" #[.ref 0] w' v) :
    v = .none ∧ w' = ⟨#[.list #[.int (-1), .int 2, .int (-3)]], [], []⟩ := by
  proofs
