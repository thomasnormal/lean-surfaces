/-
**The module-literal transport, measured** — why `gen_moves_drains_ref` does
NOT transport from `sunfish` to `sf_order` (docs/backlog.md §L9).

`Examples/python/sunfish/genmoves_drain.lean` proves the whole-drain bridge for
the `sunfish` module literal, and §L8's blocker record said `sf_order`'s
`bound_probe` needs it here, "`sf_order`'s method body being the same text —
but a different `Module` LITERAL, so the sunfish chain does not transfer
without a module-transfer argument."

**The premise is false, and this file is the evidence.** The two
`Position.gen_moves` are not the same text. Modulo spans (which the `_lit`
pin discipline already quantifies away) their ASTs agree everywhere EXCEPT the
pawn-capture guard:

* shipped `sunfish.py` (and `Examples/python/sunfish/sunfish.py`, which is
  VERBATIM the shipped file):
  `if d in (N + W, N + E) and q == "." and j != self.ep and abs(j - self.kp) > 1: break`
  — a FOUR-conjunct `and`;
* `Examples/python/sf_order/sf_order.py`:
  `if d in (N + W, N + E) and q == "." and j not in (self.ep, self.kp, self.kp - 1, self.kp + 1): break`
  — a THREE-conjunct `and` whose third conjunct is a `not in` over a 4-tuple.

The two guards are equivalent on integers; they are not the same AST, and
`ray_pawn_cap_prom_agrees` (genmoves_ray.lean) is proved *about the sunfish
one*. So there is nothing to transport: neither a module-parametric
restatement (its hypothesis "the module's `gen_moves` is this AST" is FALSE at
`sf_order`) nor a re-run of the captured chain (the pawn-capture arm's leaves
are about a guard that is not there).

`Position.value` diverges the same way — `q.islower()` where the shipped file
has `q in "pnbrqk"` — so the ordering line's other half is in the same
position.

**What this costs and what fixes it.** The divergence is ONE arm, not the
3740-line ray development: everything else in `gen_moves` is span-identical.
The cheap repair is to make `sf_order.py`'s two methods verbatim again and
re-extract — the fixture's own `spec.lean` already CLAIMS they are verbatim
("`Position.gen_moves` and `Position.value` are VERBATIM from the shipped
sunfish.py"), so that claim is a model-vs-code divergence today. That is an
owner call (it re-ingests the fixture and re-runs its pinned CPython answers),
which is why this file records the measurement instead of making the edit.
-/
import Examples.python.sunfish.genmoves_drain
import Examples.python.sf_order.proof

namespace Examples.python.sf_order.transport

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem
open Examples.python.sunfish.genmoves_scan
open Examples.python.sunfish.genmoves_ray

set_option maxRecDepth 100000

/-! ## The same projection path, in both modules -/

private def forBody (s : Stmt) : List Stmt :=
  match s with | .forStmt _ _ b _ _ => b.toList | _ => []
private def ifBody (s : Stmt) : List Stmt :=
  match s with | .ifStmt _ b _ _ => b.toList | _ => []
private def ifTest (s : Stmt) : Expr :=
  match s with | .ifStmt t _ _ _ => t | _ => .constant .none ⟨0, 0, 0, 0⟩
private def andArgs (e : Expr) : Array Expr :=
  match e with | .boolOp .and a _ => a | _ => #[]
private def stmt0 (ss : List Stmt) : Stmt :=
  match ss with | s :: _ => s | _ => .pass ⟨0, 0, 0, 0⟩
private def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match n, ss with
  | 0, s :: _ => s
  | n + 1, _ :: r => nth n r
  | _, _ => .pass ⟨0, 0, 0, 0⟩

/-- `sf_order`'s `Position.gen_moves`, and the same walk down to the ray body
that `genmoves_theorem.lean` takes in `sunfish`. -/
def sfGmB : List Stmt :=
  match findFunction sf_order "Position.gen_moves" with
  | some f => f.body.toList
  | none => []
def sfGmRay : List Stmt := forBody (stmt0 (forBody (nth 1 (forBody (stmt0 sfGmB)))))
/-- The pawn block, `if p == "P": …` — statement 2 of the ray body in both. -/
def sfPawn : Stmt := nth 2 sfGmRay
def sfPawnB : List Stmt := ifBody sfPawn
def gmPawnB : List Stmt := ifBody rPawn
/-- The pawn-capture guard — statement 2 of the pawn block in both. -/
def sfEpGuard : Stmt := nth 2 sfPawnB
def gmEpGuard : Stmt := nth 2 gmPawnB
/-- The promotion arm — `if A8 <= j <= H8:`'s first statement in both. -/
def sfProm : Stmt := stmt0 (ifBody (nth 3 sfPawnB))
def gmProm : Stmt := stmt0 (ifBody (nth 3 gmPawnB))

/-- Both bodies are one statement (the `enumerate` scan) and both ray bodies
are seven — the projection lands in the same place on both sides. -/
theorem shapes_line_up : sfGmB.length = 1 ∧ gmB.length = 1 ∧
    sfGmRay.length = 7 ∧ gmRay.length = 7 ∧
    sfPawnB.length = 4 ∧ gmPawnB.length = 4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The promotion arm is the SAME, modulo spans

§L8 read the shipped `yield from (Move(i, j, prom) for prom in "NBRQ")` as a
lowered generator EXPRESSION and expected it to be the hard half. Ingestion
desugars it to the same `for`/`yield` the reformatted fixture writes by hand,
so this arm needs nothing: one skeleton, two instances. -/

/-- The promotion arm's shape, as a function of its nine spans. -/
def promShape (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Span) : Stmt :=
  .forStmt (.name "prom" s₁) (.constant (.str "NBRQ") s₂)
    #[.yieldStmt (.call (.name "Move" s₃)
        #[.name "i" s₄, .name "j" s₅, .name "prom" s₆] #[] Option.none s₇) s₈] #[] s₉

theorem sf_prom_shape : ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉,
    sfProm = promShape s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

theorem sun_prom_shape : ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉,
    gmProm = promShape s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-! ## The pawn-capture guard is NOT the same

The conjunct census is enough: three against four, at the same position of the
same statement of the same method. No renaming of spans closes that. -/

theorem sf_guard_conjuncts : (andArgs (ifTest sfEpGuard)).size = 3 := rfl
theorem sun_guard_conjuncts : (andArgs (ifTest gmEpGuard)).size = 4 := rfl

/-- **THE MEASUREMENT.** The shipped `Position.gen_moves` and `sf_order`'s are
different programs, so `gen_moves_drains_ref` has no transport to `sf_order` —
parametric or re-run. -/
theorem ep_guard_differs : sfEpGuard ≠ gmEpGuard := by
  intro h
  have h3 := sf_guard_conjuncts
  rw [h, sun_guard_conjuncts] at h3
  exact absurd h3 (by decide)

/-- …and therefore the two method bodies are different, which is the
hypothesis a module-parametric restatement of the drain theorem would have to
discharge at `sf_order`. -/
theorem gen_moves_bodies_differ : sfGmB ≠ gmB := by
  intro h
  refine ep_guard_differs ?_
  simp only [sfEpGuard, gmEpGuard, sfPawnB, gmPawnB, sfPawn, sfGmRay, h]
  rfl

#print axioms ep_guard_differs
#print axioms gen_moves_bodies_differ

end Examples.python.sf_order.transport
