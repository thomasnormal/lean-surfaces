/-
The `gen_moves` THEOREM — the STATEMENT, in the shape the owner decided
(docs/backlog.md §H4, "gen_moves THEOREM STATEMENT — decided (owner,
2026-08-09)", commit f536d93): of the three drafted shapes — rule-predicate
set-equality, equality against a reference enumeration, a property bundle —
(2) was picked, **equality against the reference enumeration with ORDER
pinned**, because `bound`'s cutoffs depend on move order.

Both halves of that equality already exist and are already CPython-checked:

* the LEFT side is `Position.gen_moves` running under the Lean semantics on
  the shipped `sunfish.py` — `pins_genmoves.lean` runs it on the opening
  board, a promotion board and a castling board and pins CPython's own
  moves in CPython's own order;
* the RIGHT side is `Ref.refMoves` — the naively-readable enumeration in
  `pins_genmoves.lean`, written one Lean line per Python line against
  sunfish.py 172-203, pinned against CPython on the opening board plus
  thirteen boards chosen for what random play does not reach.

What this file adds is the statement itself, `GenMovesEqRef`, plus the
run-and-drain shape it is stated over. It is a `Prop`-valued definition,
NOT a `sorry`ed theorem: the repo never lands a `sorry`, and a definition
records the claim exactly while leaving "proved" unclaimed. When the proof
lands, `theorem gen_moves_eq_ref : GenMovesEqRef` is the one line to add,
and nothing about the statement moves.

**What the proof still needs** (the honest gap, so the next session starts
from a plan rather than from a blank page):

1. **Ray agreement.** The model's generator, resumed inside one
   `for j in count(i + d, d)` ray, yields exactly `Ref.ray`'s list and then
   leaves the ray at exactly the same place. This is where the work is: the
   model side is the H4 step-indexed generator (a defunctionalized
   continuation over the shipped AST, six yield sites at three control-flow
   depths, `yield from` for the promotions), the reference side is a plain
   `Except`-valued recursion. Needs `Ref.ray`'s fuel monotonicity as a
   companion (the reference's budget and the interpreter's are different
   clocks, and only the reference's is allowed to be part of the claim).
2. **Square agreement**, by `directions[p]` order: `Ref.piece` is the
   flatten of the rays, and the generator visits the same directions in the
   same order — the dict read `directions[p]` on the shipped module has to
   be shown to agree with `Ref.directions p` (kernel-computable, six keys).
3. **Board agreement**: `for i, p in enumerate(self.board)` visits squares
   in index order, skipping every non-`"PNBRQK"` square, which is the outer
   `List.range b.length` scan — plus the `continue` arm, which is the model
   side's only flow subtlety at this level.
4. The drain-vs-fuel bookkeeping: `genMovesOf` runs at a single fuel `F` for
   both the call and the drain, so the threshold form (`∃ t, ∀ F ≥ t`) is
   what the splicing lemmas in the repo already speak.
-/
import Examples.python.sunfish.pins_genmoves

namespace Examples.python.sunfish.genmoves_theorem

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.pins_genmoves

/-- The shipped `Position` namedtuple, all six fields free. `gen_moves`
reads `board`, `wc`, `ep` and `kp`; `score` and `bc` ride along because a
Position value has them (and because the theorem must not quietly assume
anything about the fields the method does not read). -/
def posOf (b : String) (score : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) :
    RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str b, .int score, .tuple #[.bool wc0, .bool wc1],
      .tuple #[.bool bc0, .bool bc1], .int ep, .int kp]

/-- Drain a generator object to exhaustion, collecting the `Move` fields.
`none` is "the drain did not decide" — a step that refused, timed out, or
yielded something that is not a `Move` — so a short list can never be
mistaken for a finished one (`pins_genmoves.lean`'s private twin, public
here because the statement quantifies over it). -/
def drain (w : World) (a : Addr) : Nat → Option (List (Int × Int × String))
  | 0 => Option.none
  | n + 1 =>
    match stepIter sunfish 16384 w a with
    | .ok w' (some (.ntuple _ _ #[.int i, .int j, .str p])) =>
      (drain w' a n).map ((i, j, p) :: ·)
    | .ok _ Option.none => some []
    | _ => Option.none

/-- The MODEL's answer: call `Position.gen_moves` on the shipped file at
fuel `F` and drain the generator it returns. -/
def genMovesOf (F : Nat) (p : RVal) : Option (List (Int × Int × String)) :=
  match callIn sunfish F (initWorld sunfish) "Position.gen_moves" #[p] with
  | .ok w (.ref a) => drain w a F
  | _ => Option.none

/-- The REFERENCE's answer in the same shape. -/
def refTriples (ms : List Ref.RefMove) : List (Int × Int × String) :=
  ms.map fun m => (m.i, m.j, m.prom)

/-- **THE `gen_moves` THEOREM — the decided statement.**

For every position on which the reference enumeration has an answer, the
shipped `Position.gen_moves`, run under the Lean semantics and drained,
yields exactly that answer — the same moves in the same ORDER.

Two things are load-bearing in the shape:

* the reference's answer is a hypothesis (`Ref.refMoves … = .ok ms`), not a
  conclusion. The reference DECLINES (`Except.error`) on a board it cannot
  read and on an exhausted ray budget, so this hypothesis is where the
  board's well-formedness lives — nothing else in the statement has to
  mention padding, and no `.error` can be mistaken for a short move list.
* the fuel is a THRESHOLD (`∃ t, ∀ F ≥ t`), the total-correctness shape of
  every other judgment in the repo: the equality holds at every large enough
  fuel, so `timeout` is excluded rather than tolerated. -/
def GenMovesEqRef : Prop :=
  ∀ (b : String) (score : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (rf : Nat) (ms : List Ref.RefMove),
    Ref.refMoves b.toList wc0 wc1 ep kp rf = .ok ms →
    ∃ t, ∀ F ≥ t,
      genMovesOf F (posOf b score wc0 wc1 bc0 bc1 ep kp) = some (refTriples ms)

/-! ### The presentation lemmas the decomposition uses

`refTriples` distributes over the reference's own structure — the reference
is built by `flatten`ing per-square and per-ray lists, and the model side
arrives one yielded move at a time, so every step of the proof meets a
`refTriples (… ++ …)`. -/

@[simp] theorem refTriples_nil : refTriples [] = [] := rfl

@[simp] theorem refTriples_cons (m : Ref.RefMove) (ms : List Ref.RefMove) :
    refTriples (m :: ms) = (m.i, m.j, m.prom) :: refTriples ms := rfl

@[simp] theorem refTriples_append (l₁ l₂ : List Ref.RefMove) :
    refTriples (l₁ ++ l₂) = refTriples l₁ ++ refTriples l₂ := by
  simp [refTriples]

@[simp] theorem refTriples_flatten (ls : List (List Ref.RefMove)) :
    refTriples ls.flatten = (ls.map refTriples).flatten := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.flatten_cons, refTriples_append, ih, List.map_cons]

/-! ### The reference's budget — the next step, NOT claimed here

`Ref.ray` stands in for CPython's unbounded `count(i + d, d)` with a step
budget, and running out is an ERROR, never a truncated answer. The proof
needs that budget to be irrelevant once it is large enough, i.e.

    ray b wc0 wc1 ep kp i p d f j = .ok ms →
      ∀ f' ≥ f, ray b wc0 wc1 ep kp i p d f' j = .ok ms

— otherwise the theorem's `rf` would be part of the claim instead of an
artifact of writing the reference in Lean. It is a fuel-monotonicity lemma
of exactly the interpreter's `_mono` family shape, by induction on the
budget: everything in one ray step before the recursive call is
budget-free, so only the tail consumes the IH. It is NOT stated as a
theorem here because it is not proved here, and this repo does not land
`sorry` — the shape above is the specification for whoever picks it up
(the `do`-block over `Except` wants `Except.bind_eq_ok`-style decomposition
rather than a naive `cases` chain; that is the one thing a first attempt
gets wrong). -/

end Examples.python.sunfish.genmoves_theorem
