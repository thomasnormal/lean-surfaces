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

/-! ### The ray leg, factored

`Ref.ray` stands in for CPython's unbounded `count(i + d, d)` with a step
budget, and running out is an ERROR, never a truncated answer. Everything
below comes off ONE characterization, which is the shape worth having:
the ray's body either IGNORES its tail (every leaf that breaks the ray)
or MAPS one fixed function over it (the single leaf that continues).

That single fact is also what an earlier attempt got wrong, recorded here
because it looks right: casing on the recursive call and refuting the
`.error` branch is UNPROVABLE. A ray that breaks on its first guard
returns `[]` without ever forcing the tail, so `body (.error e) = .ok []`
is perfectly satisfiable. Going THROUGH the characterization instead of
around it turns that obstacle into the tool. -/

/-- Inversion of a successful `Except` bind — the primitive every tactic
on a `do`-block over `Except` stalls without (core's simp set has no
equivalent). -/
theorem exceptBind_ok {ε α β} {x : Except ε α} {g : α → Except ε β} {c : β} :
    (x >>= g) = .ok c ↔ ∃ a, x = .ok a ∧ g a = .ok c := by
  cases x <;> simp [bind, Except.bind]

/-- Inversion of a successful `Except` map. -/
theorem exceptMap_ok {ε α β} {x : Except ε α} {g : α → β} {c : β} :
    (g <$> x) = .ok c ↔ ∃ a, x = .ok a ∧ g a = c := by
  cases x <;> simp [Functor.map, Except.map]

theorem bind_pure_eq_map {ε α β} (g : α → β) (x : Except ε α) :
    (x >>= fun a => pure (g a)) = g <$> x := by cases x <;> rfl

open Ref in
/-- `Ref.ray`'s body with the RECURSIVE CALL abstracted as `tail` —
transcribed verbatim, which is what makes `ray_step` hold by `rfl`. -/
def rayBody (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (i : Int) (p : Char)
    (d : Int) (j : Int) (tail : Except String (List RefMove)) :
    Except String (List RefMove) := do
  let q ← at? b j
  if inStr q " \nPNBRQK" then return []
  match ← pawnBreak b ep kp i p q d j with
  | some ms => return ms
  | none =>
    let here : RefMove := ⟨i, j, ""⟩
    if inStr p "PNK" || inStr q "pnbrqk" then return [here]
    let castle1 ← if i == A1 then
        (do if (← at? b (j + E)) == 'K' && wc0 then
              return [(⟨j + E, j - E, ""⟩ : RefMove)] else return [])
      else pure []
    let castle2 ← if i == H1 then
        (do if (← at? b (j + W)) == 'K' && wc1 then
              return [(⟨j + W, j - W, ""⟩ : RefMove)] else return [])
      else pure []
    let rest ← tail
    return here :: castle1 ++ castle2 ++ rest

open Ref in
/-- One step of the ray IS the body applied to the rest of the ray. -/
theorem ray_step (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int) (p : Char)
    (d : Int) (f : Nat) (j : Int) :
    ray b wc0 wc1 ep kp i p d (f + 1) j
      = rayBody b wc0 wc1 ep kp i p d j (ray b wc0 wc1 ep kp i p d f (j + d)) :=
  rfl

open Ref in
set_option maxHeartbeats 2000000 in
/-- **The characterization.** Every leaf of the ray body either returns a
value that does not mention the tail, or returns one fixed function mapped
over it. The proof is the leaf enumeration itself: unfold, split every
guard, and each leaf closes by `rfl` on one side or the other. -/
theorem rayBody_map_or_const (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d : Int) (j : Int) :
    (∃ r, ∀ t, rayBody b wc0 wc1 ep kp i p d j t = r) ∨
    (∃ g : List RefMove → List RefMove,
        ∀ t, rayBody b wc0 wc1 ep kp i p d j t = g <$> t) := by
  unfold rayBody
  simp only [bind, Except.bind]
  repeat' split
  all_goals
    first
      | exact Or.inl ⟨_, fun t => rfl⟩
      | exact Or.inr ⟨_, fun t => by cases t <;> rfl⟩

open Ref in
set_option maxHeartbeats 2000000 in
/-- **The budget lemma**: an answer at budget `f` is the same answer at
every larger budget, so the reference's step budget is an artifact of
writing it in Lean and not part of what `GenMovesEqRef` claims. Three
lines off the characterization — the constant leaves are equal outright,
the map leaf consumes the induction hypothesis. -/
theorem ray_mono (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int) (p : Char)
    (d : Int) :
    ∀ (f : Nat) (j : Int) (ms : List RefMove) (k : Nat),
      ray b wc0 wc1 ep kp i p d f j = .ok ms →
      ray b wc0 wc1 ep kp i p d (f + k) j = .ok ms := by
  intro f
  induction f with
  | zero => intro j ms k h; simp [ray] at h
  | succ f ih =>
    intro j ms k h
    rw [show f + 1 + k = (f + k) + 1 from by omega, ray_step]
    rw [ray_step] at h
    rcases rayBody_map_or_const b wc0 wc1 ep kp i p d j with ⟨r, hconst⟩ | ⟨g, hmap⟩
    · rw [hconst] at h ⊢; exact h
    · rw [hmap] at h ⊢
      obtain ⟨a, ha, hga⟩ := exceptMap_ok.mp h
      rw [ih (j + d) a k ha, ← hga]
      rfl

open Ref in
/-- The budget lemma in the threshold form the rest of the repo speaks. -/
theorem ray_at_least (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int)
    (p : Char) (d : Int) (f : Nat) (j : Int) (ms : List RefMove)
    (h : ray b wc0 wc1 ep kp i p d f j = .ok ms) :
    ∀ f' ≥ f, ray b wc0 wc1 ep kp i p d f' j = .ok ms := by
  intro f' hf'
  obtain ⟨k, rfl⟩ : ∃ k, f' = f + k := ⟨f' - f, by omega⟩
  exact ray_mono b wc0 wc1 ep kp i p d f j ms k h

/-! ### The first bridge between the reference and the model (L1)

`Ref.at?` is the reference's board read, spelled over `List Char`; the
interpreter's is `indexVal` on a `.str`. They agree — and the proof is the
string-as-list family (VCTactic.lean §strings as lists of characters),
which is the whole point of that family: every string operation in the
tier is defined through `String.toList`, so a symbolic board reasons as
the character list it wraps.

This is the standalone gate of landing L1 in
docs/generator-tier-architecture.md. It is stated over an ARBITRARY board
and an arbitrary index — no concreteness anywhere — and it is the shape a
future ray-agreement proof consumes each time it reads a square. -/

open Ref in
/-- Inversion of a successful reference read: it took the in-range arm, and
the character came out of the character list at the folded index. -/
private theorem at?_ok_inv (l : List Char) (j : Int) (c : Char)
    (h : at? l j = .ok c) :
    ∃ k : Int, (if j < 0 then j + (l.length : Int) else j) = k ∧
      0 ≤ k ∧ k < (l.length : Int) ∧ l[k.toNat]? = some c := by
  rw [at?] at h
  by_cases hr : 0 ≤ (if j < 0 then j + (l.length : Int) else j) ∧
      (if j < 0 then j + (l.length : Int) else j) < (l.length : Int)
  · rw [if_pos hr] at h
    refine ⟨_, rfl, hr.1, hr.2, ?_⟩
    cases hg : l[(if j < 0 then j + (l.length : Int) else j).toNat]? with
    | none => rw [hg] at h; simp at h
    | some c' => rw [hg] at h; simpa using h
  · rw [if_neg hr] at h; simp at h

open Ref in
/-- At any index the reference accepts, the model's subscript reads the
same character (as the one-character string Python gives back). -/
theorem at?_eq_indexVal (b : String) (j : Int) (c : Char)
    (href : at? b.toList j = .ok c) :
    indexVal (.str b) (.int j) = .ok (.str (String.singleton c)) := by
  obtain ⟨k, hkeq, hk0, hklt, hget⟩ := at?_ok_inv b.toList j c href
  have hnorm : normIndex j b.length = some k.toNat := by
    simp only [normIndex, strLength_eq_toList, hkeq]
    rw [if_pos ⟨hk0, hklt⟩]
  have hgd : b.toList.getD k.toNat ' ' = c := by
    rw [List.getD_eq_getElem?_getD, hget]; rfl
  simp only [indexVal, asInt, hnorm, hgd]

/-! Non-vacuity: the bridge on the shipped opening board, at a square that
holds a piece (CPython's `initial[91] == "R"`). -/
#guard (match indexVal (.str board0) (.int 91) with
        | .ok (.str s) => s.toList
        | _ => []) == ['R']

#guard (match Ref.at? board0.toList 91 with
        | .ok c => [c]
        | _ => []) == ['R']

/-! ### Ray AGREEMENT — measured, and blocked on tooling, not on effort

With the budget lemma in hand the next step was the other half of the ray
leg: the model's generator, resumed inside one
`for j in count(i + d, d)`, yields exactly `Ref.ray`'s list. It does not
land here, and the reason is worth more than another attempt.

**Stating it is fine.** A suspended `gen_moves` is a `GenCont`, a STACK of
`GenFrame`s (Runtime.lean), and inside a ray that stack is concrete in
shape: `block <rest of the ray body> :: countFrom j d :: block … ::
forSeq <directions[p]> … :: enumSeq <the board> :: []`. "Resume until the
`countFrom` frame is popped" is expressible against that.

**Proving it needs a symbolic-execution calculus for the GENERATOR tier,
which does not exist.** The statement quantifies over an arbitrary board,
so every `self.board[j]` is a subscript on a SYMBOLIC 120-character
string and every guard (`q in " \nPNBRQK"`, `p == "P"`, `A8 <= j <= H8`)
is a comparison on a symbolic character. Nothing reduces; the proof would
have to case-split the interpreter by hand at every step. That is exactly
the work `py_vcgen` does for the heap-free fragment — and the walker has
no generator case, layer 2 has no triple over `stepIter`/`execGen`, and
the only generator-level lemmas in the repo are `stepIter_mono` and the
clock-erasure one. Checked, not assumed.

So the flagship's remaining distance is a TOOLING distance, and it is
bigger than the leg it blocks: a `PyGenTriple` layer over `execGen` (yield
sites as postcondition arms, the frame stack as the state), a walker case
that consumes it, and symbolic string/char reasoning for the guards.
Recorded rather than started, and deliberately not attempted piecemeal:
the same wall stands in front of the square-agreement and board-scan legs,
because both also quantify over an arbitrary board.

What IS closed by this file: the reference side is now a settled object —
factored, characterized, and budget-free — so when that tooling exists the
agreement proof meets a fixed target instead of a moving one. -/

end Examples.python.sunfish.genmoves_theorem
