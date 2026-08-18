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
records the claim exactly while leaving "proved" unclaimed.

**STATE (2026-08-19).** Notes 1-3 below are landed (§L4/§L5, genmoves_ray.lean
and genmoves_scan.lean); note 4 was NOT true of the code, which made the
statement false on long boards, and the owner's repair — `drain` takes `F` —
is now in `drain` below, the ONLY change this statement has ever taken.
`Examples/python/sunfish/genmoves_drain.lean` proves the repaired statement
from two ground facts about `initWorld sunfish`
(`gen_moves_eq_ref_of_dirs`), and measures what those two cost the kernel;
`theorem gen_moves_eq_ref : GenMovesEqRef` is that theorem applied to two
`rfl`s, and it is the module INITIALIZER, not the generator, that has not
paid for them yet.

**What the proof needed** (the gap as it was written, kept because the plan
it names is what got followed):

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

/-- Drain a generator object to exhaustion at fuel `F`, collecting the
`Move` fields. `none` is "the drain did not decide" — a step that refused,
timed out, or yielded something that is not a `Move` — so a short list can
never be mistaken for a finished one (`pins_genmoves.lean`'s private twin,
public here because the statement quantifies over it).

**The fuel is a parameter, and that is the repair** (owner-decided,
2026-08-19). The frozen text ran every step at the CONSTANT `16384` while
the statement quantifies over an arbitrary board, which made the statement
false as written: on a board long enough that one step cannot cross it —
twenty thousand `'.'`, genmoves_scan.lean's counterexample — the reference
answers `.ok []`, the single `stepIter` times out, and the equality fails
at every `F`. Note 4 above always said `genMovesOf` "runs at a single fuel
`F` for both the call and the drain"; passing `F` here is that sentence,
finally in the code. -/
def drain (F : Nat) (w : World) (a : Addr) :
    Nat → Option (List (Int × Int × String))
  | 0 => Option.none
  | n + 1 =>
    match stepIter sunfish F w a with
    | .ok w' (some (.ntuple _ _ #[.int i, .int j, .str p])) =>
      (drain F w' a n).map ((i, j, p) :: ·)
    | .ok _ Option.none => some []
    | _ => Option.none

/-- The MODEL's answer: call `Position.gen_moves` on the shipped file at
fuel `F` and drain the generator it returns — one `F` for the call, for
every step of the drain, and for the number of steps the drain may take. -/
def genMovesOf (F : Nat) (p : RVal) : Option (List (Int × Int × String)) :=
  match callIn sunfish F (initWorld sunfish) "Position.gen_moves" #[p] with
  | .ok w (.ref a) => drain F w a F
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
theorem at?_ok_inv (l : List Char) (j : Int) (c : Char)
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

/-! ### Ray AGREEMENT (L4) — the ray, taken apart against the SHIPPED AST

Landing **L4** of docs/generator-tier-architecture.md, and the first thing
it did was correct the memo and the note that used to stand here. That note
said a suspended `gen_moves` inside a ray carries
`block … :: countFrom j d :: block … :: forSeq <directions[p]> :: enumSeq
<board> :: []`. **Measured, it does not.** Stepping the shipped generator
twice and printing the heap gives

```
[66] gen Position.gen_moves
       [block, forGen a₁, block, forSeq(3), block, forGen a₂, block]
[67] gen <enumerate> [enumSeq(82, …)]
[68] gen <count>     [countFrom(61, -10)]
```

`count(…)` and `enumerate(…)` are CALLS that ALLOCATE their own generator
object, and the consuming `for` pushes a **`forGen`** frame pointed at it.
A `countFrom` frame is never in `gen_moves`' own stack; it is the ray's
inner object's entire continuation, one `stepIter` below. So L2's
`genYieldsPrefix_countFrom` is not the ray rule — it is what the ray rule
consumes through the object bridge, and the rules the ray actually needs
(`iterSteps_countFrom`, `genSilent_delegateBreak`/`GenEmits.blockBreak`,
`GenEmits.forGenRound`/`forGenBreak`/`forGenDone`) are LeanModels/Python/
VCGen.lean §L4.

What lands here is the ray's FIRST LEAF, over an arbitrary board: the
square is blocked, so the model emits nothing and leaves the ray, and
`Ref.ray` says `[]`. It is one leaf of nine and it is stated in the shape
the whole ray will have (`ms.map moveVal`, so nothing about the statement
moves when the other leaves arrive) — docs/backlog.md §L4 prices them. -/

/-! #### The shipped ray, projected

Never retyped: every definition projects out of `sunfish`, so a changed
PROGRAM stops the `rfl`s loudly. -/

/-- The span a projection falls back to. Public because `genmoves_ray.lean`
projects the rest of the ray with the same kit. -/
def nowhere : Span := ⟨0, 0, 0, 0⟩

private def gmBody : List Stmt :=
  match findFunction sunfish "Position.gen_moves" with
  | some f => f.body.toList
  | none => []

private def stmt0 (ss : List Stmt) : Stmt :=
  match ss with | s :: _ => s | _ => .pass nowhere

private def forBody (s : Stmt) : List Stmt :=
  match s with | .forStmt _ _ b _ _ => b.toList | _ => []

private def forTarget (s : Stmt) : Expr :=
  match s with | .forStmt t _ _ _ _ => t | _ => .constant .none nowhere

/-- Positional projection into a statement list — public for the same
reason as `nowhere`. -/
def nth (n : Nat) (ss : List Stmt) : Stmt :=
  match n, ss with
  | 0, s :: _ => s
  | n + 1, _ :: r => nth n r
  | _, _ => .pass nowhere

/-- `for j in count(i + d, d): …` — the ray statement itself. -/
def gmRayS : Stmt := stmt0 (forBody (nth 1 (forBody (stmt0 gmBody))))
/-- **The ray body**, sunfish.py 184-203. -/
def gmRay : List Stmt := forBody gmRayS
/-- The ray's loop target, `j`. -/
def gmRayTarget : Expr := forTarget gmRayS
/-- `q = self.board[j]`. -/
def rQ : Stmt := nth 0 gmRay
/-- `if q in " \nPNBRQK": break` — the guard that ends this leaf. -/
def rStop : Stmt := nth 1 gmRay
/-- The six statements after the stop guard (the leaves still open). -/
def rRest : List Stmt := match gmRay with | _ :: _ :: r => r | _ => []

theorem gmRay_split : gmRay = rQ :: rStop :: rRest := rfl
theorem rQ_plan : genPlan rQ = .delegate := rfl
theorem rStop_plan : genPlan rStop = .delegate := rfl

theorem gmRayTarget_lit : ∃ s, gmRayTarget = .name "j" s := ⟨_, rfl⟩

theorem rQ_lit : ∃ s₁ s₂ s₃ s₄ s₅ s₆, rQ = .assign #[.name "q" s₁]
    (.subscript (.attribute (.name "self" s₂) "board" s₃) (.name "j" s₄) s₅) s₆ :=
  ⟨_, _, _, _, _, _, rfl⟩

theorem rStop_lit : ∃ s₁ s₂ s₃ s₄ s₅, rStop =
    .ifStmt (.compare (.name "q" s₁) #[.inOp] #[.constant (.str " \nPNBRQK") s₂] s₃)
      #[.brk s₄] #[] s₅ := ⟨_, _, _, _, _, rfl⟩

/-! #### The two statements, run at a SYMBOLIC board -/

theorem run_at_least {s : Stmt} {st st' : FrameState} {fl : Nat} {r : RFlow}
    (h : execStmt sunfish fl st s = .ok st' r) :
    ∃ t, ∀ F ≥ t, execStmt sunfish F st s = .ok st' r :=
  ⟨fl, fun F hF => execStmt_mono h (by simp) F hF⟩

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
/-- **`q = self.board[j]` at an arbitrary board and an arbitrary index.**
The board never becomes concrete: the attribute read resolves off the
`Position` namedtuple's field table and the subscript reduces through L1's
string family, so what is left is exactly Python's negative-index fold —
which `at?_ok_inv` supplies, because it is the same fold the reference
performs. -/
theorem rQ_run (w : World) (env : REnv) (b : String) (score ep kp jv : Int)
    (wc0 wc1 bc0 bc1 : Bool) (c : Char)
    (hself : Env.lookup env "self" = some (posOf b score wc0 wc1 bc0 bc1 ep kp))
    (hj : Env.lookup env "j" = some (.int jv))
    (href : Ref.at? b.toList jv = .ok c) :
    execStmt sunfish 16 ⟨w, env⟩ rQ
      = .ok ⟨w, Env.set env "q" (.str (String.singleton c))⟩ .next := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, hlit⟩ := rQ_lit
  rw [hlit]
  py_simp [sunfish, posOf, hself, hj]
  obtain ⟨k, hkeq, hk0, hklt, hget⟩ := at?_ok_inv b.toList jv c href
  rw [show (b.length : Int) = (b.toList.length : Int) from by rw [strLength_eq_toList],
    hkeq, if_pos ⟨hk0, hklt⟩]
  refine ⟨_, rfl, ?_⟩
  rw [hget]
  rfl

set_option maxHeartbeats 1600000 in
/-- **`if q in " \nPNBRQK": break` at a symbolic character.** The guard
collapses to `strContains` on a one-character needle, which is L1's
`strContains_singleton` — and `Ref.inStr` is definitionally the same list
`contains`, so the two sides of the guard meet with no case split over the
literal alphabet. -/
theorem rStop_run (w : World) (env : REnv) (c : Char)
    (hq : Env.lookup env "q" = some (.str (String.singleton c)))
    (hstop : Ref.inStr c " \nPNBRQK" = true) :
    execStmt sunfish 16 ⟨w, env⟩ rStop = .ok ⟨w, env⟩ .brk := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, hlit⟩ := rStop_lit
  rw [hlit]
  have hc : strContains " \nPNBRQK" (String.singleton c) = true := by
    rw [strContains_singleton]; exact hstop
  py_simp [hq, hc]

/-! #### The leaf, and the agreement -/

/-- The `Move` namedtuple value the generator yields for a reference move —
the marshalling the whole ray theorem is stated through. -/
def moveVal (m : Ref.RefMove) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int m.i, .int m.j, .str m.prom]

/-- The REFERENCE's stop leaf: a blocked square ends the ray with no
moves. -/
theorem ray_stop_nil (b : List Char) (wc0 wc1 : Bool) (ep kp i : Int) (p : Char)
    (d : Int) (f : Nat) (jv : Int) (c : Char) (ms : List Ref.RefMove)
    (href : Ref.at? b jv = .ok c) (hstop : Ref.inStr c " \nPNBRQK" = true)
    (hray : Ref.ray b wc0 wc1 ep kp i p d (f + 1) jv = .ok ms) : ms = [] := by
  rw [Ref.ray] at hray
  simp only [bind, Except.bind, href, hstop, if_pos] at hray
  exact (Except.ok.inj hray).symm

set_option maxHeartbeats 1600000 in
/-- **RAY AGREEMENT AT THE STOP LEAF, over an ARBITRARY board.**

The shipped `Position.gen_moves`, suspended in a ray at the `count` object
`a` holding `j`, on a board whose square `j` the reference reads as a
blocker: the generator emits exactly the moves `Ref.ray` reports (none),
and leaves the ray frame with the count advanced and `j`/`q` bound.

Nothing is concrete: the board is a free `String`, the square a free `Int`
(the negative-index fold included), the character free, the world and the
frame free apart from the two lookups the statement actually performs.
This is the first fact in the repo relating the MODEL's generator to the
reference enumeration — L1's `at?_eq_indexVal` related their board READS;
this relates what they PRODUCE. -/
theorem ray_stop_agrees
    (w : World) (env : REnv) (a : Addr) (h₂ : Heap)
    (b : String) (score ep kp i jv d : Int) (wc0 wc1 bc0 bc1 : Bool)
    (p c : Char) (f : Nat) (ms : List Ref.RefMove)
    (hself : Env.lookup env "self" = some (posOf b score wc0 wc1 bc0 bc1 ep kp))
    (hcount : Heap.get? w.heap a = some (countObj jv d))
    (hback : Heap.update w.heap a (countObj (jv + d) d) = some h₂)
    (href : Ref.at? b.toList jv = .ok c)
    (hstop : Ref.inStr c " \nPNBRQK" = true)
    (hray : Ref.ray b.toList wc0 wc1 ep kp i p d (f + 1) jv = .ok ms) :
    GenEmits sunfish ⟨w, env⟩ [.forGen gmRayTarget a gmRay] (ms.map moveVal)
      ⟨{ w with heap := h₂ },
        Env.set (Env.set env "j" (.int jv)) "q" (.str (String.singleton c))⟩ := by
  obtain ⟨sj, htgt⟩ := gmRayTarget_lit
  rw [ray_stop_nil b.toList wc0 wc1 ep kp i p d f jv c ms href hstop hray]
  refine GenEmits.forGenBreak (v := .int jv) (w' := { w with heap := h₂ })
    (env₁ := Env.set env "j" (.int jv)) (iterSteps_countFrom hcount hback)
    (by rw [htgt]; rfl) ?_
  have hself₁ : Env.lookup (Env.set env "j" (RVal.int jv)) "self"
      = some (posOf b score wc0 wc1 bc0 bc1 ep kp) := by
    rw [Env.lookup_set_ne _ (by decide), hself]
  have hj₁ : Env.lookup (Env.set env "j" (RVal.int jv)) "j" = some (.int jv) :=
    Env.lookup_set_self _ _ _
  refine GenEmits.silent
    (pre₁ := [GenFrame.block (rStop :: rRest), GenFrame.forGen gmRayTarget a gmRay])
    (fun k => by
      simpa [gmRay_split] using genSilent_delegate (m := sunfish) (s := rQ)
        (ss := rStop :: rRest) (k := [GenFrame.forGen gmRayTarget a gmRay] ++ k) rQ_plan
        (run_at_least (rQ_run { w with heap := h₂ } (Env.set env "j" (.int jv)) b
          score ep kp jv wc0 wc1 bc0 bc1 c hself₁ hj₁ href))) ?_
  exact GenEmits.blockBreak (pre := [GenFrame.forGen gmRayTarget a gmRay]) rStop_plan
    (fun _ => rfl)
    (run_at_least (rStop_run { w with heap := h₂ }
      (Env.set (Env.set env "j" (.int jv)) "q" (.str (String.singleton c))) c
      (Env.lookup_set_self _ _ _) hstop))

/-! Non-vacuity, on the shipped opening board: square 91 holds our own rook
(a BLOCKER — the ray stops), square 71 is empty (it does NOT), so both arms
of `ray_stop_agrees`' hypothesis are reachable and neither is vacuous. -/

#guard (match Ref.at? board0.toList 91 with
        | .ok c => Ref.inStr c " \nPNBRQK"
        | _ => false) == true

#guard (match Ref.at? board0.toList 71 with
        | .ok c => Ref.inStr c " \nPNBRQK"
        | _ => true) == false

/-! ### What the rest of the ray costs, and why it is recorded not attempted

`rRest` is six statements — the pawn block (`.branch`, with the inlined
`yield from` inside it), the unconditional `yield`, the crawler guard and
the two castling `.branch`es — and `Ref.ray` has eight more leaves. Every
one of them is the same three moves as above (project the statement, run it
at a symbolic board, splice the frame rule), so the shape is settled; what
is NOT settled is the state threading, because from the `yield` on the ray
CONTINUES and the invariant has to carry `i`, `p`, `d`, the advancing count
object and the board across rounds. `GenEmits.forGenRound` is the rule for
that and it is landed; the induction over rounds is the work.
docs/backlog.md §L4 carries the measured per-statement cost. -/

end Examples.python.sunfish.genmoves_theorem
