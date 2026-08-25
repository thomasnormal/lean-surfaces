-- LEGACY: statement target of pre-rebuild theorems; compiles, refuses what
-- it does not implement, gains no consumers; deleted when re-founded.
import LeanModels.Python.VC2

/-! # Payload blindness — the interpreter cannot see a RUNNING generator's payload

docs/backlog.md §"L6 LANDED" stated `PayloadBlind` in VCGen.lean and priced
its proof; §L7 proved it, so the definition lives here and VCGen.lean's
generator calculus imports this module. The claim: for a slot `a` holding
`.generator qname locals cont .running`, a decided interpreter run (1)
leaves the slot exactly as it found it and (2) runs identically when the
payload is replaced by any other `locals`/`cont` at the same `qname`.

**STATUS — PROVED.** `payloadBlind` (bottom of this file) is
`∀ m, PayloadBlind m`, on `propext`/`Classical.choice`/`Quot.sound` and
nothing else: no `sorry`, no `native_decide`, no side condition, no
consumer-side hypothesis. What carries it is the factoring (§Tier A/C),
every helper equation the block reaches (§Tier B — thirty-eight of them,
plus a slot-preservation lemma for each helper that answers a NEW heap), all
EIGHTEEN interpreter arms (§Tier D — one standalone `_succ` theorem per
member of Semantics.lean:4232-6207), the block's induction on fuel
(`pbAll`), and the reduction `payloadBlind_of_execGen`, which is the point
of the module: both of `PayloadBlind`'s conjuncts come from ONE instance of
the `execGen` conjunct — stability at the identity twin, transport at the
swap the consumer names.

**Why it is true.** `stepIter` is the interpreter's ONLY reader of a
generator object's `locals`/`cont` fields, and its `.running` arm answers
`.valueError "generator already executing"` before reaching either. Every
other occurrence of `Obj.generator` in the semantics binds neither field.

**The factoring** (the shape finding of this landing, against §L6's price).
The perturbation is FUNCTIONAL — `Heap.update h a o` is `Array.set` under a
bounds check, so its total twin `Heap.swapAt` makes the perturbed heap a
FUNCTION of the original rather than a relation. That collapses the "two
runs at two merely-related worlds" problem, which is what priced this proof
at ClockErase scale, into a one-directional relation on runs:

    PBF a o₀ o x y  ≈  x decided ⇒ (the slot still reads o₀) ∧ y = x.swapAt

whose `bind`/`bindE`/`liftRes`/`ite`/`toWorld`/`withLocals` congruences are
proved once (§Tier C) and consumed by the arms (§Tier D). `.timeout` and
`.unsupported` constrain nothing, exactly as `ClockErasedF` leaves its
refusals free — nothing in the block converts either back to a decision.
Because the relation is functional, the per-helper obligations are plain
EQUATIONS (`f (Heap.swapAt h a o) … = f h …`, §Tier B) rather than two-world
simulations, which is what brings the helper tier into reach: four lines
apiece for the readers, and for the seven that answer a NEW heap a
`map`-shaped equation (`f (Heap.swapAt h a o) … = Res.mapOk (Heap.swapAt ·
a o) (f h …)`) that `Heap.update_swapAt_ne` discharges.

Geometry mirrors ClockErase.lean: swap algebra, the relation and its
combinators, per-helper blindness, then the mutual induction on fuel. -/

namespace LeanModels.Python

open scoped Run

/-! ## Tier A — the single-slot swap and its algebra

`Heap.swapAt` is `Heap.update`'s TOTAL twin: same bounds check, same
`Array.set`, `h` itself when the address is dead. Totality is what makes
the perturbed run a FUNCTION of the original. -/

/-- Replace the object at `a`; `h` itself if `a` is dead. `Heap.update`'s
total twin, and `Array.setIfInBounds` is exactly that bounds discipline.
Full name only at every use site — `Heap` is an `abbrev`, so `h.swapAt`
resolves to `Array.swapAt` (`Heap.get?`'s own caveat, Runtime.lean). -/
def Heap.swapAt (h : Heap) (a : Addr) (o : Obj) : Heap :=
  h.setIfInBounds a o

/-- `Heap.get?` IS `getElem?` — the bridge onto `Array`'s mature
`setIfInBounds`/`push` simp set, which is what keeps the swap algebra
below to one `simp` apiece. -/
theorem Heap.get?_eq_getElem? (h : Heap) (a : Addr) : Heap.get? h a = h[a]? := by
  unfold Heap.get?; split <;> simp_all

@[simp] theorem Heap.size_swapAt (h : Heap) (a : Addr) (o : Obj) :
    (Heap.swapAt h a o).size = h.size := by
  simp [Heap.swapAt]

/-- The written slot reads back as what was written. -/
theorem Heap.get?_swapAt_self {h : Heap} {a : Addr} (hlt : a < h.size) (o : Obj) :
    Heap.get? (Heap.swapAt h a o) a = some o := by
  simp [Heap.get?_eq_getElem?, Heap.swapAt, hlt]

/-- **Every OTHER slot is untouched** — the workhorse of §Tier B: it is
what makes each heap-reading helper blind to the swap away from `a`. -/
@[simp] theorem Heap.get?_swapAt_ne {h : Heap} {a b : Addr} {o : Obj} (hne : b ≠ a) :
    Heap.get? (Heap.swapAt h a o) b = Heap.get? h b := by
  simp [Heap.get?_eq_getElem?, Heap.swapAt, Ne.symm hne]

/-- A live slot's address is in bounds — the side condition every swap
lemma needs, read off the slot hypothesis. -/
theorem Heap.lt_size_of_get? {h : Heap} {a : Addr} {o : Obj}
    (hobj : Heap.get? h a = some o) : a < h.size := by
  rw [Heap.get?] at hobj; split at hobj
  · assumption
  · simp at hobj

/-- A dead address cannot be written. -/
theorem Heap.update_eq_none {h : Heap} {a : Addr} {o : Obj} (hlt : ¬ a < h.size) :
    Heap.update h a o = Option.none := by
  rw [Heap.update, dif_neg hlt]

/-- **`update` IS `swapAt` where it is defined** — the bridge from
`PayloadBlind`'s `Heap.update … = some h` hypotheses to the functional
form the induction runs on. -/
theorem Heap.update_eq_swapAt {h h' : Heap} {a : Addr} {o : Obj}
    (hu : Heap.update h a o = some h') : h' = Heap.swapAt h a o := by
  rw [Heap.update] at hu
  split at hu
  · next hlt =>
      injection hu with hu
      subst hu
      refine Array.ext_getElem? fun i => ?_
      rw [Array.getElem?_set hlt]
      simp only [Heap.swapAt, Array.getElem?_setIfInBounds]
      by_cases hia : a = i
      · rw [if_pos hia, if_pos hia, if_pos hlt]
      · rw [if_neg hia, if_neg hia]
  · next => simp at hu

/-- A live slot's write agrees with the swap. -/
theorem Heap.update_swapAt_self {h : Heap} {a : Addr} {o : Obj} (hlt : a < h.size) :
    Heap.update h a o = some (Heap.swapAt h a o) := by
  obtain ⟨h', hh'⟩ : ∃ h', Heap.update h a o = some h' := by
    rw [Heap.update, dif_pos hlt]; exact ⟨_, rfl⟩
  rw [hh', Heap.update_eq_swapAt hh']

/-- **A swap commutes with ALLOCATION** — the heap only ever grows at the
end, so a perturbation inside it survives every `alloc`. -/
theorem Heap.swapAt_push {h : Heap} {a : Addr} {o : Obj} (hlt : a < h.size) (v : Obj) :
    (Heap.swapAt h a o).push v = Heap.swapAt (h.push v) a o := by
  refine Array.ext_getElem? fun i => ?_
  by_cases hia : a = i
  · subst hia
    simp [Heap.swapAt, hlt, Nat.lt_succ_of_lt hlt, Array.getElem_push_lt,
      Array.getElem_setIfInBounds_self]
  · simp [Array.getElem?_push, Heap.swapAt, hia]

/-- **The slot survives ALLOCATION** — the fact §Tier C's three allocation
leaves proved inline, named once because every `evalExpr` display arm needs
it too. (`Heap.get?_push_lt` in Examples/python/sunfish/genmoves_ray.lean is
the same fact in `hlt` form; it stays local, this one is stated at the slot
so the arms read off `hslot` directly.) -/
theorem Heap.get?_push_of_get? {h : Heap} {a : Addr} {o₀ : Obj} (g : Obj)
    (hslot : Heap.get? h a = some o₀) : Heap.get? (h.push g) a = some o₀ := by
  have hne : a ≠ h.size := Nat.ne_of_lt (Heap.lt_size_of_get? hslot)
  rw [Heap.get?_eq_getElem?, Array.getElem?_push, if_neg hne, ← Heap.get?_eq_getElem?]
  exact hslot

/-- **The slot's ANSWER survives allocation**, live or not — the same fact one
step more general than `Heap.get?_push_of_get?`, which needs the slot to be
occupied already. The one address a `push` moves is the fresh one, so `a ≠
h.size` is the whole side condition; a frame lemma that must also cover a
`none` answer (a probe of a slot the caller has not proved live) needs this
form. Consumer: `Bracket.SubtreeWrites`'s allocation arm in DictCalc.lean.

Proved from the `dif` rather than through `Array.getElem?_push`, and that is
not style: **`Array.getElem?_push` depends on `Classical.choice`** while
`Array.getElem_push_lt` depends on `propext` alone. Its sibling above pays
that price; a lemma DictCalc consumes may not, because DictCalc's axiom set is
choice-free by contract (docs/backlog.md §L13).

The size arithmetic is by name and not by `omega` for the reason AGENTS.md's
failure table gives for `PyInt`: `Addr` is a reducible abbrev of `Nat`, so a
comparison headed at it is skipped wholesale and `omega` reports "no usable
constraints" with the constraint in plain sight. -/
theorem Heap.get?_push_ne {h : Heap} {a : Addr} {o : Obj} (hne : a ≠ h.size) :
    Heap.get? (h.push o) a = Heap.get? h a := by
  by_cases hlt : a < h.size
  · have hlt' : a < (h.push o).size := by
      rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt
    rw [Heap.get?, dif_pos hlt', Heap.get?, dif_pos hlt, Array.getElem_push_lt]
  · have hlt' : ¬ a < (h.push o).size := by
      rw [Array.size_push]
      exact fun hc => (Nat.lt_succ_iff_lt_or_eq.mp hc).elim hlt hne
    rw [Heap.get?, dif_neg hlt', Heap.get?, dif_neg hlt]

/-- **Two swaps at DIFFERENT slots commute.** -/
theorem Heap.swapAt_comm {h : Heap} {a b : Addr} {o v : Obj} (hne : b ≠ a) :
    Heap.swapAt (Heap.swapAt h a o) b v = Heap.swapAt (Heap.swapAt h b v) a o := by
  refine Array.ext_getElem? fun i => ?_
  by_cases hbi : b = i
  · subst hbi
    simp [Heap.swapAt, Array.getElem?_setIfInBounds, Ne.symm hne]
  · by_cases hai : a = i
    · subst hai
      simp [Heap.swapAt, Array.getElem?_setIfInBounds, hne]
    · simp [Heap.swapAt, hai, hbi]

/-- **A swap commutes with a write ELSEWHERE** — the heap motion of every
call site that is not `a` itself passes through this. -/
theorem Heap.update_swapAt_ne {h : Heap} {a b : Addr} {o v : Obj} (hne : b ≠ a) :
    Heap.update (Heap.swapAt h a o) b v
      = (Heap.update h b v).map (fun h' => Heap.swapAt h' a o) := by
  by_cases hb : b < h.size
  · have hb' : b < (Heap.swapAt h a o).size := by rw [Heap.size_swapAt]; exact hb
    rw [Heap.update_swapAt_self hb', Heap.update_swapAt_self hb, Option.map_some,
      Heap.swapAt_comm hne]
  · have hb' : ¬ b < (Heap.swapAt h a o).size := by rw [Heap.size_swapAt]; exact hb
    rw [Heap.update_eq_none hb', Heap.update_eq_none hb, Option.map_none]

/-- A write ELSEWHERE leaves the slot alone — the `Heap.update` form of
`Heap.get?_swapAt_ne`, and what carries the slot fact across `stepIter`'s
four write-backs. -/
theorem Heap.get?_update_ne {h h' : Heap} {pa b : Addr} {v : Obj}
    (hu : Heap.update h b v = some h') (hne : pa ≠ b) :
    Heap.get? h' pa = Heap.get? h pa := by
  rw [Heap.update_eq_swapAt hu]
  exact Heap.get?_swapAt_ne hne

/-- Two swaps of one slot are the second swap. -/
@[simp] theorem Heap.swapAt_swapAt (h : Heap) (a : Addr) (o o' : Obj) :
    Heap.swapAt (Heap.swapAt h a o) a o' = Heap.swapAt h a o' := by
  refine Array.ext_getElem? fun i => ?_
  by_cases hia : a = i
  · simp [Heap.swapAt, hia]
  · simp [Heap.swapAt, hia]

/-! ### The swap lifted to worlds and frames -/

/-- The swap on a world: only the heap moves. -/
def World.swapAt (w : World) (a : Addr) (o : Obj) : World :=
  { w with heap := Heap.swapAt w.heap a o }

/-- The swap on a frame: only the world's heap moves; the locals ride. -/
def FrameState.swapAt (st : FrameState) (a : Addr) (o : Obj) : FrameState :=
  { st with world := st.world.swapAt a o }

@[simp] theorem World.swapAt_heap (w : World) (a : Addr) (o : Obj) :
    (w.swapAt a o).heap = Heap.swapAt w.heap a o := rfl
@[simp] theorem World.swapAt_globals (w : World) (a : Addr) (o : Obj) :
    (w.swapAt a o).globals = w.globals := rfl
@[simp] theorem World.swapAt_stdout (w : World) (a : Addr) (o : Obj) :
    (w.swapAt a o).stdout = w.stdout := rfl
@[simp] theorem World.swapAt_clock (w : World) (a : Addr) (o : Obj) :
    (w.swapAt a o).clock = w.clock := rfl
@[simp] theorem FrameState.swapAt_world (st : FrameState) (a : Addr) (o : Obj) :
    (st.swapAt a o).world = st.world.swapAt a o := rfl
@[simp] theorem FrameState.swapAt_locals (st : FrameState) (a : Addr) (o : Obj) :
    (st.swapAt a o).locals = st.locals := rfl

@[simp] theorem World.swapAt_mk (h : Heap) (g : REnv) (so : List String)
    (c : List Int) (a : Addr) (o : Obj) :
    World.swapAt ⟨h, g, so, c⟩ a o = ⟨Heap.swapAt h a o, g, so, c⟩ := rfl
@[simp] theorem FrameState.swapAt_mk (w : World) (l : REnv) (a : Addr) (o : Obj) :
    FrameState.swapAt ⟨w, l⟩ a o = ⟨w.swapAt a o, l⟩ := rfl

/-- The swap through a heap-replacing `with` — the form every interpreter
arm's post-write world is in. -/
@[simp] theorem World.swapAt_heap_set (w : World) (h : Heap) (a : Addr) (o : Obj) :
    World.swapAt { w with heap := h } a o = { w with heap := Heap.swapAt h a o } := rfl

@[simp] theorem FrameState.swapAt_world_set (st : FrameState) (w : World)
    (a : Addr) (o : Obj) :
    FrameState.swapAt { st with world := w } a o = { st with world := w.swapAt a o } := rfl

/-! ## Tier B/C prelude — the perturbation, and the relation on runs -/

/-- **The perturbation the interpreter must not see**: same `qname`, same
`.running` status, ANY other locals/cont. All three narrowings are
load-bearing (docs/backlog.md §L6): widen any one and the property is
FALSE, because an arbitrary object, a `.suspended` payload, and `qname`
are each observable. -/
def PayloadTwin (o₀ o : Obj) : Prop :=
  ∃ (q : String) (l₀ : REnv) (c₀ : GenCont) (l₁ : REnv) (c₁ : GenCont),
    o₀ = .generator q l₀ c₀ .running ∧ o = .generator q l₁ c₁ .running

/-- The relation on `World`-typed runs: a DECIDED base run pins the slot
at `a` and forces the swapped run to be its image. Refusals — `.timeout`,
`.unsupported` — constrain nothing; nothing in the block converts either
back to a decision. -/
abbrev PBW (a : Addr) (o₀ o : Obj) (x y : Run World α) : Prop :=
  (∀ w v, x = .ok w v → Heap.get? w.heap a = some o₀ ∧ y = .ok (w.swapAt a o) v) ∧
  (∀ w e, x = .exn w e → Heap.get? w.heap a = some o₀ ∧ y = .exn (w.swapAt a o) e)

/-- The `FrameState` twin. -/
abbrev PBF (a : Addr) (o₀ o : Obj) (x y : Run FrameState α) : Prop :=
  (∀ st v, x = .ok st v → Heap.get? st.world.heap a = some o₀ ∧ y = .ok (st.swapAt a o) v) ∧
  (∀ st e, x = .exn st e → Heap.get? st.world.heap a = some o₀ ∧ y = .exn (st.swapAt a o) e)

/-! ## Tier C — the combinators, proved once

One congruence per `Run` combinator, `ClockErasedF`'s geometry. Every arm
in §Tier D is a composition of these. -/

namespace PBW
variable {a : Addr} {o₀ o : Obj} {α β : Type}

theorem ok {w : World} (hslot : Heap.get? w.heap a = some o₀) (v : α) :
    PBW a o₀ o (.ok w v) (.ok (w.swapAt a o) v) := by
  refine ⟨fun w' v' h => ?_, fun w' e h => ?_⟩
  · injection h with hw hv; subst hw; subst hv; exact ⟨hslot, rfl⟩
  · exact absurd h (by simp)

theorem exn {w : World} (hslot : Heap.get? w.heap a = some o₀) (e : PyErr) :
    PBW a o₀ o (α := α) (.exn w e) (.exn (w.swapAt a o) e) := by
  refine ⟨fun w' v' h => ?_, fun w' e' h => ?_⟩
  · exact absurd h (by simp)
  · injection h with hw he; subst hw; subst he; exact ⟨hslot, rfl⟩

/-- A refusal on the base side constrains NOTHING. -/
theorem timeout {y : Run World α} : PBW a o₀ o .timeout y := by
  exact ⟨fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩

theorem unsupported {msg : String} {y : Run World α} :
    PBW a o₀ o (.unsupported msg) y :=
  ⟨fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩

/-- A base run that is not decided constrains nothing — the catch-all
closing every arm whose base side refuses. -/
theorem of_undecided {x : Run World α} {y : Run World α}
    (hok : ∀ w v, x ≠ .ok w v) (hexn : ∀ w e, x ≠ .exn w e) : PBW a o₀ o x y :=
  ⟨fun w v h => absurd h (hok w v), fun w e h => absurd h (hexn w e)⟩

theorem liftRes {w : World} (hslot : Heap.get? w.heap a = some o₀) (r : Res α) :
    PBW a o₀ o (Run.liftRes w r) (Run.liftRes (w.swapAt a o) r) := by
  cases r with
  | ok v => exact ok hslot v
  | exn e => exact exn hslot e
  | timeout => exact timeout
  | unsupported msg => exact unsupported

/-- THE WORKHORSE: sequencing. The prefix hands the continuation both its
intermediate state AND the slot fact at that state, which is exactly the
hypothesis the inductive call needs. -/
theorem bind {x y : Run World α} {f g : World → α → Run World β}
    (hx : PBW a o₀ o x y)
    (hf : ∀ w v, x = .ok w v → Heap.get? w.heap a = some o₀ →
      PBW a o₀ o (f w v) (g (w.swapAt a o) v)) :
    PBW a o₀ o (x.bind f) (y.bind g) := by
  cases x with
  | ok w v =>
      obtain ⟨hslot, hy⟩ := hx.1 w v rfl
      rw [hy, Run.ok_bind, Run.ok_bind]
      exact hf w v rfl hslot
  | exn w e =>
      obtain ⟨hslot, hy⟩ := hx.2 w e rfl
      rw [hy, Run.exn_bind, Run.exn_bind]
      exact exn hslot e
  | timeout => rw [Run.timeout_bind]; exact timeout
  | unsupported msg => rw [Run.unsupported_bind]; exact unsupported

/-- Sequencing with an EXN continuation (`stepIter`'s combinator: a raise
out of a resume must close the object). -/
theorem bindE {x y : Run World α} {f g : World → α → Run World β}
    {f' g' : World → PyErr → Run World β}
    (hx : PBW a o₀ o x y)
    (hf : ∀ w v, x = .ok w v → Heap.get? w.heap a = some o₀ →
      PBW a o₀ o (f w v) (g (w.swapAt a o) v))
    (hf' : ∀ w e, x = .exn w e → Heap.get? w.heap a = some o₀ →
      PBW a o₀ o (f' w e) (g' (w.swapAt a o) e)) :
    PBW a o₀ o (x.bindE f f') (y.bindE g g') := by
  cases x with
  | ok w v =>
      obtain ⟨hslot, hy⟩ := hx.1 w v rfl
      rw [hy, Run.ok_bindE, Run.ok_bindE]
      exact hf w v rfl hslot
  | exn w e =>
      obtain ⟨hslot, hy⟩ := hx.2 w e rfl
      rw [hy, Run.exn_bindE, Run.exn_bindE]
      exact hf' w e rfl hslot
  | timeout => rw [Run.timeout_bindE]; exact timeout
  | unsupported msg => rw [Run.unsupported_bindE]; exact unsupported

/-- A branch whose CONDITION is already known equal on both sides. Every
heap-dependent condition is brought to this form by a §Tier B equation. -/
theorem ite {c : Prop} [Decidable c] {x y z u : Run World α}
    (ht : c → PBW a o₀ o x y) (he : ¬c → PBW a o₀ o z u) :
    PBW a o₀ o (if c then x else z) (if c then y else u) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact ht hc
  · rw [if_neg hc, if_neg hc]; exact he hc

/-- Enter a frame: the world is threaded, the caller's locals ride. -/
theorem withLocals {l : REnv} {x y : Run World α} (h : PBW a o₀ o x y) :
    PBF a o₀ o (x.withLocals l) (y.withLocals l) := by
  cases x with
  | ok w v =>
      obtain ⟨hslot, hy⟩ := h.1 w v rfl
      rw [hy]
      refine ⟨fun st v' hs => ?_, fun st e hs => ?_⟩
      · injection hs with hst hv; subst hst; subst hv; exact ⟨hslot, rfl⟩
      · exact absurd hs (by simp [Run.withLocals])
  | exn w e =>
      obtain ⟨hslot, hy⟩ := h.2 w e rfl
      rw [hy]
      refine ⟨fun st v' hs => ?_, fun st e' hs => ?_⟩
      · exact absurd hs (by simp [Run.withLocals])
      · injection hs with hst he; subst hst; subst he; exact ⟨hslot, rfl⟩
  | timeout => exact ⟨fun _ _ h => absurd h (by simp [Run.withLocals]),
      fun _ _ h => absurd h (by simp [Run.withLocals])⟩
  | unsupported msg =>
                       exact ⟨fun _ _ h => absurd h (by simp [Run.withLocals]),
                         fun _ _ h => absurd h (by simp [Run.withLocals])⟩

/-- Allocation at the WORLD level: the heap grows at the END, so the fresh
address is the same on both sides, the slot survives the append, and the
swap commutes with it. -/
theorem push {w : World} {g : Obj}
    (hslot : Heap.get? w.heap a = some o₀) :
    PBW a o₀ o (.ok { w with heap := w.heap.push g } (RVal.ref w.heap.size))
      (.ok { w.swapAt a o with heap := (w.swapAt a o).heap.push g }
        (RVal.ref (w.swapAt a o).heap.size)) := by
  have hlt := Heap.lt_size_of_get? hslot
  have hne : a ≠ w.heap.size := Nat.ne_of_lt hlt
  have hslot' : Heap.get? (w.heap.push g) a = some o₀ := by
    rw [Heap.get?_eq_getElem?, Array.getElem?_push, if_neg hne, ← Heap.get?_eq_getElem?]
    exact hslot
  have hst : ({ w.swapAt a o with heap := (w.swapAt a o).heap.push g } : World)
      = ({ w with heap := w.heap.push g } : World).swapAt a o := by
    simp only [World.swapAt, World.swapAt_heap]
    rw [Heap.swapAt_push hlt]
  have hsz : (w.swapAt a o).heap.size = w.heap.size := by
    rw [World.swapAt_heap, Heap.size_swapAt]
  rw [hst, hsz]
  exact ok hslot' _

end PBW

namespace PBF
variable {a : Addr} {o₀ o : Obj} {α β : Type}

theorem ok {st : FrameState} (hslot : Heap.get? st.world.heap a = some o₀) (v : α) :
    PBF a o₀ o (.ok st v) (.ok (st.swapAt a o) v) := by
  refine ⟨fun st' v' h => ?_, fun st' e h => ?_⟩
  · injection h with hst hv; subst hst; subst hv; exact ⟨hslot, rfl⟩
  · exact absurd h (by simp)

theorem exn {st : FrameState} (hslot : Heap.get? st.world.heap a = some o₀) (e : PyErr) :
    PBF a o₀ o (α := α) (.exn st e) (.exn (st.swapAt a o) e) := by
  refine ⟨fun st' v' h => ?_, fun st' e' h => ?_⟩
  · exact absurd h (by simp)
  · injection h with hst he; subst hst; subst he; exact ⟨hslot, rfl⟩

theorem timeout {y : Run FrameState α} : PBF a o₀ o .timeout y :=
  ⟨fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩

theorem unsupported {msg : String} {y : Run FrameState α} :
    PBF a o₀ o (.unsupported msg) y :=
  ⟨fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩

theorem of_undecided {x y : Run FrameState α}
    (hok : ∀ st v, x ≠ .ok st v) (hexn : ∀ st e, x ≠ .exn st e) : PBF a o₀ o x y :=
  ⟨fun st v h => absurd h (hok st v), fun st e h => absurd h (hexn st e)⟩

theorem liftRes {st : FrameState} (hslot : Heap.get? st.world.heap a = some o₀)
    (r : Res α) :
    PBF a o₀ o (Run.liftRes st r) (Run.liftRes (st.swapAt a o) r) := by
  cases r with
  | ok v => exact ok hslot v
  | exn e => exact exn hslot e
  | timeout => exact timeout
  | unsupported msg => exact unsupported

theorem bind {x y : Run FrameState α} {f g : FrameState → α → Run FrameState β}
    (hx : PBF a o₀ o x y)
    (hf : ∀ st v, x = .ok st v → Heap.get? st.world.heap a = some o₀ →
      PBF a o₀ o (f st v) (g (st.swapAt a o) v)) :
    PBF a o₀ o (x.bind f) (y.bind g) := by
  cases x with
  | ok st v =>
      obtain ⟨hslot, hy⟩ := hx.1 st v rfl
      rw [hy, Run.ok_bind, Run.ok_bind]
      exact hf st v rfl hslot
  | exn st e =>
      obtain ⟨hslot, hy⟩ := hx.2 st e rfl
      rw [hy, Run.exn_bind, Run.exn_bind]
      exact exn hslot e
  | timeout => rw [Run.timeout_bind]; exact timeout
  | unsupported msg => rw [Run.unsupported_bind]; exact unsupported

theorem bindE {x y : Run FrameState α} {f g : FrameState → α → Run FrameState β}
    {f' g' : FrameState → PyErr → Run FrameState β}
    (hx : PBF a o₀ o x y)
    (hf : ∀ st v, x = .ok st v → Heap.get? st.world.heap a = some o₀ →
      PBF a o₀ o (f st v) (g (st.swapAt a o) v))
    (hf' : ∀ st e, x = .exn st e → Heap.get? st.world.heap a = some o₀ →
      PBF a o₀ o (f' st e) (g' (st.swapAt a o) e)) :
    PBF a o₀ o (x.bindE f f') (y.bindE g g') := by
  cases x with
  | ok st v =>
      obtain ⟨hslot, hy⟩ := hx.1 st v rfl
      rw [hy, Run.ok_bindE, Run.ok_bindE]
      exact hf st v rfl hslot
  | exn st e =>
      obtain ⟨hslot, hy⟩ := hx.2 st e rfl
      rw [hy, Run.exn_bindE, Run.exn_bindE]
      exact hf' st e rfl hslot
  | timeout => rw [Run.timeout_bindE]; exact timeout
  | unsupported msg => rw [Run.unsupported_bindE]; exact unsupported

theorem ite {c : Prop} [Decidable c] {x y z u : Run FrameState α}
    (ht : c → PBF a o₀ o x y) (he : ¬c → PBF a o₀ o z u) :
    PBF a o₀ o (if c then x else z) (if c then y else u) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact ht hc
  · rw [if_neg hc, if_neg hc]; exact he hc

/-- Return from a call: the frame's locals die, the world survives. -/
theorem toWorld {x y : Run FrameState α} (h : PBF a o₀ o x y) :
    PBW a o₀ o x.toWorld y.toWorld := by
  cases x with
  | ok st v =>
      obtain ⟨hslot, hy⟩ := h.1 st v rfl
      rw [hy]
      refine ⟨fun w v' hs => ?_, fun w e hs => ?_⟩
      · injection hs with hw hv; subst hw; subst hv; exact ⟨hslot, rfl⟩
      · exact absurd hs (by simp [Run.toWorld])
  | exn st e =>
      obtain ⟨hslot, hy⟩ := h.2 st e rfl
      rw [hy]
      refine ⟨fun w v' hs => ?_, fun w e' hs => ?_⟩
      · exact absurd hs (by simp [Run.toWorld])
      · injection hs with hw he; subst hw; subst he; exact ⟨hslot, rfl⟩
  | timeout => exact ⟨fun _ _ h => absurd h (by simp [Run.toWorld]),
      fun _ _ h => absurd h (by simp [Run.toWorld])⟩
  | unsupported msg =>
                       exact ⟨fun _ _ h => absurd h (by simp [Run.toWorld]),
                         fun _ _ h => absurd h (by simp [Run.toWorld])⟩

/-! ### The allocation leaves

An `alloc` appends, so it commutes with a swap INSIDE the heap
(`Heap.swapAt_push`) and answers the same address (`Heap.size_swapAt`). -/

theorem allocList {st : FrameState} (hslot : Heap.get? st.world.heap a = some o₀)
    (xs : Array RVal) :
    PBF a o₀ o (allocListRun st xs) (allocListRun (st.swapAt a o) xs) := by
  have hlt := Heap.lt_size_of_get? hslot
  unfold allocListRun
  refine ⟨fun st' v' h => ?_, fun st' e h => ?_⟩
  · injection h with hst hv
    subst hst; subst hv
    refine ⟨?_, ?_⟩
    · have hne : a ≠ st.world.heap.size := Nat.ne_of_lt hlt
      rw [Heap.get?_eq_getElem?, Array.getElem?_push, if_neg hne,
        ← Heap.get?_eq_getElem?]
      exact hslot
    · simp only [FrameState.swapAt, World.swapAt]
      rw [Heap.swapAt_push hlt, Heap.size_swapAt]
  · exact absurd h (by simp)

theorem allocDict {st : FrameState} (hslot : Heap.get? st.world.heap a = some o₀)
    (es : Array (RVal × RVal)) :
    PBF a o₀ o (allocDictRun st es) (allocDictRun (st.swapAt a o) es) := by
  have hlt := Heap.lt_size_of_get? hslot
  unfold allocDictRun
  refine ⟨fun st' v' h => ?_, fun st' e h => ?_⟩
  · injection h with hst hv
    subst hst; subst hv
    refine ⟨?_, ?_⟩
    · have hne : a ≠ st.world.heap.size := Nat.ne_of_lt hlt
      rw [Heap.get?_eq_getElem?, Array.getElem?_push, if_neg hne,
        ← Heap.get?_eq_getElem?]
      exact hslot
    · simp only [FrameState.swapAt, World.swapAt]
      rw [Heap.swapAt_push hlt, Heap.size_swapAt]
  · exact absurd h (by simp)

end PBF


/-! ## Tier B — the universal read primitive

Every heap-reading helper resolves its reads through this one fact, and
that is why each helper's blindness lemma is an ARM-BY-ARM `rfl` rather
than a simulation: away from `pa` the swapped heap reads the SAME object,
and AT `pa` both sides read a `.running` generator of the same `qname` —
which every arm in the semantics but `stepIter`'s answers without looking
at the payload (the census, docs/backlog.md §L6). -/

/-- **The read, resolved**: same object off `pa`, twin generators at it. -/
theorem Heap.get?_swapAt_twin {h : Heap} {pa b : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) :
    Heap.get? (Heap.swapAt h pa o) b = Heap.get? h b ∨
      (∃ (q : String) (l₀ : REnv) (c₀ : GenCont) (l₁ : REnv) (c₁ : GenCont),
        Heap.get? h b = some (.generator q l₀ c₀ .running) ∧
        Heap.get? (Heap.swapAt h pa o) b = some (.generator q l₁ c₁ .running)) := by
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    exact Or.inr ⟨q, l₀, c₀, l₁, c₁, hslot,
      Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot) _⟩
  · exact Or.inl (Heap.get?_swapAt_ne hba)

/-- **The read, resolved the OTHER way**: an answer that is not the slot's
own object is at a different address, so the swap does not move it. The
functional-induction case hypothesis of a recursive reader
(`h.get? a = some (.list xs)`) is exactly this lemma's input, which is
what keeps §Tier B's two mutual recursions to their `.ref` arms. -/
theorem Heap.get?_swapAt_of_ne_slot {h : Heap} {pa b : Addr} {o₀ o obj : Obj}
    (hslot : Heap.get? h pa = some o₀) (hne : obj ≠ o₀)
    (hb : Heap.get? h b = some obj) :
    Heap.get? (Heap.swapAt h pa o) b = some obj := by
  refine (Heap.get?_swapAt_ne ?_).trans hb
  intro hba
  subst hba
  rw [hslot] at hb
  exact hne (Option.some.inj hb).symm

/-- `RVal.typeNameH` is blind — the refusal messages name the CONSTRUCTOR,
and a twin pair shares it. The template every §Tier B arm follows. -/
theorem RVal.typeNameH_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (v : RVal) :
    RVal.typeNameH (Heap.swapAt h pa o) v = RVal.typeNameH h v := by
  cases v with
  | ref b =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨q, l₀, c₀, l₁, c₁, h1, h2⟩
      · rw [RVal.typeNameH, RVal.typeNameH, heq]
      · rw [RVal.typeNameH, RVal.typeNameH, h1, h2]
  | _ => rfl

/-! ### The key-hashing helpers

`keyRefusal`'s two message helpers recurse through tuples; both have a
generated functional-induction principle whose heap is a fixed PARAMETER,
which is exactly the motive shape a blindness equation needs. -/

/-- A key's instance/identity census is blind: it reads the CONSTRUCTOR. -/
theorem keyHasInstanceRef_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (v : RVal) :
    keyHasInstanceRef (Heap.swapAt h pa o) v = keyHasInstanceRef h v := by
  induction v using keyHasInstanceRef.induct (h := h)
    (motive_2 := fun vs => keyHasInstanceRefList (Heap.swapAt h pa o) vs
      = keyHasInstanceRefList h vs) with
  -- case3 is the H7 CELL arm (a cell is identity, like an instance: the
  -- key census refuses it), which is why every later case shifted by one
  | case1 b cls attrs hb | case2 b q l c st hb | case3 b cv hb
  | case4 b n p a1 a2 a3 a4 bd cp hb
  | case5 b xs hb | case6 b _ _ _ _ =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · rw [keyHasInstanceRef, keyHasInstanceRef, heq]
      · rw [keyHasInstanceRef, keyHasInstanceRef, h1, h2]
  | case7 xs ih | case8 _ _ xs ih => rw [keyHasInstanceRef, keyHasInstanceRef]; exact ih
  | case9 _ _ _ => rfl
  | case10 t _ _ _ _ => rw [keyHasInstanceRef.eq_def, keyHasInstanceRef.eq_def]; split <;> simp_all
  | case11 => rfl
  | case12 x rest ih1 ih2 => rw [keyHasInstanceRefList, keyHasInstanceRefList, ih1, ih2]

/-- The name CPython would print in `unhashable type: '…'` is blind. -/
theorem unhashableName?_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (v : RVal) :
    unhashableName? (Heap.swapAt h pa o) v = unhashableName? h v := by
  induction v using unhashableName?.induct (h := h)
    (motive_2 := fun vs => unhashableNameList? (Heap.swapAt h pa o) vs
      = unhashableNameList? h vs) <;>
  simp_all [unhashableName?, unhashableNameList?, RVal.typeNameH_swapAt hslot htwin]

/-! ### The H7 CELL workers are blind

`allocCells` never READS the heap — it appends, and the swap commutes
with an append at a live address. `cellsFor` reads exactly the cell
slots, and a `PayloadTwin` is a running GENERATOR: at the perturbed
address both sides see a generator, so both refuse identically, and
everywhere else the read is literally the same. -/

theorem allocCells_swapAt {pa : Addr} {o : Obj} :
    ∀ (st : FrameState) (caps : List String), pa < st.world.heap.size →
      allocCells (st.swapAt pa o) caps = (allocCells st caps).swapAt pa o := by
  intro st caps
  induction caps generalizing st with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hlt
    rw [allocCells, allocCells]
    by_cases hc : isCellKey c = true
    · simp only [hc, if_true, ite_true, FrameState.swapAt_locals]
      cases Env.lookup st.locals c with
      | some _ => exact ih st hlt
      | none =>
        simp only [FrameState.swapAt_world, World.swapAt_heap, Heap.size_swapAt,
          Heap.swapAt_push hlt, World.swapAt_globals, World.swapAt_stdout,
          World.swapAt_clock]
        refine ih { st with
            world := { st.world with
              heap := st.world.heap.push (.cell (Env.lookup st.locals (cellName c))) },
            locals := Env.set st.locals c (.ref st.world.heap.size) } ?_
        simpa using Nat.lt_trans hlt (Nat.lt_succ_self _)
    · simp only [hc, Bool.false_eq_true, if_false, ite_false]
      exact ih st hlt

/-- Allocating cells only APPENDS, so every live slot reads back. -/
theorem allocCells_get? : ∀ (st : FrameState) (caps : List String) {pa : Addr} {o₀ : Obj},
    Heap.get? st.world.heap pa = some o₀ →
    Heap.get? (allocCells st caps).world.heap pa = some o₀ := by
  intro st caps
  induction caps generalizing st with
  | nil => intro _ _ h; exact h
  | cons c cs ih =>
    intro pa o₀ h
    rw [allocCells]
    by_cases hc : isCellKey c = true
    · simp only [hc, if_true]
      cases Env.lookup st.locals c with
      | some _ => exact ih st h
      | none => exact ih _ (Heap.get?_push_of_get? _ h)
    · simp only [hc, Bool.false_eq_true, if_false]
      exact ih st h

theorem cellsFor_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (env : Env) (cap : REnv) :
    cellsFor (Heap.swapAt h pa o) env cap = cellsFor h env cap := by
  induction cap with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    -- `rw [cellsFor]` would ask for the pattern side conditions of
    -- the inner match (§L11 finding 1's neighbourhood); `simp only`
    -- unfolds the cons equation without them
    simp only [cellsFor]
    by_cases hk : isCellKey k = true
    · simp only [hk, if_true]
      cases v
      all_goals try rfl
      rename_i a
      dsimp only
      rcases Heap.get?_swapAt_twin (b := a) hslot htwin with heq | ⟨q, l₀, c₀, l₁, c₁, h1, h2⟩
      · rw [heq, ih]
      · rw [h1, h2]
    · simp only [hk, Bool.false_eq_true, if_false, ite_false, ih]

/-- The unhashable-key refusal is blind — both its branch and its
message. -/
theorem keyRefusal_swapAt {α : Type} {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (k : RVal) :
    keyRefusal (α := α) (Heap.swapAt h pa o) k = keyRefusal h k := by
  rw [keyRefusal, keyRefusal, keyHasInstanceRef_swapAt hslot htwin,
    unhashableName?_swapAt hslot htwin, RVal.typeNameH_swapAt hslot htwin]

/-! ### The single-address readers

Each is `match Heap.get? h b with …` over the six `Obj` constructors, and
`Heap.get?_swapAt_twin` resolves that scrutinee in one step: the `.generator`
arm is reached on BOTH sides at `pa` and answers the same, every other arm
is reached with the identical object. -/

/-- `len(o)` is blind. -/
theorem heapLen_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (b : Addr) :
    heapLen (Heap.swapAt h pa o) b = heapLen h b := by
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · rw [heapLen, heapLen, heq]
  · rw [heapLen, heapLen, h1, h2]

/-- Truthiness is blind (a generator object is truthy either way). -/
theorem truthyH_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (v : RVal) :
    truthyH (Heap.swapAt h pa o) v = truthyH h v := by
  cases v with
  | ref b =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · rw [truthyH, truthyH, heq]
      · rw [truthyH, truthyH, h1, h2]
  | _ => rfl

/-- `d.get(k)` is blind. -/
theorem heapGet_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (k dflt : RVal) :
    heapGet (Heap.swapAt h pa o) b k dflt = heapGet h b k dflt := by
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · simp only [heapGet, heq, keyRefusal_swapAt hslot htwin]
  · rw [heapGet, heapGet, h1, h2]

/-- `o[k]` is blind. -/
theorem heapIndex_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (k : RVal) :
    heapIndex (Heap.swapAt h pa o) b k = heapIndex h b k := by
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · simp only [heapIndex, heq, keyRefusal_swapAt hslot htwin,
      RVal.typeNameH_swapAt hslot htwin]
  · rw [heapIndex, heapIndex, h1, h2]

/-! ### The forwarders

Nothing left to see: each hands its heap to a helper already proved
blind. -/

/-- `len(v)` at the value level is blind. -/
theorem lenValH_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (v : RVal) :
    lenValH (Heap.swapAt h pa o) v = lenValH h v := by
  cases v with
  | ref b => rw [lenValH, lenValH, heapLen_swapAt hslot htwin]
  | _ => rfl

/-- Unary operators are blind (`not` is the only heap consumer). -/
theorem evalUnaryOpH_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (op : UnaryOp) (v : RVal) :
    evalUnaryOpH (Heap.swapAt h pa o) op v = evalUnaryOpH h op v := by
  cases op with
  | not => simp only [evalUnaryOpH, truthyH_swapAt hslot htwin]
  | usub => rfl
  -- §L39 rung 1: `+` and `~` delegate to the PURE `evalUnaryOp` exactly as
  -- `-` does, so they never look at the heap and the swap is `rfl` too.
  | uadd => rfl
  | invert => rfl

/-- Subscription at the value level is blind. -/
theorem indexValH_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (container index : RVal) :
    indexValH (Heap.swapAt h pa o) container index
      = indexValH h container index := by
  unfold indexValH
  split <;>
    simp_all [heapIndex_swapAt hslot htwin, RVal.typeNameH_swapAt hslot htwin]

/-! ### The direct callers

Every helper the fifteen proved arms reach. From here to §Tier D the heap
rides as a fixed parameter, so the section's `variable`s carry the slot and
the twin instead of every statement repeating them. -/

section TierB
variable {h : Heap} {pa : Addr} {o₀ o : Obj}

/-- `range(…)` construction is blind (its `TypeError`s name the offending
argument's type). -/
theorem rangeMake_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (vs : List RVal) :
    rangeMake (Heap.swapAt h pa o) vs = rangeMake h vs := by
  unfold rangeMake
  simp only [RVal.typeNameH_swapAt hslot htwin]

/-- `max`/`min` over the heap are blind. -/
theorem extremumValH_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (isMax : Bool) (vs : List RVal) :
    extremumValH (Heap.swapAt h pa o) isMax vs = extremumValH h isMax vs := by
  match vs with
  | [] => rfl
  | [v] =>
      cases v with
      | ref b =>
          rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
          · simp only [extremumValH, heq]
          · simp only [extremumValH, h1, h2]
      | _ => rfl
  | _ :: _ :: _ => rfl

/-- `enumerate`'s initial frame is blind. -/
theorem enumFrame_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (i : Int) (v : RVal) :
    enumFrame (Heap.swapAt h pa o) i v = enumFrame h i v := by
  cases v with
  | ref b =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · rw [enumFrame, enumFrame, heq]
      · rw [enumFrame, enumFrame, h1, h2]
  | _ => rfl

/-- Unpacking arity/type discipline is blind. -/
theorem unpackSeq_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (n : Nat) (v : RVal) :
    unpackSeq (Heap.swapAt h pa o) n v = unpackSeq h n v := by
  cases v with
  | ref b =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · rw [unpackSeq, unpackSeq, heq]
      · rw [unpackSeq, unpackSeq, h1, h2]
  | _ => rfl

/-- The heap-aware assignment is blind: it diverts only on a `.ref`
value at a tuple/list target, and reads the referent's CONSTRUCTOR. -/
theorem assignToH_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (env : Env) (target : Expr) (v : RVal) :
    assignToH (Heap.swapAt h pa o) env target v = assignToH h env target v := by
  cases v with
  | ref b =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · unfold assignToH; split <;> simp [heq]
      · unfold assignToH; split <;> simp [h1, h2]
  | _ => unfold assignToH; split <;> rfl

/-- The attribute-READ plan is blind (a generator receiver refuses in read
position, on both sides, with the same message). -/
theorem attrReadPlan_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (m : Module) (b : Addr) (attr : String) :
    attrReadPlan m (Heap.swapAt h pa o) b attr = attrReadPlan m h b attr := by
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · rw [attrReadPlan, attrReadPlan, heq]
  · rw [attrReadPlan, attrReadPlan, h1, h2]

/-- The attribute-CALL plan is blind — `execAttrCall`'s whole dispatch
decision, decided before any argument runs. -/
theorem attrCallPlan_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (m : Module) (b : Addr) (attr : String) :
    attrCallPlan m (Heap.swapAt h pa o) b attr = attrCallPlan m h b attr := by
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · rw [attrCallPlan, attrCallPlan, heq]
  · rw [attrCallPlan, attrCallPlan, h1, h2]

/-! ### The two mutual recursions, and what rides on them

`reprVal` and `heapEq` are the tier's only heap-recursive readers. Lean
generates a functional-induction principle for each whose heap is a fixed
PARAMETER — exactly the motive shape a blindness equation needs — and
`fun_induction` does NOT work on them (they are mutual): the spelling is
`induction … using f.induct (motive_2 := …)`, and supplying the sibling
motives explicitly is mandatory since nothing can infer them -/

/-- **`repr` is blind** — the first of §Tier B's two mutual recursions.
`reprVal.induct`'s heap is a fixed PARAMETER and its `.ref` arms carry the
base read as a hypothesis, so `Heap.get?_swapAt_of_ne_slot` discharges the
four container arms and the twin the fifth (a generator renders as
`none` either way). -/
theorem reprVal_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (active : List Addr) (v : RVal) :
    reprVal (Heap.swapAt h pa o) fuel active v = reprVal h fuel active v := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
  induction fuel, active, v using reprVal.induct (h := h)
    (motive2 := fun f act es =>
      reprEntries (Heap.swapAt h pa (.generator q l₁ c₁ .running)) f act es
        = reprEntries h f act es)
    (motive3 := fun f act vs =>
      reprVals (Heap.swapAt h pa (.generator q l₁ c₁ .running)) f act vs
        = reprVals h f act vs) with
  | case14 _ a _ _ hb _ =>
      simp_all [reprVal, Heap.get?_swapAt_of_ne_slot hslot (by simp) hb]
  | case15 _ a _ _ hb _ ih =>
      simp_all [reprVal, Heap.get?_swapAt_of_ne_slot hslot (by simp) hb]
  | case16 _ a _ _ _ hb _ =>
      simp_all [reprVal, Heap.get?_swapAt_of_ne_slot hslot (by simp) hb]
  | case17 _ a _ _ _ hb _ ih =>
      simp_all [reprVal, Heap.get?_swapAt_of_ne_slot hslot (by simp) hb]
  | case18 _ a _ hnl hnd =>
      rcases Heap.get?_swapAt_twin (b := a) hslot ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ with
        heq | ⟨_, _, _, _, _, _, h2⟩
      · simp only [reprVal, heq]
      · simp only [reprVal, h2]
  | _ => simp_all [reprVal, reprVals, reprEntries]

/-- **`==` through the heap is blind** — the second mutual recursion, and
the one whose ref/ref arm reads TWO addresses. A generator on either side
falls through to the cross-type `False` (or the dangling refusal) on both
heaps, which is why the twin closes the two negative arms. -/
theorem heapEq_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (active : List (Addr × Addr)) (x y : RVal) :
    heapEq (Heap.swapAt h pa o) fuel active x y = heapEq h fuel active x y := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
  induction fuel, active, x, y using heapEq.induct (h := h)
    (motive_2 := fun f act as bs =>
      heapEqList (Heap.swapAt h pa (.generator q l₁ c₁ .running)) f act as bs
        = heapEqList h f act as bs)
    (motive_3 := fun f act ls rs =>
      heapEqEntries (Heap.swapAt h pa (.generator q l₁ c₁ .running)) f act ls rs
        = heapEqEntries h f act ls rs) with
  | case4 _ _ x y _ _ _ _ _ _ hy hx _ ih =>
      simp_all [heapEq, Heap.get?_swapAt_of_ne_slot hslot (by simp) hx,
        Heap.get?_swapAt_of_ne_slot hslot (by simp) hy]
  | case5 _ _ x y _ _ _ _ _ _ hy hx _ =>
      simp_all [heapEq, Heap.get?_swapAt_of_ne_slot hslot (by simp) hx,
        Heap.get?_swapAt_of_ne_slot hslot (by simp) hy]
  | case6 _ _ x y _ _ _ _ hy hx _ ih =>
      simp_all [heapEq, Heap.get?_swapAt_of_ne_slot hslot (by simp) hx,
        Heap.get?_swapAt_of_ne_slot hslot (by simp) hy]
  | case7 _ _ x y _ _ _ _ hy hx _ =>
      simp_all [heapEq, Heap.get?_swapAt_of_ne_slot hslot (by simp) hx,
        Heap.get?_swapAt_of_ne_slot hslot (by simp) hy]
  | case8 _ _ x y _ _ _ _ _ _ hy hx =>
      rcases Heap.get?_swapAt_twin (b := x) hslot ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ with
        heqx | ⟨_, _, _, _, _, hx1, hx2⟩ <;>
      rcases Heap.get?_swapAt_twin (b := y) hslot ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ with
        heqy | ⟨_, _, _, _, _, hy1, hy2⟩ <;>
      simp_all [heapEq]
  | case9 _ _ x y _ _ hno =>
      rcases Heap.get?_swapAt_twin (b := x) hslot ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ with
        heqx | ⟨_, _, _, _, _, hx1, hx2⟩ <;>
      rcases Heap.get?_swapAt_twin (b := y) hslot ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ with
        heqy | ⟨_, _, _, _, _, hy1, hy2⟩ <;>
      simp_all [heapEq]
  | _ => simp_all [heapEq, heapEqList, heapEqEntries]

/-- `print`'s rendering of one value is blind. -/
theorem printOne_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (v : RVal) : printOne (Heap.swapAt h pa o) v = printOne h v := by
  cases v <;> simp only [printOne, reprVal_swapAt hslot htwin]

/-- `str(…)` over the heap is blind. -/
theorem strOfValH_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (v : RVal) : strOfValH (Heap.swapAt h pa o) v = strOfValH h v := by
  cases v <;> simp only [strOfValH, printOne_swapAt hslot htwin]

/-- `print`'s space-joined argument rendering is blind. -/
theorem strOfArgs_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (vs : List RVal) : strOfArgs (Heap.swapAt h pa o) vs = strOfArgs h vs := by
  induction vs using strOfArgs.induct <;>
    simp_all [strOfArgs, printOne_swapAt hslot htwin]

/-- The `x in lst` scan is blind (each step is the fueled `heapEq`). -/
theorem heapContainsScan_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (x : RVal) (vs : List RVal) :
    heapContainsScan (Heap.swapAt h pa o) fuel x vs = heapContainsScan h fuel x vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp only [heapContainsScan, heapEq_swapAt hslot htwin, ih]

/-- `k in o` on a heap object is blind. -/
theorem heapContains_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (b : Addr) (k : RVal) :
    heapContains (Heap.swapAt h pa o) fuel b k = heapContains h fuel b k := by
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · simp only [heapContains, heq, keyRefusal_swapAt hslot htwin,
      heapContainsScan_swapAt hslot htwin]
  · rw [heapContains, heapContains, h1, h2]

/-- `x in c` for every in-tier container is blind. -/
theorem valContains_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (x y : RVal) :
    valContains (Heap.swapAt h pa o) fuel x y = valContains h fuel x y := by
  cases y <;>
    simp only [valContains, heapContains_swapAt hslot htwin,
      heapContainsScan_swapAt hslot htwin, RVal.typeNameH_swapAt hslot htwin]

/-- **The comparison step is blind** — what `evalCompareChain`'s arm
consumes. `is`/`is not` compare ADDRESSES, which the swap does not move. -/
theorem evalCompareOpH_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (op : CmpOp) (x y : RVal) :
    evalCompareOpH (Heap.swapAt h pa o) fuel op x y = evalCompareOpH h fuel op x y := by
  cases op <;>
    simp only [evalCompareOpH, heapEq_swapAt hslot htwin, valContains_swapAt hslot htwin]

/-- `any`/`all` over a snapshot are blind. -/
theorem anyAllScan_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (isAll : Bool) (vs : List RVal) :
    anyAllScan (Heap.swapAt h pa o) isAll vs = anyAllScan h isAll vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp only [anyAllScan, truthyH_swapAt hslot htwin, ih]

/-- Set construction's dedup is blind. -/
theorem setDedup_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (fuel : Nat) (acc vs : List RVal) :
    setDedup (Heap.swapAt h pa o) fuel acc vs = setDedup h fuel acc vs := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v rest ih =>
      simp only [setDedup, keyRefusal_swapAt hslot htwin,
        heapContainsScan_swapAt hslot htwin, ih]

/-- A dict literal's insertion sequence is blind. -/
theorem dictBuild_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (acc es : List (RVal × RVal)) :
    dictBuild (Heap.swapAt h pa o) acc es = dictBuild h acc es := by
  induction es generalizing acc with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      simp only [dictBuild, keyRefusal_swapAt hslot htwin, ih]

/-! ### The heap-RETURNING helpers

Seven helpers answer a new heap, so their equations are `map`-shaped
rather than plain: the swap comes OUT of the call. `Heap.update_swapAt_ne`
is what discharges each one — every write that decides is at a
non-generator object, hence not at `pa` -/

/-- `Res`'s functor action on the DECIDED value, written out: the
`Monad`-derived `Functor.map` does not reduce in a simp set, and the
heap-returning helpers' equations are all `map`-shaped. -/
def Res.mapOk {α β : Type} (f : α → β) : Res α → Res β
  | .ok a => .ok (f a)
  | .exn e => .exn e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

/-- The key refusal never DECIDES a value, so a result-map leaves it
alone — what closes the `unhashable` arm of a heap-returning helper's
equation. -/
theorem Res.mapOk_keyRefusal {α β : Type} (f : α → β) (h : Heap) (k : RVal) :
    Res.mapOk f (keyRefusal h k) = keyRefusal h k := by
  unfold keyRefusal; split <;> rfl

/-- `lst.append(x)` is blind up to the swap it carries along. -/
theorem heapAppend_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (v : RVal) :
    heapAppend (Heap.swapAt h pa o) b v
      = Res.mapOk (fun h' => Heap.swapAt h' pa o) (heapAppend h b v) := by
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    simp only [heapAppend, hslot, Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot)]
    rfl
  · cases hget : Heap.get? h b with
    | none => simp only [heapAppend, Heap.get?_swapAt_ne hba, hget]; rfl
    | some obj =>
        cases obj with
        | list xs =>
            simp only [heapAppend, Heap.get?_swapAt_ne hba, hget]
            rw [Heap.update_swapAt_ne hba]
            cases Heap.update h b (Obj.list (xs.push v)) <;> rfl
        | _ => simp only [heapAppend, Heap.get?_swapAt_ne hba, hget] <;> rfl

/-- `lst.insert(i, x)` is blind up to the swap. -/
theorem heapInsert_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (i : Int) (v : RVal) :
    heapInsert (Heap.swapAt h pa o) b i v
      = Res.mapOk (fun h' => Heap.swapAt h' pa o) (heapInsert h b i v) := by
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    simp only [heapInsert, hslot, Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot)]
    rfl
  · cases hget : Heap.get? h b with
    | none => simp only [heapInsert, Heap.get?_swapAt_ne hba, hget]; rfl
    | some obj =>
        cases obj with
        | list xs =>
            simp only [heapInsert, Heap.get?_swapAt_ne hba, hget]
            rw [Heap.update_swapAt_ne hba]
            cases Heap.update h b (Obj.list ((xs.toList.take (if i < 0 then i + xs.size else i).toNat
              ++ v :: xs.toList.drop (if i < 0 then i + xs.size else i).toNat).toArray)) <;> rfl
        | _ => simp only [heapInsert, Heap.get?_swapAt_ne hba, hget] <;> rfl

/-- `o.attr = v` is blind up to the swap (only an INSTANCE receiver
writes, and the slot holds a generator). -/
theorem heapAttrStore_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (attr : String) (v : RVal) :
    heapAttrStore (Heap.swapAt h pa o) b attr v
      = Res.mapOk (fun h' => Heap.swapAt h' pa o) (heapAttrStore h b attr v) := by
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    simp only [heapAttrStore, hslot, Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot)]
    rfl
  · cases hget : Heap.get? h b with
    | none => simp only [heapAttrStore, Heap.get?_swapAt_ne hba, hget]; rfl
    | some obj =>
        cases obj with
        | «instance» ci attrs =>
            simp only [heapAttrStore, Heap.get?_swapAt_ne hba, hget]
            rw [Heap.update_swapAt_ne hba]
            cases Heap.update h b (Obj.instance ci (Env.set attrs.toList attr v).toArray) <;> rfl
        | _ => simp only [heapAttrStore, Heap.get?_swapAt_ne hba, hget] <;> rfl

/-- `lst.pop(i)` is blind up to the swap; the popped VALUE is untouched. -/
theorem heapPop_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (i : Option Int) :
    heapPop (Heap.swapAt h pa o) b i
      = Res.mapOk (fun p => (Heap.swapAt p.1 pa o, p.2)) (heapPop h b i) := by
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    simp only [heapPop, hslot, Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot)]
    rfl
  · cases hget : Heap.get? h b with
    | none => simp only [heapPop, Heap.get?_swapAt_ne hba, hget]; rfl
    | some obj =>
        cases obj with
        | list xs =>
            cases hni : normIndex (i.getD (-1)) xs.size with
            | none => simp only [heapPop, Heap.get?_swapAt_ne hba, hget, hni]; rfl
            | some n =>
                simp only [heapPop, Heap.get?_swapAt_ne hba, hget, hni]
                rw [Heap.update_swapAt_ne hba]
                cases Heap.update h b (Obj.list ((xs.toList.eraseIdx n).toArray)) <;> rfl
        | _ => simp only [heapPop, Heap.get?_swapAt_ne hba, hget] <;> rfl

/-- `o[k] = v` is blind up to the swap — the widest of the writers (dict
and list arms, the hashability gate, and the index `TypeError`). -/
theorem heapStore_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (b : Addr) (k v : RVal) :
    heapStore (Heap.swapAt h pa o) b k v
      = Res.mapOk (fun h' => Heap.swapAt h' pa o) (heapStore h b k v) := by
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    simp only [heapStore, hslot, Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot)]
    rfl
  · cases hget : Heap.get? h b with
    | none => simp only [heapStore, Heap.get?_swapAt_ne hba, hget]; rfl
    | some obj =>
        cases obj with
        | dict es ver =>
            cases hds : dictStore es.toList k v with
            | mk es' grew =>
              by_cases hk : hashableKey k = true
              · simp only [heapStore, Heap.get?_swapAt_ne hba, hget, hds, if_pos hk]
                rw [Heap.update_swapAt_ne hba]
                cases Heap.update h b
                  (Obj.dict es'.toArray (if grew = true then ver + 1 else ver)) <;> rfl
              · simp only [heapStore, Heap.get?_swapAt_ne hba, hget, hds, if_neg hk,
                  keyRefusal_swapAt hslot htwin]
                exact (Res.mapOk_keyRefusal _ h k).symm
        | list xs =>
            cases hai : asInt k with
            | none =>
                simp only [heapStore, Heap.get?_swapAt_ne hba, hget, hai,
                  RVal.typeNameH_swapAt hslot htwin]
                rfl
            | some j =>
                cases hni : normIndex j xs.size with
                | none => simp only [heapStore, Heap.get?_swapAt_ne hba, hget, hai, hni]; rfl
                | some n =>
                    simp only [heapStore, Heap.get?_swapAt_ne hba, hget, hai, hni]
                    rw [Heap.update_swapAt_ne hba]
                    cases Heap.update h b (Obj.list ((xs.toList.set n v).toArray)) <;> rfl
        | _ => simp only [heapStore, Heap.get?_swapAt_ne hba, hget] <;> rfl

/-! ### Slot preservation across the writers

The `map`-shaped equations say where the swapped run GOES; the write-
position arms need one fact more, and it is what `PBF`'s first conjunct
asks of the post-write state: a DECIDED write leaves the slot alone. Each
writer's own arm enumeration proves it — every arm that answers a heap
writes at a list, a dict or an instance, and the slot holds a generator,
so `Heap.get?_update_ne` carries it. -/

/-- The slot holds a GENERATOR (`PayloadTwin`), so an address answering
any OTHER object is a different address — the side condition each
enumeration below reads off the writer's own arm. -/
theorem Heap.ne_slot_of_get? {h : Heap} {pa b : Addr} {o₀ obj : Obj}
    (hslot : Heap.get? h pa = some o₀) (hb : Heap.get? h b = some obj)
    (hne : obj ≠ o₀) : pa ≠ b := by
  intro hba
  subst hba
  rw [hslot] at hb
  exact hne (Option.some.inj hb).symm

/-- The same fact read off the TWIN: the slot's object is a generator, so
any address answering a dict, a list or an instance is a different address
— what every raw-`Heap.update` arm needs (`execAttrCall`'s `.clear()`). -/
theorem Heap.ne_slot_of_twin {h : Heap} {pa b : Addr} {o₀ o obj : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (hb : Heap.get? h b = some obj)
    (hne : ∀ q l c s, obj ≠ Obj.generator q l c s) : pa ≠ b := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, -⟩ := htwin
  exact Heap.ne_slot_of_get? hslot hb (hne q l₀ c₀ .running)

/-- `lst.append(x)` pins the slot: the only deciding arm writes at a list. -/
theorem heapAppend_slot (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    {b : Addr} {v : RVal} {h' : Heap} (hw : heapAppend h b v = .ok h') :
    Heap.get? h' pa = some o₀ := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, -⟩ := htwin
  cases hget : Heap.get? h b with
  | none => simp [heapAppend, hget] at hw
  | some obj =>
      cases obj with
      | list xs =>
          have hne : pa ≠ b := Heap.ne_slot_of_get? hslot hget (by simp)
          simp [heapAppend, hget] at hw
          cases hu : Heap.update h b (Obj.list (xs.push v)) with
          | none => simp [hu] at hw
          | some h₁ =>
              simp only [hu, Res.ok.injEq] at hw
              subst hw
              exact (Heap.get?_update_ne hu hne).trans hslot
      | _ => simp [heapAppend, hget] at hw

/-- `lst.insert(i, x)` pins the slot. -/
theorem heapInsert_slot (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    {b : Addr} {i : Int} {v : RVal} {h' : Heap} (hw : heapInsert h b i v = .ok h') :
    Heap.get? h' pa = some o₀ := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, -⟩ := htwin
  cases hget : Heap.get? h b with
  | none => simp [heapInsert, hget] at hw
  | some obj =>
      cases obj with
      | list xs =>
          have hne : pa ≠ b := Heap.ne_slot_of_get? hslot hget (by simp)
          simp [heapInsert, hget] at hw
          cases hu : Heap.update h b (Obj.list ((xs.toList.take
            (if i < 0 then i + xs.size else i).toNat
              ++ v :: xs.toList.drop (if i < 0 then i + xs.size else i).toNat).toArray)) with
          | none => simp [hu] at hw
          | some h₁ =>
              simp only [hu, Res.ok.injEq] at hw
              subst hw
              exact (Heap.get?_update_ne hu hne).trans hslot
      | _ => simp [heapInsert, hget] at hw

/-- `o.attr = v` pins the slot: the only deciding arm writes at an
instance. -/
theorem heapAttrStore_slot (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    {b : Addr} {attr : String} {v : RVal} {h' : Heap}
    (hw : heapAttrStore h b attr v = .ok h') : Heap.get? h' pa = some o₀ := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, -⟩ := htwin
  cases hget : Heap.get? h b with
  | none => simp [heapAttrStore, hget] at hw
  | some obj =>
      cases obj with
      | «instance» ci attrs =>
          have hne : pa ≠ b := Heap.ne_slot_of_get? hslot hget (by simp)
          simp [heapAttrStore, hget] at hw
          cases hu : Heap.update h b
            (Obj.instance ci (Env.set attrs.toList attr v).toArray) with
          | none => simp [hu] at hw
          | some h₁ =>
              simp only [hu, Res.ok.injEq] at hw
              subst hw
              exact (Heap.get?_update_ne hu hne).trans hslot
      | _ => simp [heapAttrStore, hget] at hw

/-- `lst.pop(i)` pins the slot (the popped value rides in `.2`). -/
theorem heapPop_slot (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    {b : Addr} {i : Option Int} {p : Heap × RVal} (hw : heapPop h b i = .ok p) :
    Heap.get? p.1 pa = some o₀ := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, -⟩ := htwin
  cases hget : Heap.get? h b with
  | none => simp [heapPop, hget] at hw
  | some obj =>
      cases obj with
      | list xs =>
          have hne : pa ≠ b := Heap.ne_slot_of_get? hslot hget (by simp)
          cases hni : normIndex (i.getD (-1)) xs.size with
          | none => simp [heapPop, hget, hni] at hw
          | some n =>
              simp [heapPop, hget, hni] at hw
              cases hu : Heap.update h b (Obj.list ((xs.toList.eraseIdx n).toArray)) with
              | none => simp [hu] at hw
              | some h₁ =>
                  simp only [hu, Res.ok.injEq] at hw
                  subst hw
                  exact (Heap.get?_update_ne hu hne).trans hslot
      | _ => simp [heapPop, hget] at hw

/-- `o[k] = v` pins the slot: the dict and list arms are the only ones
that write. -/
theorem heapStore_slot (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    {b : Addr} {k v : RVal} {h' : Heap} (hw : heapStore h b k v = .ok h') :
    Heap.get? h' pa = some o₀ := by
  obtain ⟨q, l₀, c₀, l₁, c₁, rfl, -⟩ := htwin
  cases hget : Heap.get? h b with
  | none => simp [heapStore, hget] at hw
  | some obj =>
      cases obj with
      | dict es ver =>
          have hne : pa ≠ b := Heap.ne_slot_of_get? hslot hget (by simp)
          cases hds : dictStore es.toList k v with
          | mk es' grew =>
              by_cases hk : hashableKey k = true
              · simp [heapStore, hget, hds, if_pos hk] at hw
                cases hu : Heap.update h b
                  (Obj.dict es'.toArray (if grew = true then ver + 1 else ver)) with
                | none => simp [hu] at hw
                | some h₁ =>
                    simp only [hu, Res.ok.injEq] at hw
                    subst hw
                    exact (Heap.get?_update_ne hu hne).trans hslot
              · simp [heapStore, hget, hds, if_neg hk] at hw
                unfold keyRefusal at hw
                split at hw <;> simp [] at hw
      | list xs =>
          have hne : pa ≠ b := Heap.ne_slot_of_get? hslot hget (by simp)
          cases hai : asInt k with
          | none => simp [heapStore, hget, hai] at hw
          | some j =>
              cases hni : normIndex j xs.size with
              | none => simp [heapStore, hget, hai, hni] at hw
              | some n =>
                  simp [heapStore, hget, hai, hni] at hw
                  cases hu : Heap.update h b (Obj.list ((xs.toList.set n v).toArray)) with
                  | none => simp [hu] at hw
                  | some h₁ =>
                      simp only [hu, Res.ok.injEq] at hw
                      subst hw
                      exact (Heap.get?_update_ne hu hne).trans hslot
      | _ => simp [heapStore, hget] at hw

/-! ### The last three equations

`sortedValH` ALLOCATES, so its equation is `map`-shaped through
`Heap.swapAt_push`; `unpackStoreH` THREADS the heap, so its generated
induction (whose motive carries the heap, and whose attribute case hands
an IH at EVERY heap) re-establishes the slot after each
`heapAttrStore`. -/

/-- `sorted(v)` is blind up to the swap it carries along: a heap-list
argument reads its elements and allocates the fresh result at the end. -/
theorem sortedValH_swapAt (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (v : RVal) (desc : Bool) :
    sortedValH (Heap.swapAt h pa o) v desc
      = Res.mapOk (fun p => (Heap.swapAt p.1 pa o, p.2)) (sortedValH h v desc) := by
  have hlt := Heap.lt_size_of_get? hslot
  cases v with
  | ref b =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · simp only [sortedValH, heq]
        cases hget : Heap.get? h b with
        | none => rfl
        | some obj =>
            cases obj with
            | list xs =>
                cases hai : (if desc then Option.none else asIntList xs.toList) with
                | some ns =>
                    simp only [hai, Heap.swapAt_push hlt, Heap.size_swapAt, Res.mapOk,
                      Res.pure_eq]
                | none =>
                    cases hsb : sortByLt desc xs.toList with
                    | ok l =>
                        simp only [hai, hsb, Res.ok_bind, Heap.swapAt_push hlt,
                          Heap.size_swapAt, Res.mapOk, Res.pure_eq]
                    | exn e => simp only [hai, hsb, Res.exn_bind, Res.mapOk, Res.pure_eq]
                    | timeout => simp only [hai, hsb, Res.timeout_bind, Res.mapOk, Res.pure_eq]
                    | unsupported msg =>
                        simp only [hai, hsb, Res.unsupported_bind, Res.mapOk, Res.pure_eq]
            -- §L53 rung 3b: the KEYS, allocating the same fresh result
            | dict es sv =>
                cases hai : (if desc then Option.none else asIntList (dictKeys es).toList) with
                | some ns =>
                    simp only [hai, Heap.swapAt_push hlt, Heap.size_swapAt, Res.mapOk,
                      Res.pure_eq]
                | none =>
                    cases hsb : sortByLt desc (dictKeys es).toList with
                    | ok l =>
                        simp only [hai, hsb, Res.ok_bind, Heap.swapAt_push hlt,
                          Heap.size_swapAt, Res.mapOk, Res.pure_eq]
                    | exn e => simp only [hai, hsb, Res.exn_bind, Res.mapOk, Res.pure_eq]
                    | timeout => simp only [hai, hsb, Res.timeout_bind, Res.mapOk, Res.pure_eq]
                    | unsupported msg =>
                        simp only [hai, hsb, Res.unsupported_bind, Res.mapOk, Res.pure_eq]
            | _ => rfl
      · simp only [sortedValH, h1, h2, Res.mapOk]
  | _ =>
      simp only [sortedValH]
      cases sortedVal _ desc <;> simp only [Res.ok_bind, Res.exn_bind, Res.timeout_bind,
        Res.unsupported_bind, Res.mapOk, Res.pure_eq]

/-- `sorted` pins the slot: it either ALLOCATES its fresh result at the end
of the heap or answers the heap it was given. -/
theorem sortedValH_slot (hslot : Heap.get? h pa = some o₀)
    {v : RVal} {desc : Bool} {p : Heap × RVal} (hw : sortedValH h v desc = .ok p) :
    Heap.get? p.1 pa = some o₀ := by
  cases v with
  | ref b =>
      cases hget : Heap.get? h b with
      | none => simp [sortedValH, hget] at hw
      | some obj =>
          cases obj with
          | list xs =>
              cases hai : (if desc then Option.none else asIntList xs.toList) with
              | some ns =>
                  simp only [sortedValH, hget, hai, Res.ok.injEq] at hw
                  subst hw
                  exact Heap.get?_push_of_get? _ hslot
              | none =>
                  cases hsb : sortByLt desc xs.toList with
                  | ok l =>
                      simp only [sortedValH, hget, hai, hsb, Res.ok_bind, Res.pure_eq,
                        Res.ok.injEq] at hw
                      subst hw
                      exact Heap.get?_push_of_get? _ hslot
                  | exn e => simp [sortedValH, hget, hai, hsb] at hw
                  | timeout => simp [sortedValH, hget, hai, hsb] at hw
                  | unsupported msg => simp [sortedValH, hget, hai, hsb] at hw
          -- §L53 rung 3b: the KEYS, allocating the same fresh result
          | dict es sv =>
              cases hai : (if desc then Option.none else asIntList (dictKeys es).toList) with
              | some ns =>
                  simp only [sortedValH, hget, hai, Res.ok.injEq] at hw
                  subst hw
                  exact Heap.get?_push_of_get? _ hslot
              | none =>
                  cases hsb : sortByLt desc (dictKeys es).toList with
                  | ok l =>
                      simp only [sortedValH, hget, hai, hsb, Res.ok_bind, Res.pure_eq,
                        Res.ok.injEq] at hw
                      subst hw
                      exact Heap.get?_push_of_get? _ hslot
                  | exn e => simp [sortedValH, hget, hai, hsb] at hw
                  | timeout => simp [sortedValH, hget, hai, hsb] at hw
                  | unsupported msg => simp [sortedValH, hget, hai, hsb] at hw
          | _ => simp [sortedValH, hget] at hw
  | _ =>
      -- the value arms answer the heap they were given; the argument is not
      -- nameable in a catch-all, so the bind is INVERTED instead of cased
      simp only [sortedValH, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at hw
      obtain ⟨r, -, hr⟩ := hw
      subst hr
      exact hslot

/-- The tuple-target attribute store is blind up to the swap AND pins the
slot — both in ONE induction, because both consume the same case
enumeration and the attribute case needs the slot fact re-established at
the heap `heapAttrStore` answered (`unpackStoreH.induct` hands that case
an IH at EVERY heap, which is exactly the motive shape this needs). -/
theorem unpackStoreH_swapAt (htwin : PayloadTwin o₀ o) :
    ∀ (h : Heap) (env : Env) (es : List Expr) (vs : List RVal),
      Heap.get? h pa = some o₀ →
      unpackStoreH (Heap.swapAt h pa o) env es vs
          = Res.mapOk (fun p => (Heap.swapAt p.1 pa o, p.2)) (unpackStoreH h env es vs)
        ∧ ∀ p, unpackStoreH h env es vs = .ok p → Heap.get? p.1 pa = some o₀ := by
  intro h env es vs
  induction h, env, es, vs using unpackStoreH.induct with
  | case1 h env =>
      intro hslot
      refine ⟨rfl, fun p hp => ?_⟩
      simp only [unpackStoreH, Res.ok.injEq] at hp
      subst hp
      exact hslot
  | case2 h env id sp es v vs ih =>
      intro hslot
      obtain ⟨heq, hpin⟩ := ih hslot
      exact ⟨by simp only [unpackStoreH]; exact heq, fun p hp => hpin p hp⟩
  | case3 h env rid sp attr sp' es v vs b hlk ih =>
      intro hslot
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [unpackStoreH, hlk, heapAttrStore_swapAt hslot htwin]
        cases hw : heapAttrStore h b attr v with
        | ok h' =>
            simp only [Res.mapOk, Res.ok_bind]
            exact (ih h' (heapAttrStore_slot hslot htwin hw)).1
        | exn e => simp only [Res.mapOk, Res.exn_bind]
        | timeout => simp only [Res.mapOk, Res.timeout_bind]
        | unsupported msg => simp only [Res.mapOk, Res.unsupported_bind]
      · simp only [unpackStoreH, hlk] at hp
        cases hw : heapAttrStore h b attr v with
        | ok h' =>
            simp only [hw, Res.ok_bind] at hp
            exact (ih h' (heapAttrStore_slot hslot htwin hw)).2 p hp
        | exn e => simp [hw] at hp
        | timeout => simp [hw] at hp
        | unsupported msg => simp [hw] at hp
  | case4 h env rid sp attr sp' es v vs val hnr hlk =>
      intro _
      cases val with
      | ref b => exact absurd rfl (hnr b)
      | _ => exact ⟨by simp only [unpackStoreH, hlk, Res.mapOk],
                fun p hp => by simp [unpackStoreH, hlk] at hp⟩
  | case5 h env rid sp attr sp' es v vs hlk =>
      intro _
      exact ⟨by simp only [unpackStoreH, hlk, Res.mapOk],
        fun p hp => by simp [unpackStoreH, hlk] at hp⟩
  | case6 h env e es v vs hnn hna =>
      intro _
      cases e with
      | name id sp => exact absurd rfl (hnn id sp)
      | «attribute» recv attr sp =>
          cases recv with
          | name rid sp' => exact absurd rfl (hna rid sp' attr sp)
          | _ => exact ⟨by simp only [unpackStoreH, Res.mapOk],
                    fun p hp => by simp [unpackStoreH] at hp⟩
      | _ => exact ⟨by simp only [unpackStoreH, Res.mapOk],
                fun p hp => by simp [unpackStoreH] at hp⟩
  | case7 es h env vs h1 h2 h3 h4 =>
      intro _
      cases es with
      | nil =>
          cases vs with
          | nil => exact absurd rfl (h1 rfl)
          | cons _ _ => exact ⟨by simp only [unpackStoreH, Res.mapOk],
                          fun p hp => by simp [unpackStoreH] at hp⟩
      | cons e es' =>
          cases vs with
          | nil => exact ⟨by simp only [unpackStoreH, Res.mapOk],
                    fun p hp => by simp [unpackStoreH] at hp⟩
          | cons v vs' => exact (h4 e es' v vs' rfl rfl).elim

end TierB

/-! ## Tier C′ — write position

The three pieces every mutating arm of `execStmt`/`execAttrCall`/
`evalExpr` is built from: the bridge that threads a `map`-shaped equation
into the continuation that writes the answer back, the write-back leaf
itself, and the allocation leaf. -/

namespace PBF
variable {a : Addr} {o₀ o : Obj} {β γ : Type}

/-- **The write-position bridge**: a heap-returning helper's `map`-shaped
equation (§Tier B), threaded into the continuation the interpreter applies
to its answer. Every mutating method call and every subscript store is
this shape. -/
theorem liftMapOk {st : FrameState} {r : Res γ} {φ : γ → γ}
    {f g : FrameState → γ → Run FrameState β}
    (hslot : Heap.get? st.world.heap a = some o₀)
    (hf : ∀ x, r = .ok x → PBF a o₀ o (f st x) (g (st.swapAt a o) (φ x))) :
    PBF a o₀ o (Run.liftRes st r ⤳ f)
      (Run.liftRes (st.swapAt a o) (Res.mapOk φ r) ⤳ g) := by
  cases r with
  | ok x => exact hf x rfl
  | exn e => exact exn hslot e
  | timeout => exact timeout
  | unsupported msg => exact unsupported

/-- **The write-back leaf**: the post-write state's swap IS the swap of
the post-write state (the heap is the only field that moves), so the whole
obligation is the slot fact at the NEW heap. -/
theorem okWrite {st : FrameState} {h' : Heap} (hslot' : Heap.get? h' a = some o₀)
    (v : β) :
    PBF a o₀ o (.ok { st with world := { st.world with heap := h' } } v)
      (.ok { st.swapAt a o with
              world := { (st.swapAt a o).world with heap := Heap.swapAt h' a o } } v) :=
  ok (a := a) (o := o) (st := { st with world := { st.world with heap := h' } }) hslot' v

/-- **The allocation leaf**: `evalExpr`'s displays and constructors append,
so the fresh address is the same on both sides and the slot survives. -/
theorem pushRef {st : FrameState} (hslot : Heap.get? st.world.heap a = some o₀)
    (g : Obj) :
    PBF a o₀ o
      (.ok { st with world := { st.world with heap := st.world.heap.push g } }
        (RVal.ref st.world.heap.size))
      (.ok { st.swapAt a o with
              world := { (st.swapAt a o).world with
                          heap := (Heap.swapAt st.world.heap a o).push g } }
        (RVal.ref (Heap.swapAt st.world.heap a o).size)) := by
  rw [Heap.swapAt_push (Heap.lt_size_of_get? hslot), Heap.size_swapAt]
  exact okWrite (Heap.get?_push_of_get? g hslot) _

end PBF

/-- The attribute READ is blind: its PLAN is (§Tier B) and every outcome
carries the receiver's own frame — `evalExpr`'s `.attribute` arm and
`execStmt`'s attribute `+=` both consume this. -/
theorem attrReadResult_pb {pa : Addr} {o₀ o : Obj} {st : FrameState}
    (hslot : Heap.get? st.world.heap pa = some o₀) (htwin : PayloadTwin o₀ o)
    (m : Module) (b : Addr) (attr : String) :
    PBF pa o₀ o (attrReadResult m st b attr) (attrReadResult m (st.swapAt pa o) b attr) := by
  simp only [attrReadResult, FrameState.swapAt_world, World.swapAt_heap,
    attrReadPlan_swapAt hslot htwin]
  cases attrReadPlan m st.world.heap b attr with
  | value v => exact PBF.ok hslot _
  | boundMethod => exact PBF.unsupported
  | missing => exact PBF.exn hslot _
  | refuse msg => exact PBF.unsupported
  | dangling => exact PBF.unsupported

/-- The trace-clock admission is blind: it reads the frame's locals and
the world's GLOBALS, and the swap moves neither. -/
theorem isClockCall_swapAt {pa : Addr} {o : Obj} (m : Module) (st : FrameState)
    (recv : Expr) (attr : String) :
    isClockCall m (st.swapAt pa o) recv attr = isClockCall m st recv attr := by
  cases recv <;> simp only [isClockCall, clockRecvOk, FrameState.swapAt_world,
    FrameState.swapAt_locals, World.swapAt_globals]

/-! ## Tier D — the 18 conjuncts

One statement per member of the interpreter's mutual block
(Semantics.lean:4232–6207), `fuelMono`'s conjunct order — ClockErase.lean's
`CE` geometry. `PBAll` is what the mutual induction on fuel proves; each
arm is a composition of §Tier C's combinators over §Tier B's equations.

Every conjunct is stated here so that the remainder of this proof is
ENUMERATED rather than described: `payloadBlind_of_execGen` below shows
the reduction closes, and what is owed is exactly the arms. -/

section Conjuncts
variable (pa : Addr) (o₀ o : Obj)

abbrev PBEvalExpr (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (e : Expr),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (evalExpr m fuel st e) (evalExpr m fuel (st.swapAt pa o) e)

abbrev PBEvalExprs (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (es : List Expr),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (evalExprs m fuel st es) (evalExprs m fuel (st.swapAt pa o) es)

abbrev PBEvalDictItems (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (keys values : List Expr),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (evalDictItems m fuel st keys values)
      (evalDictItems m fuel (st.swapAt pa o) keys values)

abbrev PBExecAttrCall (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (b : Addr) (attr : String) (args : List Expr),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execAttrCall m fuel st b attr args)
      (execAttrCall m fuel (st.swapAt pa o) b attr args)

abbrev PBEvalBoolChain (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (op : BoolOp) (e : Expr) (rest : List Expr),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (evalBoolChain m fuel st op e rest)
      (evalBoolChain m fuel (st.swapAt pa o) op e rest)

abbrev PBEvalCompareChain (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (lhs : RVal) (ops : List CmpOp)
    (comparators : List Expr),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (evalCompareChain m fuel st lhs ops comparators)
      (evalCompareChain m fuel (st.swapAt pa o) lhs ops comparators)

abbrev PBExecStmt (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (s : Stmt),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execStmt m fuel st s) (execStmt m fuel (st.swapAt pa o) s)

abbrev PBExecStmts (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (ss : List Stmt),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execStmts m fuel st ss) (execStmts m fuel (st.swapAt pa o) ss)

abbrev PBExecFor (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (target : Expr) (xs : List RVal)
    (body : List Stmt),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execFor m fuel st target xs body)
      (execFor m fuel (st.swapAt pa o) target xs body)

abbrev PBExecForList (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (target : Expr) (b : Addr) (i : Nat)
    (body : List Stmt),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execForList m fuel st target b i body)
      (execForList m fuel (st.swapAt pa o) target b i body)

abbrev PBExecWhile (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (test : Expr) (body orelse : List Stmt),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execWhile m fuel st test body orelse)
      (execWhile m fuel (st.swapAt pa o) test body orelse)

abbrev PBCallIn (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (fname : String) (args : Array RVal),
    Heap.get? w.heap pa = some o₀ →
    PBW pa o₀ o (callIn m fuel w fname args)
      (callIn m fuel (w.swapAt pa o) fname args)

/-- The load-bearing one: `stepIter` is the ONLY reader of a generator's
payload, and at `pa` — a `.running` object — it refuses before reaching
either field. -/
abbrev PBStepIter (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (b : Addr),
    Heap.get? w.heap pa = some o₀ →
    PBW pa o₀ o (stepIter m fuel w b) (stepIter m fuel (w.swapAt pa o) b)

abbrev PBExecGen (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (k : GenCont),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execGen m fuel st k) (execGen m fuel (st.swapAt pa o) k)

abbrev PBExecForGen (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (target : Expr) (b : Addr) (body : List Stmt),
    Heap.get? st.world.heap pa = some o₀ →
    PBF pa o₀ o (execForGen m fuel st target b body)
      (execForGen m fuel (st.swapAt pa o) target b body)

abbrev PBDrainIter (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (b : Addr),
    Heap.get? w.heap pa = some o₀ →
    PBW pa o₀ o (drainIter m fuel w b) (drainIter m fuel (w.swapAt pa o) b)

abbrev PBAnyAllIter (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (b : Addr) (isAll : Bool),
    Heap.get? w.heap pa = some o₀ →
    PBW pa o₀ o (anyAllIter m fuel w b isAll)
      (anyAllIter m fuel (w.swapAt pa o) b isAll)

abbrev PBCallClosure (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (name : String) (params : Array Param)
    (ao lo ig : Bool) (body : Array Stmt) (cap : REnv) (args : Array RVal),
    Heap.get? w.heap pa = some o₀ →
    PBW pa o₀ o (callClosure m fuel w name params ao lo ig body cap args)
      (callClosure m fuel (w.swapAt pa o) name params ao lo ig body cap args)

/-- **The whole-block statement** — what the mutual induction on fuel
proves, `fuelMono`'s conjunct order. -/
abbrev PBAll (fuel : Nat) : Prop :=
  PBEvalExpr pa o₀ o fuel ∧ PBEvalExprs pa o₀ o fuel ∧
  PBEvalBoolChain pa o₀ o fuel ∧ PBEvalCompareChain pa o₀ o fuel ∧
  PBExecStmt pa o₀ o fuel ∧ PBExecStmts pa o₀ o fuel ∧
  PBExecWhile pa o₀ o fuel ∧ PBCallIn pa o₀ o fuel ∧
  PBExecFor pa o₀ o fuel ∧ PBEvalDictItems pa o₀ o fuel ∧
  PBExecForList pa o₀ o fuel ∧ PBExecAttrCall pa o₀ o fuel ∧
  PBStepIter pa o₀ o fuel ∧ PBExecGen pa o₀ o fuel ∧
  PBExecForGen pa o₀ o fuel ∧ PBDrainIter pa o₀ o fuel ∧
  PBAnyAllIter pa o₀ o fuel ∧ PBCallClosure pa o₀ o fuel

end Conjuncts

/-! ## Tier D arms — the composition-only members

The five members whose bodies are nothing but `Run` plumbing over
recursive calls: they need §Tier C's combinators and the block IH, and no
new helper reasoning at all. `ClockErase.lean`'s `_succ` shape — each is a
standalone theorem taking `PBAll fuel` as the induction hypothesis, so the
block's arms land one at a time rather than all-or-nothing. -/

section Arms
variable {pa : Addr} {o₀ o : Obj} {fuel : Nat}

/-- Argument lists: `evalExpr` then recurse, cons the values. -/
theorem pbEvalExprs_succ (ih : PBAll pa o₀ o fuel) : PBEvalExprs pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, ihEs, -⟩ := ih
  intro m st es hslot
  cases es with
  | nil => simp only [evalExprs]; exact PBF.ok hslot _
  | cons e rest =>
      simp only [evalExprs]
      exact PBF.bind (ihE m st e hslot) fun s v _ hs =>
        PBF.bind (ihEs m s rest hs) fun s2 vs _ hs2 => PBF.ok hs2 _

/-- Dict literals: key, value, recurse — CPython's `BUILD_MAP` order. -/
theorem pbEvalDictItems_succ (ih : PBAll pa o₀ o fuel) :
    PBEvalDictItems pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, -, -, -, -, -, -, -, -, ihItems, -⟩ := ih
  intro m st keys values hslot
  cases keys with
  | nil =>
      cases values with
      | nil => simp only [evalDictItems]; exact PBF.ok hslot _
      | cons _ _ => simp only [evalDictItems]; exact PBF.unsupported
  | cons k ks =>
      cases values with
      | nil => simp only [evalDictItems]; exact PBF.unsupported
      | cons v vs =>
          simp only [evalDictItems]
          exact PBF.bind (ihE m st k hslot) fun s kv _ hs =>
            PBF.bind (ihE m s v hs) fun s2 vv _ hs2 =>
              PBF.bind (ihItems m s2 ks vs hs2) fun s3 rest _ hs3 => PBF.ok hs3 _

/-- Statement sequences: run one, and only `.next` continues. -/
theorem pbExecStmts_succ (ih : PBAll pa o₀ o fuel) : PBExecStmts pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, ihS, ihSs, -⟩ := ih
  intro m st ss hslot
  cases ss with
  | nil => simp only [execStmts]; exact PBF.ok hslot _
  | cons s rest =>
      simp only [execStmts]
      refine PBF.bind (ihS m st s hslot) fun s2 flow _ hs2 => ?_
      cases flow with
      | next => exact ihSs m s2 rest hs2
      | ret v => exact PBF.ok hs2 _
      | brk => exact PBF.ok hs2 _
      | cont => exact PBF.ok hs2 _

/-- The WHOLE drain: step, and recurse until exhaustion. -/
theorem pbDrainIter_succ (ih : PBAll pa o₀ o fuel) : PBDrainIter pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ihIter, -, -, ihDrain, -⟩ := ih
  intro m w b hslot
  simp only [drainIter]
  refine PBW.bind (ihIter m w b hslot) fun w2 r _ hw2 => ?_
  cases r with
  | none => exact PBW.ok hw2 _
  | some v => exact PBW.bind (ihDrain m w2 b hw2) fun w3 vs _ hw3 => PBW.ok hw3 _

/-- The SHORT-CIRCUIT drain: step, test, stop or recurse. The one arm here
that consumes a §Tier B equation (`truthyH`), and the reason these lemmas
take the twin. -/
theorem pbAnyAllIter_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBAnyAllIter pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ihIter, -, -, -, ihAny, -⟩ := ih
  intro m w b isAll hslot
  simp only [anyAllIter]
  refine PBW.bind (ihIter m w b hslot) fun w2 r _ hw2 => ?_
  cases r with
  | none => exact PBW.ok hw2 _
  | some v =>
      -- The two truthiness probes are EQUAL, not defeq, so the lifted pair is
      -- stated explicitly; `PBW.bind` then meets the goal's match by iota.
      have hlift : PBW pa o₀ o (Run.liftRes w2 (truthyH w2.heap v))
          (Run.liftRes (w2.swapAt pa o) (truthyH (Heap.swapAt w2.heap pa o) v)) := by
        rw [truthyH_swapAt hw2 htwin]
        exact PBW.liftRes hw2 _
      refine PBW.bind hlift fun w3 bb _ hw3 => ?_
      exact PBW.ite (fun _ => PBW.ok hw3 _) (fun _ => ihAny m w3 b isAll hw3)

/-! ### The composition-and-dispatch arms

Nine more members, and between them they consume every §Tier B equation
the block's non-`evalExpr` control flow can reach: `truthyH`,
`assignToH`, `evalCompareOpH`, `RVal.typeNameH`. Nothing here is a new
idea — each is §Tier C's combinators over the block IH, which is what
`_succ` theorems taking `PBAll fuel` buy: an arm at a time. -/

theorem pbEvalBoolChain_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBEvalBoolChain pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, -, ihBool, -⟩ := ih
  intro m st op e rest hslot
  simp only [evalBoolChain]
  refine PBF.bind (ihE m st e hslot) fun s v _ hs => ?_
  cases rest with
  | nil => exact PBF.ok hs _
  | cons e' rest' =>
      have hlift : PBF pa o₀ o (Run.liftRes s (truthyH s.world.heap v))
          (Run.liftRes (s.swapAt pa o) (truthyH (Heap.swapAt s.world.heap pa o) v)) := by
        rw [truthyH_swapAt hs htwin]
        exact PBF.liftRes hs _
      refine PBF.bind hlift fun s2 b _ hs2 => ?_
      cases op with
      | and => exact PBF.ite (fun _ => ihBool m s2 .and e' rest' hs2) (fun _ => PBF.ok hs2 _)
      | or => exact PBF.ite (fun _ => PBF.ok hs2 _) (fun _ => ihBool m s2 .or e' rest' hs2)

theorem pbEvalCompareChain_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBEvalCompareChain pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, -, -, ihCmp, -⟩ := ih
  intro m st lhs ops comparators hslot
  simp only [evalCompareChain]
  cases ops with
  | nil =>
      cases comparators with
      | nil => exact PBF.ok hslot _
      | cons _ _ => exact PBF.unsupported
  | cons op ops' =>
      cases comparators with
      | nil => exact PBF.unsupported
      | cons e rest =>
          refine PBF.bind (ihE m st e hslot) fun s rhs _ hs => ?_
          have hlift : PBF pa o₀ o
              (Run.liftRes s (evalCompareOpH s.world.heap fuel op lhs rhs))
              (Run.liftRes (s.swapAt pa o)
                (evalCompareOpH (Heap.swapAt s.world.heap pa o) fuel op lhs rhs)) := by
            rw [evalCompareOpH_swapAt hs htwin]
            exact PBF.liftRes hs _
          refine PBF.bind hlift fun s2 b _ hs2 => ?_
          exact PBF.ite (fun _ => ihCmp m s2 rhs ops' rest hs2) (fun _ => PBF.ok hs2 _)

theorem pbExecFor_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecFor pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, ihSs, -, -, ihFor, -⟩ := ih
  intro m st target xs body hslot
  simp only [execFor]
  cases xs with
  | nil => exact PBF.ok hslot _
  | cons x rest =>
      have hlift : PBF pa o₀ o
          (Run.liftRes st (assignToH st.world.heap st.locals target x))
          (Run.liftRes (st.swapAt pa o)
            (assignToH (Heap.swapAt st.world.heap pa o) st.locals target x)) := by
        rw [assignToH_swapAt hslot htwin]
        exact PBF.liftRes hslot _
      refine PBF.bind hlift fun s env₁ _ hs => ?_
      refine PBF.bind (ihSs m { s with locals := env₁ } body hs) fun s2 flow _ hs2 => ?_
      cases flow with
      | next => exact ihFor m s2 target rest body hs2
      | cont => exact ihFor m s2 target rest body hs2
      | brk => exact PBF.ok hs2 _
      | ret v => exact PBF.ok hs2 _

theorem pbExecWhile_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecWhile pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, -, -, -, -, ihSs, ihWhile, -⟩ := ih
  intro m st test body orelse hslot
  simp only [execWhile]
  refine PBF.bind (ihE m st test hslot) fun s t _ hs => ?_
  have hlift : PBF pa o₀ o (Run.liftRes s (truthyH s.world.heap t))
      (Run.liftRes (s.swapAt pa o) (truthyH (Heap.swapAt s.world.heap pa o) t)) := by
    rw [truthyH_swapAt hs htwin]
    exact PBF.liftRes hs _
  refine PBF.bind hlift fun s2 b _ hs2 => ?_
  refine PBF.ite (fun _ => ?_) (fun _ => ihSs m s2 orelse hs2)
  refine PBF.bind (ihSs m s2 body hs2) fun s3 flow _ hs3 => ?_
  cases flow with
  | next => exact ihWhile m s3 test body orelse hs3
  | cont => exact ihWhile m s3 test body orelse hs3
  | brk => exact PBF.ok hs3 _
  | ret v => exact PBF.ok hs3 _

theorem pbExecForGen_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecForGen pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, ihSs, -, -, -, -, -, -, ihIter, -, ihForGen, -⟩ := ih
  intro m st target b body hslot
  simp only [execForGen]
  refine PBF.bind (PBW.withLocals (ihIter m st.world b hslot)) fun s r _ hs => ?_
  cases r with
  | none => exact PBF.ok hs _
  | some v =>
      have hlift : PBF pa o₀ o
          (Run.liftRes s (assignToH s.world.heap s.locals target v))
          (Run.liftRes (s.swapAt pa o)
            (assignToH (Heap.swapAt s.world.heap pa o) s.locals target v)) := by
        rw [assignToH_swapAt hs htwin]
        exact PBF.liftRes hs _
      refine PBF.bind hlift fun s2 env₁ _ hs2 => ?_
      refine PBF.bind (ihSs m { s2 with locals := env₁ } body hs2) fun s3 flow _ hs3 => ?_
      cases flow with
      | next => exact ihForGen m s3 target b body hs3
      | cont => exact ihForGen m s3 target b body hs3
      | brk => exact PBF.ok hs3 _
      | ret v => exact PBF.ok hs3 _

theorem pbExecForList_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecForList pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, ihSs, -, -, -, -, ihForList, -, -, -, ihForGen, -⟩ := ih
  intro m st target b i body hslot
  simp only [execForList, FrameState.swapAt_world, World.swapAt_heap]
  rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
  · rw [heq]
    cases hget : Heap.get? st.world.heap b with
    | none => exact PBF.unsupported
    | some obj =>
        cases obj with
        | list xs =>
            refine PBF.ite (fun _ => ?_) (fun _ => PBF.ok hslot _)
            have hlift : PBF pa o₀ o
                (Run.liftRes st (assignToH st.world.heap st.locals target (xs.getD i .none)))
                (Run.liftRes (st.swapAt pa o)
                  (assignToH (Heap.swapAt st.world.heap pa o) st.locals target
                    (xs.getD i .none))) := by
              rw [assignToH_swapAt hslot htwin]
              exact PBF.liftRes hslot _
            refine PBF.bind hlift fun s env₁ _ hs => ?_
            refine PBF.bind (ihSs m { s with locals := env₁ } body hs) fun s2 flow _ hs2 => ?_
            cases flow with
            | next => exact ihForList m s2 target b (i + 1) body hs2
            | cont => exact ihForList m s2 target b (i + 1) body hs2
            | brk => exact PBF.ok hs2 _
            | ret v => exact PBF.ok hs2 _
        | «instance» ci attrs => exact PBF.exn hslot _
        | generator qn l c s =>
            exact PBF.ite (fun _ => PBF.unsupported)
              (fun _ => ihForGen m st target b body hslot)
        | _ => exact PBF.unsupported
  · rw [h1, h2]
    exact PBF.ite (fun _ => PBF.unsupported) (fun _ => ihForGen m st target b body hslot)

theorem pbCallClosure_succ (ih : PBAll pa o₀ o fuel) : PBCallClosure pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, ihSs, -⟩ := ih
  intro m w name params ao lo ig body cap args hslot
  simp only [callClosure]
  refine PBW.ite (fun _ => PBW.unsupported) fun _ => ?_
  refine PBW.ite (fun _ => PBW.unsupported) fun _ => ?_
  refine PBW.ite (fun _ => PBW.exn hslot _) fun _ => ?_
  refine PBW.ite (fun _ => PBW.push hslot) fun _ => ?_
  refine PBF.toWorld ?_
  refine PBF.bind (ihSs m ⟨w, mkCallEnv params args ++ cap⟩ body.toList hslot)
    fun s flow _ hs => ?_
  cases flow with
  | ret v => exact PBF.ok hs _
  | next => exact PBF.ok hs _
  | brk => exact PBF.unsupported
  | cont => exact PBF.unsupported

theorem pbCallIn_succ (ih : PBAll pa o₀ o fuel) : PBCallIn pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, ihSs, -⟩ := ih
  intro m w fname args hslot
  simp only [callIn]
  cases findFunction m fname with
  | none => exact PBW.exn hslot _
  | some f =>
      refine PBW.ite (fun _ => PBW.unsupported) fun _ => ?_
      refine PBW.ite (fun _ => PBW.unsupported) fun _ => ?_
      refine PBW.ite (fun _ => PBW.exn hslot _) fun _ => ?_
      refine PBW.ite (fun _ => PBW.push hslot) fun _ => ?_
      refine PBF.toWorld ?_
      refine PBF.bind (ihSs m ⟨w, mkCallEnv f.params args⟩ f.body.toList hslot)
        fun s flow _ hs => ?_
      cases flow with
      | ret v => exact PBF.ok hs _
      | next => exact PBF.ok hs _
      | brk => exact PBF.unsupported
      | cont => exact PBF.unsupported

theorem pbStepIter_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBStepIter pa o₀ o (fuel + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ihGen, -⟩ := ih
  intro m w b hslot
  simp only [stepIter, World.swapAt_heap]
  by_cases hba : b = pa
  · subst hba
    obtain ⟨q, l₀, c₀, l₁, c₁, rfl, rfl⟩ := htwin
    rw [hslot, Heap.get?_swapAt_self (Heap.lt_size_of_get? hslot)]
    exact PBW.exn hslot _
  · rw [Heap.get?_swapAt_ne hba]
    cases hget : Heap.get? w.heap b with
    | none => exact PBW.unsupported
    | some obj =>
        cases obj with
        | generator qname locals cont status =>
            cases status with
            | closed => exact PBW.ok hslot _
            | running => exact PBW.exn hslot _
            | created =>
                simp only [Heap.update_swapAt_ne hba]
                cases hu : Heap.update w.heap b (Obj.generator qname locals cont .running) with
                | none => exact PBW.unsupported
                | some h₁ =>
                    have hslot₁ : Heap.get? h₁ pa = some o₀ :=
                      (Heap.get?_update_ne hu (Ne.symm hba)).trans hslot
                    refine PBF.toWorld ?_
                    refine PBF.bindE (ihGen m ⟨{ w with heap := h₁ }, locals⟩ cont hslot₁)
                      (fun s r _ hs => ?_) (fun s e _ hs => ?_)
                    · cases r with
                      | none =>
                          simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                            World.swapAt_heap, Heap.update_swapAt_ne hba]
                          cases hu2 : Heap.update s.world.heap b
                            (Obj.generator qname s.locals [] .closed) with
                          | none => exact PBF.unsupported
                          | some h₂ =>
                              exact PBF.ok ((Heap.get?_update_ne hu2 (Ne.symm hba)).trans hs) _
                      | some vc =>
                          obtain ⟨v, cont'⟩ := vc
                          simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                            World.swapAt_heap, Heap.update_swapAt_ne hba]
                          cases hu2 : Heap.update s.world.heap b
                            (Obj.generator qname s.locals cont' .suspended) with
                          | none => exact PBF.unsupported
                          | some h₂ =>
                              exact PBF.ok ((Heap.get?_update_ne hu2 (Ne.symm hba)).trans hs) _
                    · simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                        World.swapAt_heap, Heap.update_swapAt_ne hba]
                      cases hu2 : Heap.update s.world.heap b
                        (Obj.generator qname s.locals [] .closed) with
                      | none => exact PBF.unsupported
                      | some h₂ =>
                          exact PBF.exn ((Heap.get?_update_ne hu2 (Ne.symm hba)).trans hs) _
            | suspended =>
                simp only [Heap.update_swapAt_ne hba]
                cases hu : Heap.update w.heap b (Obj.generator qname locals cont .running) with
                | none => exact PBW.unsupported
                | some h₁ =>
                    have hslot₁ : Heap.get? h₁ pa = some o₀ :=
                      (Heap.get?_update_ne hu (Ne.symm hba)).trans hslot
                    refine PBF.toWorld ?_
                    refine PBF.bindE (ihGen m ⟨{ w with heap := h₁ }, locals⟩ cont hslot₁)
                      (fun s r _ hs => ?_) (fun s e _ hs => ?_)
                    · cases r with
                      | none =>
                          simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                            World.swapAt_heap, Heap.update_swapAt_ne hba]
                          cases hu2 : Heap.update s.world.heap b
                            (Obj.generator qname s.locals [] .closed) with
                          | none => exact PBF.unsupported
                          | some h₂ =>
                              exact PBF.ok ((Heap.get?_update_ne hu2 (Ne.symm hba)).trans hs) _
                      | some vc =>
                          obtain ⟨v, cont'⟩ := vc
                          simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                            World.swapAt_heap, Heap.update_swapAt_ne hba]
                          cases hu2 : Heap.update s.world.heap b
                            (Obj.generator qname s.locals cont' .suspended) with
                          | none => exact PBF.unsupported
                          | some h₂ =>
                              exact PBF.ok ((Heap.get?_update_ne hu2 (Ne.symm hba)).trans hs) _
                    · simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                        World.swapAt_heap, Heap.update_swapAt_ne hba]
                      cases hu2 : Heap.update s.world.heap b
                        (Obj.generator qname s.locals [] .closed) with
                      | none => exact PBF.unsupported
                      | some h₂ =>
                          exact PBF.exn ((Heap.get?_update_ne hu2 (Ne.symm hba)).trans hs) _
        | _ =>
            rw [RVal.typeNameH_swapAt hslot htwin]
            exact PBW.exn hslot _

/-! ### The continuation walker

`execGen` is the block's second-largest member and the one whose shape the
generator tier lives in — ten frame kinds, three of which read the heap.
It writes NOTHING (the write-backs belong to `stepIter`), so every arm is
§Tier C over the block IH again; the twin appears only where a frame
carries an address (`forList`/`enumList`, and `forHere`'s `.ref`
dispatch), where a generator referent is the LAZY cursor on both sides. -/

theorem pbExecGen_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecGen pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, -, -, -, ihS, -, -, -, -, -, -, -, ihIter, ihGen, -⟩ := ih
  intro m st k hslot
  cases k with
  | nil =>
      simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
      exact PBF.ok hslot _
  | cons frame k' =>
      cases frame with
      | block ss =>
          cases ss with
          | nil =>
              simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
              exact ihGen m st k' hslot
          | cons s ss =>
              simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
              cases genPlan s with
              | delegate =>
                  refine PBF.bind (ihS m st s hslot) fun s2 flow _ hs2 => ?_
                  cases flow with
                  | next => exact ihGen m s2 (.block ss :: k') hs2
                  | ret v =>
                      cases v with
                      | none => exact PBF.ok hs2 _
                      | _ => exact PBF.unsupported
                  | brk =>
                      cases genBreak k' with
                      | none => exact PBF.unsupported
                      | some k'' => exact ihGen m s2 k'' hs2
                  | cont =>
                      cases genContinue k' with
                      | none => exact PBF.unsupported
                      | some k'' => exact ihGen m s2 k'' hs2
              | yieldHere e =>
                  refine PBF.bind (ihE m st e hslot) fun s2 v _ hs2 => ?_
                  exact PBF.ok hs2 _
              | branch test body orelse =>
                  refine PBF.bind (ihE m st test hslot) fun s2 t _ hs2 => ?_
                  have hlift : PBF pa o₀ o (Run.liftRes s2 (truthyH s2.world.heap t))
                      (Run.liftRes (s2.swapAt pa o)
                        (truthyH (Heap.swapAt s2.world.heap pa o) t)) := by
                    rw [truthyH_swapAt hs2 htwin]
                    exact PBF.liftRes hs2 _
                  refine PBF.bind hlift fun s3 b _ hs3 => ?_
                  exact ihGen m s3 _ hs3
              | whileHere test body orelse => exact ihGen m st _ hslot
              | forHere target iter body =>
                  refine PBF.bind (ihE m st iter hslot) fun s2 it _ hs2 => ?_
                  cases it with
                  | listV xs => exact ihGen m s2 _ hs2
                  | tuple xs => exact ihGen m s2 _ hs2
                  | ntuple tn fs xs => exact ihGen m s2 _ hs2
                  | str sv => exact ihGen m s2 _ hs2
                  | rangeV lo hi step =>
                      refine PBF.bind (PBF.liftRes hs2 _) fun s3 xs _ hs3 => ?_
                      exact ihGen m s3 _ hs3
                  | ref ad =>
                      rcases Heap.get?_swapAt_twin (b := ad) hs2 htwin with
                        heq | ⟨_, _, _, _, _, h1, h2⟩
                      · simp only [FrameState.swapAt_world, World.swapAt_heap, heq]
                        cases hget : Heap.get? s2.world.heap ad with
                        | none => exact PBF.unsupported
                        | some obj =>
                            cases obj with
                            | list xs => simp only []; exact ihGen m s2 _ hs2
                            | generator qn l c stt => simp only []; exact ihGen m s2 _ hs2
                            | «instance» ci attrs => simp only []; exact PBF.exn hs2 _
                            | closure _ _ _ _ _ _ _ _ => simp only []; exact PBF.exn hs2 _
                            | _ => simp only []; exact PBF.unsupported
                      · simp only [FrameState.swapAt_world, World.swapAt_heap, h1, h2]
                        exact ihGen m s2 _ hs2
                  | _ => exact PBF.exn hs2 _
              | refuse msg => exact PBF.unsupported
      | forSeq target xs body =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          cases xs with
          | nil => exact ihGen m st k' hslot
          | cons x rest =>
              have hlift : PBF pa o₀ o
                  (Run.liftRes st (assignToH st.world.heap st.locals target x))
                  (Run.liftRes (st.swapAt pa o)
                    (assignToH (Heap.swapAt st.world.heap pa o) st.locals target x)) := by
                rw [assignToH_swapAt hslot htwin]
                exact PBF.liftRes hslot _
              refine PBF.bind hlift fun s2 env₁ _ hs2 => ?_
              exact ihGen m { s2 with locals := env₁ } _ hs2
      | forList target ad i body =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          rcases Heap.get?_swapAt_twin (b := ad) hslot htwin with
            heq | ⟨_, _, _, _, _, h1, h2⟩
          · rw [heq]
            cases hget : Heap.get? st.world.heap ad with
            | none => exact PBF.unsupported
            | some obj =>
                cases obj with
                | list xs =>
                    refine PBF.ite (fun _ => ?_) (fun _ => ihGen m st k' hslot)
                    have hlift : PBF pa o₀ o
                        (Run.liftRes st
                          (assignToH st.world.heap st.locals target (xs.getD i .none)))
                        (Run.liftRes (st.swapAt pa o)
                          (assignToH (Heap.swapAt st.world.heap pa o) st.locals target
                            (xs.getD i .none))) := by
                      rw [assignToH_swapAt hslot htwin]
                      exact PBF.liftRes hslot _
                    refine PBF.bind hlift fun s2 env₁ _ hs2 => ?_
                    exact ihGen m { s2 with locals := env₁ } _ hs2
                | «instance» ci attrs => exact PBF.exn hslot _
                | _ => exact PBF.unsupported
          · rw [h1, h2]
            exact PBF.unsupported
      | forGen target ad body =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          refine PBF.bind (PBW.withLocals (ihIter m st.world ad hslot)) fun s2 r _ hs2 => ?_
          cases r with
          | none => exact ihGen m s2 k' hs2
          | some v =>
              have hlift : PBF pa o₀ o
                  (Run.liftRes s2 (assignToH s2.world.heap s2.locals target v))
                  (Run.liftRes (s2.swapAt pa o)
                    (assignToH (Heap.swapAt s2.world.heap pa o) s2.locals target v)) := by
                rw [assignToH_swapAt hs2 htwin]
                exact PBF.liftRes hs2 _
              refine PBF.bind hlift fun s3 env₁ _ hs3 => ?_
              exact ihGen m { s3 with locals := env₁ } _ hs3
      | enumSeq i xs =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          cases xs with
          | nil => exact ihGen m st k' hslot
          | cons x rest => exact PBF.ok hslot _
      | enumList i ad cur =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          rcases Heap.get?_swapAt_twin (b := ad) hslot htwin with
            heq | ⟨_, _, _, _, _, h1, h2⟩
          · rw [heq]
            cases hget : Heap.get? st.world.heap ad with
            | none => exact PBF.unsupported
            | some obj =>
                cases obj with
                | list xs =>
                    exact PBF.ite (fun _ => PBF.ok hslot _) (fun _ => ihGen m st k' hslot)
                | _ => exact PBF.unsupported
          · rw [h1, h2]
            exact PBF.unsupported
      -- §3c-i-c: the trunk CONSTRUCTS an `enumDict` frame (`enumFrame` is
      -- shared) but refuses when STEPPING it, and a refusal is blind
      | enumDict i ad cur n sv =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          exact PBF.unsupported
      -- §iter: the trunk never CONSTRUCTS an `iterDict` frame (`iterFrame` has
      -- one caller and it is the rebuild's), and a refusal is blind
      | iterDict ad cur n sv =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          exact PBF.unsupported
      -- §iterList: likewise never constructed by the trunk, and blind
      | iterList ad cur =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          exact PBF.unsupported
      -- §3a: the trunk's `forDict` arm refuses, and a refusal is blind
      | forDict tg ad i n sv kd bd =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          exact PBF.unsupported
      | countFrom cur step =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          exact PBF.ok hslot _
      | whileLoop test body orelse =>
          simp only [execGen, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
          refine PBF.bind (ihE m st test hslot) fun s2 t _ hs2 => ?_
          have hlift : PBF pa o₀ o (Run.liftRes s2 (truthyH s2.world.heap t))
              (Run.liftRes (s2.swapAt pa o)
                (truthyH (Heap.swapAt s2.world.heap pa o) t)) := by
            rw [truthyH_swapAt hs2 htwin]
            exact PBF.liftRes hs2 _
          refine PBF.bind hlift fun s3 b _ hs3 => ?_
          exact PBF.ite (fun _ => ihGen m s3 _ hs3) (fun _ => ihGen m s3 _ hs3)

/-! ### The write-position arms

The three members that MUTATE, and the reason §Tier C′ exists: every one
of their write sites is `Run.liftRes` of a heap-returning helper followed
by a write-back, so each is `PBF.liftMapOk` over the helper's §Tier B
equation, closed by `PBF.okWrite` at the slot fact the writer's own
enumeration gives (`heapAppend_slot` and friends).

**Reading the bare `simp only []`s below.** `cases` substitutes a constructor
into the member's own `match` WITHOUT iota-reducing it, and the stuck arm's
pattern binders then SHADOW the names just introduced — so a following `cases`
on an inner scrutinee generalizes the wrong occurrence and the failure
surfaces as a type mismatch whose expected type still prints
`match <constructor> with …`. `simp only []` reduces the match and nothing
else, which is why it appears BETWEEN two `cases` and nowhere else. The dual
is worth the line too: where the matcher's decision tree tests an ELEMENT
before the list (`[.ref a]` before `vs`, `[.str sub]` before `[v]`,
`[.subscript …]` before `[t]`) there is nothing to reduce until that element
is cased, `simp only []` reports "no progress", and the fix is the opposite
one — case the element first. -/

/-- The builtin method tier: `.get`/`.clear` on a dict, `.append`/`.pop`/
`.insert` on a list, and instance methods through `callIn`. The plan is
blind (§Tier B), and each mutator is one bridge. -/
theorem pbExecAttrCall_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecAttrCall pa o₀ o (fuel + 1) := by
  obtain ⟨-, ihEs, -, -, -, -, -, ihIn, -⟩ := ih
  intro m st b attr args hslot
  simp only [execAttrCall, FrameState.swapAt_world, World.swapAt_heap,
    attrCallPlan_swapAt hslot htwin]
  cases attrCallPlan m st.world.heap b attr with
  | instMethod qname =>
      refine PBF.bind (ihEs m st args hslot) fun s vs _ hs => ?_
      exact PBW.withLocals (ihIn m s.world qname _ hs)
  | instAttrValue => exact PBF.unsupported
  | attrMissing => exact PBF.exn hslot _
  | dictGet =>
      refine PBF.bind (ihEs m st args hslot) fun s vs _ hs => ?_
      cases vs with
      | nil => exact PBF.exn hs _
      | cons k rest =>
          cases rest with
          | nil =>
              simp only [FrameState.swapAt_world, World.swapAt_heap, heapGet_swapAt hs htwin]
              exact PBF.liftRes hs _
          | cons d rest' =>
              cases rest' with
              | nil =>
                  simp only [FrameState.swapAt_world, World.swapAt_heap,
                    heapGet_swapAt hs htwin]
                  exact PBF.liftRes hs _
              | cons _ _ => exact PBF.exn hs _
  | dictClear =>
      refine PBF.bind (ihEs m st args hslot) fun s vs _ hs => ?_
      cases vs with
      | cons _ _ => exact PBF.exn hs _
      | nil =>
          simp only [FrameState.swapAt_world, World.swapAt_heap]
          rcases Heap.get?_swapAt_twin (b := b) hs htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
          · rw [heq]
            cases hget : Heap.get? s.world.heap b with
            | none => exact PBF.unsupported
            | some obj =>
                cases obj with
                | dict es ver =>
                    have hne : pa ≠ b := Heap.ne_slot_of_twin hs htwin hget (by simp)
                    simp only [Heap.update_swapAt_ne (Ne.symm hne)]
                    cases hu : Heap.update s.world.heap b (Obj.dict #[] (ver + 1)) with
                    | none => exact PBF.unsupported
                    | some h' =>
                        exact PBF.okWrite ((Heap.get?_update_ne hu hne).trans hs) _
                | _ => exact PBF.unsupported
          · rw [h1, h2]
            exact PBF.unsupported
  | listAppend =>
      refine PBF.bind (ihEs m st args hslot) fun s vs _ hs => ?_
      cases vs with
      | nil => exact PBF.exn hs _
      | cons v rest =>
          cases rest with
          | cons _ _ => exact PBF.exn hs _
          | nil =>
              simp only [FrameState.swapAt_world, World.swapAt_heap,
                heapAppend_swapAt hs htwin]
              exact PBF.liftMapOk hs fun h' hw => PBF.okWrite (heapAppend_slot hs htwin hw) _
  | listPop =>
      refine PBF.bind (ihEs m st args hslot) fun s vs _ hs => ?_
      cases vs with
      | nil =>
          simp only [FrameState.swapAt_world, World.swapAt_heap, heapPop_swapAt hs htwin]
          refine PBF.liftMapOk hs fun x hw => ?_
          obtain ⟨h', v⟩ := x
          exact PBF.okWrite (heapPop_slot hs htwin hw) _
      | cons i rest =>
          cases rest with
          | cons _ _ => exact PBF.exn hs _
          | nil =>
              -- the arm's own binder shadows `i` until the list match iota-reduces
              simp only []
              cases hai : asInt i with
              | none => exact PBF.exn hs _
              | some n =>
                  simp only [FrameState.swapAt_world, World.swapAt_heap,
                    heapPop_swapAt hs htwin]
                  refine PBF.liftMapOk hs fun x hw => ?_
                  obtain ⟨h', v⟩ := x
                  exact PBF.okWrite (heapPop_slot hs htwin hw) _
  | listInsert =>
      refine PBF.bind (ihEs m st args hslot) fun s vs _ hs => ?_
      cases vs with
      | nil => exact PBF.exn hs _
      | cons i rest =>
          cases rest with
          | nil => exact PBF.exn hs _
          | cons v rest' =>
              cases rest' with
              | cons _ _ => exact PBF.exn hs _
              | nil =>
                  simp only []
                  cases hai : asInt i with
                  | none => exact PBF.exn hs _
                  | some n =>
                      simp only [FrameState.swapAt_world, World.swapAt_heap,
                        heapInsert_swapAt hs htwin]
                      exact PBF.liftMapOk hs fun h' hw =>
                        PBF.okWrite (heapInsert_slot hs htwin hw) _
  | refuse msg => exact PBF.unsupported
  | dangling => exact PBF.unsupported

/-- One statement. The `assign`/`augAssign` arms are where the interpreter
WRITES (subscript store, attribute store, the tuple-target thread), and
each is §Tier C′ over §Tier B; everything else is composition, a pure
plan, or a `locals`-only rebinding — and `locals` ride the swap. -/
theorem pbExecStmt_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBExecStmt pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, -, -, -, -, ihSs, ihWhile, -, ihFor, -, ihForList, -⟩ := ih
  intro m st s hslot
  cases s with
  | ret v sp =>
      cases v with
      | none => simp only [execStmt]; exact PBF.ok hslot _
      | some e =>
          simp only [execStmt]
          exact PBF.bind (ihE m st e hslot) fun s1 v _ hs1 => PBF.ok hs1 _
  | assign targets value sp =>
      simp only [execStmt, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
      cases htl : targets.toList with
      | nil => exact PBF.unsupported
      | cons t rest =>
          cases rest with
          | cons _ _ => cases t <;> exact PBF.unsupported
          | nil =>
              cases t with
              | subscript dE kE sp' =>
                  refine PBF.bind (ihE m st value hslot) fun s1 v _ hs1 => ?_
                  refine PBF.bind (ihE m s1 dE hs1) fun s2 c _ hs2 => ?_
                  refine PBF.bind (ihE m s2 kE hs2) fun s3 k _ hs3 => ?_
                  cases c with
                  | ref b =>
                      simp only [FrameState.swapAt_world, World.swapAt_heap,
                        heapStore_swapAt hs3 htwin]
                      exact PBF.liftMapOk hs3 fun h' hw =>
                        PBF.okWrite (heapStore_slot hs3 htwin hw) _
                  | listV _ => exact PBF.unsupported
                  | _ => exact PBF.exn hs3 _
              | «attribute» recvE attr sp' =>
                  refine PBF.bind (ihE m st value hslot) fun s1 v _ hs1 => ?_
                  refine PBF.bind (ihE m s1 recvE hs1) fun s2 r _ hs2 => ?_
                  cases r with
                  | ref b =>
                      simp only [FrameState.swapAt_world, World.swapAt_heap,
                        heapAttrStore_swapAt hs2 htwin]
                      exact PBF.liftMapOk hs2 fun h' hw =>
                        PBF.okWrite (heapAttrStore_slot hs2 htwin hw) _
                  | _ => exact PBF.exn hs2 _
              | tuple elts sp' =>
                  refine PBF.ite (fun _ => ?_) (fun _ => ?_)
                  · refine PBF.bind (ihE m st value hslot) fun s1 v _ hs1 => ?_
                    have hlift : PBF pa o₀ o
                        (Run.liftRes s1
                          (assignToH s1.world.heap s1.locals (.tuple elts sp') v))
                        (Run.liftRes (s1.swapAt pa o)
                          (assignToH (Heap.swapAt s1.world.heap pa o) s1.locals
                            (.tuple elts sp') v)) := by
                      rw [assignToH_swapAt hs1 htwin]
                      exact PBF.liftRes hs1 _
                    refine PBF.bind hlift fun s2 env' _ hs2 => ?_
                    refine PBF.ok ?_ _
                    exact hs2
                  · refine PBF.bind (ihE m st value hslot) fun s1 v _ hs1 => ?_
                    have hlift : PBF pa o₀ o
                        (Run.liftRes s1 (unpackSeq s1.world.heap elts.size v))
                        (Run.liftRes (s1.swapAt pa o)
                          (unpackSeq (Heap.swapAt s1.world.heap pa o) elts.size v)) := by
                      rw [unpackSeq_swapAt hs1 htwin]
                      exact PBF.liftRes hs1 _
                    refine PBF.bind hlift fun s2 xs _ hs2 => ?_
                    simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                      World.swapAt_heap, (unpackStoreH_swapAt htwin _ _ _ _ hs2).1]
                    refine PBF.liftMapOk hs2 fun x hw => ?_
                    obtain ⟨h', env'⟩ := x
                    refine PBF.ok ?_ _
                    exact (unpackStoreH_swapAt htwin _ _ _ _ hs2).2 _ hw
              | _ =>
                  -- the single-target arm: `assignToH` for every OTHER target
                  -- shape, so the rewrite lands on the goal rather than on a
                  -- named `have` (the arm's target is not in scope here)
                  refine PBF.bind (ihE m st value hslot) fun s1 v _ hs1 => ?_
                  simp only [FrameState.swapAt_world, FrameState.swapAt_locals,
                    World.swapAt_heap, assignToH_swapAt hs1 htwin]
                  refine PBF.bind (PBF.liftRes hs1 _) fun s2 env' _ hs2 => ?_
                  refine PBF.ok ?_ _
                  exact hs2
  | augAssign target op value sp =>
      simp only [execStmt, FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
      cases target with
      | name id sp' =>
          -- the arm's own binder shadows `id` until the target match reduces
          simp only []
          cases hlk : Env.lookup st.locals id with
          | none => exact PBF.exn hslot _
          | some old =>
              cases old with
              | listV _ => exact PBF.unsupported
              | ref _ => exact PBF.unsupported
              | _ =>
                  refine PBF.bind (ihE m st value hslot) fun s1 v _ hs1 => ?_
                  refine PBF.bind (PBF.liftRes hs1 _) fun s2 r _ hs2 => ?_
                  refine PBF.ok ?_ _
                  exact hs2
      | «attribute» recvE attr sp' =>
          refine PBF.bind (ihE m st recvE hslot) fun s1 r _ hs1 => ?_
          cases r with
          | ref b =>
              refine PBF.bind (attrReadResult_pb hs1 htwin m b attr) fun s2 old _ hs2 => ?_
              cases old with
              | listV _ => exact PBF.unsupported
              | ref _ => exact PBF.unsupported
              | _ =>
                  refine PBF.bind (ihE m s2 value hs2) fun s3 v _ hs3 => ?_
                  refine PBF.bind (PBF.liftRes hs3 _) fun s4 res _ hs4 => ?_
                  simp only [FrameState.swapAt_world, World.swapAt_heap,
                    heapAttrStore_swapAt hs4 htwin]
                  exact PBF.liftMapOk hs4 fun h' hw =>
                    PBF.okWrite (heapAttrStore_slot hs4 htwin hw) _
          | _ => exact PBF.exn hs1 _
      | _ => exact PBF.unsupported
  | whileLoop test body orelse sp =>
      simp only [execStmt]
      exact ihWhile m st test body.toList orelse.toList hslot
  | forStmt target iter body orelse sp =>
      simp only [execStmt]
      cases horelse : orelse.toList with
      | cons _ _ => exact PBF.unsupported
      | nil =>
          refine PBF.bind (ihE m st iter hslot) fun s1 it _ hs1 => ?_
          cases it with
          | listV xs => exact ihFor m s1 target xs.toList body.toList hs1
          | tuple xs => exact ihFor m s1 target xs.toList body.toList hs1
          | ntuple _ _ xs => exact ihFor m s1 target xs.toList body.toList hs1
          | str sv => exact ihFor m s1 target (strCharVals sv) body.toList hs1
          | rangeV lo hi step =>
              refine PBF.bind (PBF.liftRes hs1 _) fun s2 xs _ hs2 => ?_
              exact ihFor m s2 target xs body.toList hs2
          | ref b => exact ihForList m s1 target b 0 body.toList hs1
          | _ => exact PBF.exn hs1 _
  | ifStmt test body orelse sp =>
      simp only [execStmt]
      refine PBF.bind (ihE m st test hslot) fun s1 t _ hs1 => ?_
      have hlift : PBF pa o₀ o (Run.liftRes s1 (truthyH s1.world.heap t))
          (Run.liftRes (s1.swapAt pa o) (truthyH (Heap.swapAt s1.world.heap pa o) t)) := by
        rw [truthyH_swapAt hs1 htwin]
        exact PBF.liftRes hs1 _
      refine PBF.bind hlift fun s2 b _ hs2 => ?_
      exact PBF.ite (fun _ => ihSs m s2 body.toList hs2) (fun _ => ihSs m s2 orelse.toList hs2)
  | exprStmt e sp =>
      simp only [execStmt]
      exact PBF.bind (ihE m st e hslot) fun s1 v _ hs1 => PBF.ok hs1 _
  | yieldStmt _ _ => simp only [execStmt]; exact PBF.unsupported
  | yieldFromStmt _ _ => simp only [execStmt]; exact PBF.unsupported
  | defStmt name params argsOk localsOk hasGlobal isGenerator body captures sp =>
      -- H7 cells: the def ALLOCATES this frame's cells first, and that is
      -- a pure append — it commutes with the swap (`allocCells_swapAt`)
      simp only [execStmt]
      rw [allocCells_swapAt _ _ (Heap.lt_size_of_get? hslot)]
      generalize hst : allocCells st captures.toList = st'
      have hslot' : Heap.get? st'.world.heap pa = some o₀ := by
        subst hst; exact allocCells_get? _ _ hslot
      simp only [FrameState.swapAt_world, FrameState.swapAt_locals, World.swapAt_heap]
      cases hcap : capturesSnapshot st'.locals captures.toList with
      | none => exact PBF.unsupported
      | some cap =>
          simp only [Heap.swapAt_push (Heap.lt_size_of_get? hslot'), Heap.size_swapAt]
          refine PBF.ok ?_ _
          exact Heap.get?_push_of_get? _ hslot'
  | raiseStmt exc cause sp =>
      simp only [execStmt, FrameState.swapAt_world, FrameState.swapAt_locals,
        World.swapAt_globals]
      cases cause with
      | some _ => exact PBF.unsupported
      | none =>
          cases exc with
          | none => exact PBF.unsupported
          | some e =>
              cases e with
              | name id sp' =>
                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                  cases findClass m id with
                  | none => exact PBF.unsupported
                  | some cic =>
                      obtain ⟨ci, c⟩ := cic
                      exact PBF.ite (fun _ => PBF.exn hslot _) (fun _ => PBF.unsupported)
              | _ => exact PBF.unsupported
  | assertStmt test msg sp =>
      simp only [execStmt]
      refine PBF.bind (ihE m st test hslot) fun s1 t _ hs1 => ?_
      have hlift : PBF pa o₀ o (Run.liftRes s1 (truthyH s1.world.heap t))
          (Run.liftRes (s1.swapAt pa o) (truthyH (Heap.swapAt s1.world.heap pa o) t)) := by
        rw [truthyH_swapAt hs1 htwin]
        exact PBF.liftRes hs1 _
      refine PBF.bind hlift fun s2 b _ hs2 => ?_
      refine PBF.ite (fun _ => PBF.ok hs2 _) fun _ => ?_
      cases msg with
      | none => exact PBF.exn hs2 _
      | some e =>
          refine PBF.bind (ihE m s2 e hs2) fun s3 v _ hs3 => ?_
          simp only [FrameState.swapAt_world, World.swapAt_heap, printOne_swapAt hs3 htwin]
          cases printOne s3.world.heap v with
          | some rendered => exact PBF.exn hs3 _
          | none => exact PBF.unsupported
  | tryStmt body excName handler tryUnsupported sp =>
      simp only [execStmt, FrameState.swapAt_world, FrameState.swapAt_locals,
        World.swapAt_globals]
      cases tryUnsupported with
      | some reason => exact PBF.unsupported
      | none =>
          refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
          cases findClass m excName with
          | none =>
              refine PBF.ite (fun _ => ?_) (fun _ => PBF.unsupported)
              cases hrun : execStmts m fuel st body.toList with
              | ok st' flow =>
                  obtain ⟨hslot', hy⟩ := (ihSs m st body.toList hslot).1 st' flow hrun
                  rw [hy]
                  exact PBF.ok hslot' _
              | exn st' e =>
                  obtain ⟨hslot', hy⟩ := (ihSs m st body.toList hslot).2 st' e hrun
                  rw [hy]
                  simp only []
                  cases e with
                  | importError _ => exact ihSs m st' handler.toList hslot'
                  | _ => exact PBF.exn hslot' _
              | timeout => exact PBF.timeout
              | unsupported msg => exact PBF.unsupported
          | some cic =>
              obtain ⟨ci, c⟩ := cic
              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
              cases hrun : execStmts m fuel st body.toList with
              | ok st' flow =>
                  obtain ⟨hslot', hy⟩ := (ihSs m st body.toList hslot).1 st' flow hrun
                  rw [hy]
                  exact PBF.ok hslot' _
              | exn st' e =>
                  obtain ⟨hslot', hy⟩ := (ihSs m st body.toList hslot).2 st' e hrun
                  rw [hy]
                  simp only []
                  cases e with
                  | user cid cname =>
                      exact PBF.ite (fun _ => ihSs m st' handler.toList hslot')
                        (fun _ => PBF.exn hslot' _)
                  | _ => exact PBF.exn hslot' _
              | timeout => exact PBF.timeout
              | unsupported msg => exact PBF.unsupported
  | delStmt names sp =>
      simp only [execStmt, FrameState.swapAt_locals]
      cases hdn : delNames st.locals names.toList with
      | mk env res =>
          cases res with
          | none => refine PBF.ok ?_ _; exact hslot
          | some n => exact PBF.unsupported
  | importFrom mod names star sp => simp only [execStmt]; exact PBF.exn hslot _
  | pass sp => simp only [execStmt]; exact PBF.ok hslot _
  | brk sp => simp only [execStmt]; exact PBF.ok hslot _
  | cont sp => simp only [execStmt]; exact PBF.ok hslot _
  | unsupported pyKind text sp => simp only [execStmt]; exact PBF.unsupported

/-- **The block's largest member**, 1047 of its 1976 lines, and the arm
that reaches every §Tier B equation. The geometry is one case per `Expr`
constructor; `.call` carries the builtin tier (its own `fname` chain), the
class/namedtuple constructors, the closure dispatch and the H6 keyword
tier. Nothing in it is a new idea: displays and constructors ALLOCATE
(`PBF.pushRef`), `sorted` allocates through a `map`-shaped equation
(§Tier C′), every other leaf is a §Tier B equation under `PBF.liftRes` or
a member of the block under the IH. -/
theorem pbEvalExpr_succ (htwin : PayloadTwin o₀ o) (ih : PBAll pa o₀ o fuel) :
    PBEvalExpr pa o₀ o (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihBool, ihCmp, -, -, -, ihIn, -, ihItems, -, ihAttrCall,
    ihIter, -, -, ihDrain, ihAny, ihClosure⟩ := ih
  intro m st e hslot
  cases e with
  | constant c sp => simp only [evalExpr]; exact PBF.ok hslot _
  | namedExpr id v sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st v hslot) fun s r _ hs => ?_
      refine PBF.ok ?_ _
      exact hs
  | name id sp =>
      simp only [evalExpr, FrameState.swapAt_locals, FrameState.swapAt_world,
        World.swapAt_globals]
      cases Env.lookup st.locals id with
      | some v => exact PBF.ok hslot _
      | none =>
          cases lookupG (moduleGlobals m).1 id with
          | some ov =>
              cases ov with
              | some v => exact PBF.ok hslot _
              | none =>
                  cases Env.lookup st.world.globals id with
                  | some v => exact PBF.ok hslot _
                  | none => exact PBF.unsupported
          | none =>
              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
              cases Env.lookup st.world.globals id with
              | some v => exact PBF.ok hslot _
              | none =>
                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                  exact PBF.ite (fun _ => PBF.exn hslot _) (fun _ => PBF.unsupported)
  | binOp l op r sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st l hslot) fun s1 a _ hs1 => ?_
      refine PBF.bind (ihE m s1 r hs1) fun s2 b _ hs2 => ?_
      exact PBF.liftRes hs2 _
  | unaryOp op operand sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st operand hslot) fun s1 v _ hs1 => ?_
      simp only [FrameState.swapAt_world, World.swapAt_heap, evalUnaryOpH_swapAt hs1 htwin]
      exact PBF.liftRes hs1 _
  | boolOp op values sp =>
      simp only [evalExpr]
      cases values.toList with
      | nil => exact PBF.unsupported
      | cons e' es => exact ihBool m st op e' es hslot
  | compare l ops comparators sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st l hslot) fun s1 a _ hs1 => ?_
      exact ihCmp m s1 a ops.toList comparators.toList hs1
  | list elts sp =>
      simp only [evalExpr]
      refine PBF.bind (ihEs m st elts.toList hslot) fun s1 vs _ hs1 => ?_
      exact PBF.pushRef hs1 _
  | tuple elts sp =>
      simp only [evalExpr]
      exact PBF.bind (ihEs m st elts.toList hslot) fun s1 vs _ hs1 => PBF.ok hs1 _
  | subscript v idx sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st v hslot) fun s1 c _ hs1 => ?_
      refine PBF.bind (ihE m s1 idx hs1) fun s2 i _ hs2 => ?_
      simp only [FrameState.swapAt_world, World.swapAt_heap, indexValH_swapAt hs2 htwin]
      exact PBF.liftRes hs2 _
  | dict keys values sp =>
      simp only [evalExpr]
      refine PBF.bind (ihItems m st keys.toList values.toList hslot) fun s1 items _ hs1 => ?_
      simp only [FrameState.swapAt_world, World.swapAt_heap, dictBuild_swapAt hs1 htwin]
      refine PBF.bind (PBF.liftRes hs1 _) fun s2 entries _ hs2 => ?_
      exact PBF.pushRef hs2 _
  | «attribute» recv attr sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st recv hslot) fun s1 r _ hs1 => ?_
      cases r with
      | ref b => exact attrReadResult_pb hs1 htwin m b attr
      | ntuple tn fields xs => exact PBF.liftRes hs1 _
      | _ => exact PBF.unsupported
  | ifExp tE bE oE sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st tE hslot) fun s1 tv _ hs1 => ?_
      simp only [FrameState.swapAt_world, World.swapAt_heap, truthyH_swapAt hs1 htwin]
      refine PBF.bind (PBF.liftRes hs1 _) fun s2 cond _ hs2 => ?_
      exact PBF.ite (fun _ => ihE m s2 bE hs2) (fun _ => ihE m s2 oE hs2)
  | slice v lE uE stp sp =>
      simp only [evalExpr]
      refine PBF.bind (ihE m st v hslot) fun s1 cv _ hs1 => ?_
      refine PBF.bind (ihE m s1 lE hs1) fun s2 lv _ hs2 => ?_
      refine PBF.bind (ihE m s2 uE hs2) fun s3 uv _ hs3 => ?_
      refine PBF.bind (ihE m s3 stp hs3) fun s4 sv _ hs4 => ?_
      exact PBF.liftRes hs4 _
  | genExp elt target iter ifs sp => simp only [evalExpr]; exact PBF.unsupported
  | unsupported pyKind text sp => simp only [evalExpr]; exact PBF.unsupported
  | call f args kwargs callUnsupported sp =>
      simp only [evalExpr, FrameState.swapAt_world, FrameState.swapAt_locals,
        World.swapAt_heap, World.swapAt_globals, World.swapAt_clock,
        isClockCall_swapAt]
      cases callUnsupported with
      | some reason => exact PBF.unsupported
      | none =>
          refine PBF.ite (fun _ => ?_) fun _ => ?_
          -- ===== POSITIONAL =====
          · cases f with
            | name fname sp' =>
                simp only []
                cases Env.lookup st.locals fname with
                | some v =>
                    cases v with
                    | ref b =>
                        refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                        refine PBF.ite (fun _ => PBF.exn hs1 _) fun _ => ?_
                        rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                          heq | ⟨_, _, _, _, _, h1, h2⟩
                        · simp only [FrameState.swapAt_world, World.swapAt_heap, heq]
                          cases hget : Heap.get? s1.world.heap b with
                          | none => exact PBF.exn hs1 _
                          | some obj =>
                              cases obj with
                              | cell cv => exact PBF.unsupported
                              | closure nm ps ao lo hg ig bd cap =>
                                  dsimp only
                                  rw [cellsFor_swapAt hs1 htwin]
                                  refine PBF.bind (PBF.liftRes hs1 _) fun s cap' _ hs => ?_
                                  exact PBW.withLocals
                                    (ihClosure m _ nm ps ao lo ig bd cap' vs.toArray hs)
                              | _ => exact PBF.exn hs1 _
                        · simp only [FrameState.swapAt_world, World.swapAt_heap, h1, h2]
                          exact PBF.exn hs1 _
                    | _ =>
                        exact PBF.bind (ihEs m st args.toList hslot)
                          fun s1 vs _ hs1 => PBF.exn hs1 _
                | none =>
                    cases lookupG (moduleGlobals m).1 fname with
                    | some ov =>
                        cases ov with
                        | some gv =>
                            cases gv <;>
                              exact PBF.bind (ihEs m st args.toList hslot)
                                fun s1 vs _ hs1 => PBF.exn hs1 _
                        | none =>
                            cases Env.lookup st.world.globals fname with
                            | some gv =>
                                cases gv with
                                | ref b =>
                                    refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    refine PBF.ite (fun _ => PBF.exn hs1 _) fun _ => ?_
                                    rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                      heq | ⟨_, _, _, _, _, h1, h2⟩
                                    · simp only [FrameState.swapAt_world, World.swapAt_heap, heq]
                                      cases hget : Heap.get? s1.world.heap b with
                                      | none => exact PBF.exn hs1 _
                                      | some obj =>
                                          cases obj with
                                          | cell cv => exact PBF.unsupported
                                          | closure nm ps ao lo hg ig bd cap =>
                                              dsimp only
                                              rw [cellsFor_swapAt hs1 htwin]
                                              refine PBF.bind (PBF.liftRes hs1 _)
                                                fun s cap' _ hs => ?_
                                              exact PBW.withLocals (ihClosure m _ nm ps ao
                                                lo ig bd cap' vs.toArray hs)
                                          | _ => exact PBF.exn hs1 _
                                    · simp only [FrameState.swapAt_world, World.swapAt_heap, h1, h2]
                                      exact PBF.exn hs1 _
                                | _ =>
                                    exact PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => PBF.exn hs1 _
                            | none => exact PBF.unsupported
                    | none =>
                        refine PBF.ite (fun _ => ?_) fun _ => ?_
                        -- a module `def`
                        · refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                          refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                          exact PBW.withLocals (ihIn m s1.world fname vs.toArray hs1)
                        · cases findClass m fname with
                          | some cic =>
                              obtain ⟨ci, c⟩ := cic
                              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                              refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                              cases c.ntBase with
                              | some nt =>
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  refine PBF.bind (ihEs m st args.toList hslot)
                                    fun s1 vs _ hs1 => ?_
                                  exact PBF.ite (fun _ => PBF.ok hs1 _) (fun _ => PBF.exn hs1 _)
                              | none =>
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  refine PBF.bind (ihEs m st args.toList hslot)
                                    fun s1 vs _ hs1 => ?_
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- `__init__` runs in the world the instance was allocated in
                                  · simp only [FrameState.swapAt_world, World.swapAt_heap,
                                      Heap.swapAt_push (Heap.lt_size_of_get? hs1),
                                      Heap.size_swapAt]
                                    refine PBF.bind (PBW.withLocals (ihIn m
                                      { s1.world with
                                          heap := s1.world.heap.push (.instance ci #[]) }
                                      (fname ++ ".__init__")
                                      ((RVal.ref s1.world.heap.size :: vs).toArray)
                                      (Heap.get?_push_of_get? _ hs1))) fun s2 r _ hs2 => ?_
                                    cases r with
                                    | none => exact PBF.ok hs2 _
                                    | _ => exact PBF.exn hs2 _
                                  · cases vs with
                                    | nil => exact PBF.pushRef hs1 _
                                    | cons _ _ => exact PBF.exn hs1 _
                          | none =>
                              cases findNamedTuple m fname with
                              | some nt =>
                                  refine PBF.bind (ihEs m st args.toList hslot)
                                    fun s1 vs _ hs1 => ?_
                                  exact PBF.ite (fun _ => PBF.ok hs1 _) (fun _ => PBF.exn hs1 _)
                              | none =>
                                  -- ===== the builtin chain =====
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- len
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only [FrameState.swapAt_world, World.swapAt_heap,
                                              lenValH_swapAt hs1 htwin]
                                            exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- sorted
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only []
                                            cases v with
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none =>
                                                      simp only [sortedValH_swapAt hs1 htwin]
                                                      refine PBF.liftMapOk hs1 fun x hw => ?_
                                                      obtain ⟨h', r⟩ := x
                                                      exact PBF.okWrite
                                                        (sortedValH_slot hs1 hw) _
                                                  | some obj =>
                                                      cases obj with
                                                      | generator qn l cnt stt =>
                                                          refine PBF.bind (PBW.withLocals
                                                            (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          refine PBF.bind (PBF.liftRes hs2 _)
                                                            fun s3 srt _ hs3 => ?_
                                                          exact PBF.pushRef hs3 _
                                                      | _ =>
                                                          simp only [sortedValH_swapAt hs1 htwin]
                                                          refine PBF.liftMapOk hs1 fun x hw => ?_
                                                          obtain ⟨h', r⟩ := x
                                                          exact PBF.okWrite
                                                            (sortedValH_slot hs1 hw) _
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  refine PBF.bind (PBW.withLocals
                                                    (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  refine PBF.bind (PBF.liftRes hs2 _)
                                                    fun s3 srt _ hs3 => ?_
                                                  exact PBF.pushRef hs3 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, sortedValH_swapAt hs1 htwin]
                                                refine PBF.liftMapOk hs1 fun x hw => ?_
                                                obtain ⟨h', r⟩ := x
                                                exact PBF.okWrite (sortedValH_slot hs1 hw) _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- max
                                  · refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil =>
                                        simp only [FrameState.swapAt_world, World.swapAt_heap,
                                          extremumValH_swapAt hs1 htwin]
                                        exact PBF.liftRes hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ =>
                                            simp only [FrameState.swapAt_world, World.swapAt_heap,
                                              extremumValH_swapAt hs1 htwin]
                                            exact PBF.liftRes hs1 _
                                        | nil =>
                                            cases v with
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world, World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none =>
                                                      simp only [extremumValH_swapAt hs1 htwin]
                                                      exact PBF.liftRes hs1 _
                                                  | some obj =>
                                                      cases obj with
                                                      | generator qn l cnt stt =>
                                                          refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                                          refine PBF.bind (PBW.withLocals (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          exact PBF.liftRes hs2 _
                                                      | _ =>
                                                          simp only [extremumValH_swapAt hs1 htwin]
                                                          exact PBF.liftRes hs1 _
                                                · simp only [FrameState.swapAt_world, World.swapAt_heap, h1, h2]
                                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                                  refine PBF.bind (PBW.withLocals (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  exact PBF.liftRes hs2 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world, World.swapAt_heap,
                                                  extremumValH_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- min
                                  · refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil =>
                                        simp only [FrameState.swapAt_world, World.swapAt_heap,
                                          extremumValH_swapAt hs1 htwin]
                                        exact PBF.liftRes hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ =>
                                            simp only [FrameState.swapAt_world, World.swapAt_heap,
                                              extremumValH_swapAt hs1 htwin]
                                            exact PBF.liftRes hs1 _
                                        | nil =>
                                            cases v with
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world, World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none =>
                                                      simp only [extremumValH_swapAt hs1 htwin]
                                                      exact PBF.liftRes hs1 _
                                                  | some obj =>
                                                      cases obj with
                                                      | generator qn l cnt stt =>
                                                          refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                                          refine PBF.bind (PBW.withLocals (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          exact PBF.liftRes hs2 _
                                                      | _ =>
                                                          simp only [extremumValH_swapAt hs1 htwin]
                                                          exact PBF.liftRes hs1 _
                                                · simp only [FrameState.swapAt_world, World.swapAt_heap, h1, h2]
                                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                                  refine PBF.bind (PBW.withLocals (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  exact PBF.liftRes hs2 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world, World.swapAt_heap,
                                                  extremumValH_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- any / all
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only []
                                            cases v with
                                            | str t =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, anyAllScan_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                            | tuple xs =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, anyAllScan_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                            | ntuple _ _ xs =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, anyAllScan_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                            | listV xs =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, anyAllScan_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                            | rangeV lo hi step =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, anyAllScan_swapAt hs1 htwin]
                                                exact PBF.liftRes hs1 _
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none => exact PBF.unsupported
                                                  | some obj =>
                                                      cases obj with
                                                      | list xs =>
                                                          simp only [anyAllScan_swapAt hs1 htwin]
                                                          exact PBF.liftRes hs1 _
                                                      | dict es sv =>
                                                          simp only [anyAllScan_swapAt hs1 htwin]
                                                          exact PBF.liftRes hs1 _
                                                      | generator qn l cnt stt =>
                                                          refine PBF.bind (PBW.withLocals
                                                            (ihAny m s1.world b _ hs1))
                                                            fun s2 bb _ hs2 => ?_
                                                          exact PBF.ok hs2 _
                                                      | «instance» ci attrs => exact PBF.exn hs1 _
                                                      | closure _ _ _ _ _ _ _ _ =>
                                                          exact PBF.exn hs1 _
                                                      | _ => exact PBF.unsupported
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  refine PBF.bind (PBW.withLocals
                                                    (ihAny m s1.world b _ hs1))
                                                    fun s2 bb _ hs2 => ?_
                                                  exact PBF.ok hs2 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap]
                                                exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- set
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.pushRef hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only []
                                            cases v with
                                            | str t =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, setDedup_swapAt hs1 htwin]
                                                refine PBF.bind (PBF.liftRes hs1 _)
                                                  fun s2 es _ hs2 => ?_
                                                exact PBF.pushRef hs2 _
                                            | tuple xs =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, setDedup_swapAt hs1 htwin]
                                                refine PBF.bind (PBF.liftRes hs1 _)
                                                  fun s2 es _ hs2 => ?_
                                                exact PBF.pushRef hs2 _
                                            | ntuple _ _ xs =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, setDedup_swapAt hs1 htwin]
                                                refine PBF.bind (PBF.liftRes hs1 _)
                                                  fun s2 es _ hs2 => ?_
                                                exact PBF.pushRef hs2 _
                                            | listV xs =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, setDedup_swapAt hs1 htwin]
                                                refine PBF.bind (PBF.liftRes hs1 _)
                                                  fun s2 es _ hs2 => ?_
                                                exact PBF.pushRef hs2 _
                                            | rangeV lo hi step =>
                                                refine PBF.bind (PBF.liftRes hs1 _)
                                                  fun s2 xs _ hs2 => ?_
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap, setDedup_swapAt hs2 htwin]
                                                refine PBF.bind (PBF.liftRes hs2 _)
                                                  fun s3 es _ hs3 => ?_
                                                exact PBF.pushRef hs3 _
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none => exact PBF.unsupported
                                                  | some obj =>
                                                      cases obj with
                                                      | list xs =>
                                                          simp only [setDedup_swapAt hs1 htwin]
                                                          refine PBF.bind (PBF.liftRes hs1 _)
                                                            fun s2 es _ hs2 => ?_
                                                          exact PBF.pushRef hs2 _
                                                      | dict es sv =>
                                                          simp only [setDedup_swapAt hs1 htwin]
                                                          refine PBF.bind (PBF.liftRes hs1 _)
                                                            fun s2 es _ hs2 => ?_
                                                          exact PBF.pushRef hs2 _
                                                      | pyset xs => exact PBF.pushRef hs1 _
                                                      | generator qn l cnt stt =>
                                                          refine PBF.bind (PBW.withLocals
                                                            (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          simp only [FrameState.swapAt_world,
                                                            World.swapAt_heap,
                                                            setDedup_swapAt hs2 htwin]
                                                          refine PBF.bind (PBF.liftRes hs2 _)
                                                            fun s3 es _ hs3 => ?_
                                                          exact PBF.pushRef hs3 _
                                                      | «instance» ci attrs => exact PBF.exn hs1 _
                                                      | closure _ _ _ _ _ _ _ _ =>
                                                          exact PBF.exn hs1 _
                                                      | _ => exact PBF.unsupported
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  refine PBF.bind (PBW.withLocals
                                                    (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, setDedup_swapAt hs2 htwin]
                                                  refine PBF.bind (PBF.liftRes hs2 _)
                                                    fun s3 es _ hs3 => ?_
                                                  exact PBF.pushRef hs3 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap]
                                                exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- abs
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil => exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- int
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.ok hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.unsupported
                                        | nil => exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- sum
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases sumArgs vs with
                                    | none => exact PBF.exn hs1 _
                                    | some vstart =>
                                        obtain ⟨v, start⟩ := vstart
                                        cases start with
                                        | str _ => exact PBF.exn hs1 _
                                        | _ =>
                                            simp only []
                                            cases v with
                                            | tuple xs => exact PBF.liftRes hs1 _
                                            | ntuple _ _ xs => exact PBF.liftRes hs1 _
                                            | listV xs => exact PBF.liftRes hs1 _
                                            | str t => exact PBF.liftRes hs1 _
                                            | rangeV lo hi step => exact PBF.liftRes hs1 _
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none => exact PBF.unsupported
                                                  | some obj =>
                                                      cases obj with
                                                      | list xs => exact PBF.liftRes hs1 _
                                                      -- §L53 rung 3b: the KEYS, at a slot the twin cannot be
                                                      | dict es sv => exact PBF.liftRes hs1 _
                                                      | generator qn l cnt stt =>
                                                          refine PBF.ite
                                                            (fun _ => PBF.unsupported) fun _ => ?_
                                                          refine PBF.bind (PBW.withLocals
                                                            (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          exact PBF.liftRes hs2 _
                                                      | «instance» ci attrs => exact PBF.exn hs1 _
                                                      | closure _ _ _ _ _ _ _ _ =>
                                                          exact PBF.exn hs1 _
                                                      | _ => exact PBF.unsupported
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  refine PBF.ite
                                                    (fun _ => PBF.unsupported) fun _ => ?_
                                                  refine PBF.bind (PBW.withLocals
                                                    (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  exact PBF.liftRes hs2 _
                                            | _ => exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- tuple
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.ok hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only []
                                            cases v with
                                            | str t => exact PBF.ok hs1 _
                                            | tuple xs => exact PBF.ok hs1 _
                                            | ntuple _ _ xs => exact PBF.ok hs1 _
                                            | listV xs => exact PBF.ok hs1 _
                                            | rangeV lo hi step => exact PBF.liftRes hs1 _
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none => exact PBF.unsupported
                                                  | some obj =>
                                                      cases obj with
                                                      | list xs => exact PBF.ok hs1 _
                                                      -- §L53 rung 3b: the KEYS, at a slot the twin cannot be
                                                      | dict es sv => exact PBF.ok hs1 _
                                                      | generator qn l cnt stt =>
                                                          refine PBF.ite
                                                            (fun _ => PBF.unsupported) fun _ => ?_
                                                          refine PBF.bind (PBW.withLocals
                                                            (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          exact PBF.ok hs2 _
                                                      | «instance» ci attrs => exact PBF.exn hs1 _
                                                      | closure _ _ _ _ _ _ _ _ =>
                                                          exact PBF.exn hs1 _
                                                      | _ => exact PBF.unsupported
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  refine PBF.ite
                                                    (fun _ => PBF.unsupported) fun _ => ?_
                                                  refine PBF.bind (PBW.withLocals
                                                    (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  exact PBF.ok hs2 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap]
                                                exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- list
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.allocList hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only []
                                            cases v with
                                            | str t => exact PBF.allocList hs1 _
                                            | tuple xs => exact PBF.allocList hs1 _
                                            | ntuple _ _ xs => exact PBF.allocList hs1 _
                                            | listV xs => exact PBF.allocList hs1 _
                                            | rangeV lo hi step =>
                                                refine PBF.bind (PBF.liftRes hs1 _)
                                                  fun s2 xs _ hs2 => ?_
                                                exact PBF.allocList hs2 _
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none => exact PBF.unsupported
                                                  | some obj =>
                                                      cases obj with
                                                      | list xs => exact PBF.allocList hs1 _
                                                      -- §L53 rung 3b: the KEYS, at a slot the twin cannot be
                                                      | dict es sv => exact PBF.allocList hs1 _
                                                      | generator qn l cnt stt =>
                                                          refine PBF.bind (PBW.withLocals
                                                            (ihDrain m s1.world b hs1))
                                                            fun s2 vals _ hs2 => ?_
                                                          exact PBF.allocList hs2 _
                                                      | «instance» ci attrs => exact PBF.exn hs1 _
                                                      | closure _ _ _ _ _ _ _ _ =>
                                                          exact PBF.exn hs1 _
                                                      | _ => exact PBF.unsupported
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  refine PBF.bind (PBW.withLocals
                                                    (ihDrain m s1.world b hs1))
                                                    fun s2 vals _ hs2 => ?_
                                                  exact PBF.allocList hs2 _
                                            | _ =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap]
                                                exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- dict
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.allocDict hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil =>
                                            simp only []
                                            cases v with
                                            | ref b =>
                                                rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                                  heq | ⟨_, _, _, _, _, h1, h2⟩
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, heq]
                                                  cases hget : Heap.get? s1.world.heap b with
                                                  | none => exact PBF.unsupported
                                                  | some obj =>
                                                      cases obj with
                                                      | dict entries ver =>
                                                          exact PBF.allocDict hs1 _
                                                      | pyset xs => exact PBF.exn hs1 _
                                                      | «instance» ci attrs => exact PBF.exn hs1 _
                                                      | closure _ _ _ _ _ _ _ _ =>
                                                          exact PBF.exn hs1 _
                                                      | _ => exact PBF.unsupported
                                                · simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, h1, h2]
                                                  exact PBF.unsupported
                                            | listV _ => exact PBF.unsupported
                                            | _ =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap]
                                                exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- range
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    simp only [FrameState.swapAt_world, World.swapAt_heap,
                                      rangeMake_swapAt hs1 htwin]
                                    exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- enumerate
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        simp only []
                                        cases enumStart rest with
                                        | none =>
                                            cases rest with
                                            | nil =>
                                                simp only [FrameState.swapAt_world,
                                                  World.swapAt_heap]
                                                exact PBF.exn hs1 _
                                            | cons bad rest' =>
                                                cases rest' with
                                                | nil =>
                                                    simp only [FrameState.swapAt_world,
                                                      World.swapAt_heap,
                                                      RVal.typeNameH_swapAt hs1 htwin]
                                                    exact PBF.exn hs1 _
                                                | cons _ _ =>
                                                    simp only [FrameState.swapAt_world,
                                                      World.swapAt_heap]
                                                    exact PBF.exn hs1 _
                                        | some i0 =>
                                            simp only [FrameState.swapAt_world, World.swapAt_heap,
                                              enumFrame_swapAt hs1 htwin]
                                            cases enumFrame s1.world.heap i0 v with
                                            | ok fr => exact PBF.pushRef hs1 _
                                            | exn e => exact PBF.exn hs1 _
                                            | timeout => exact PBF.timeout
                                            | unsupported msg => exact PBF.unsupported
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- count
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases countArgs vs with
                                    | none => exact PBF.exn hs1 _
                                    | some sst => exact PBF.pushRef hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- next
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil =>
                                        simp only [FrameState.swapAt_world, World.swapAt_heap]
                                        exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases v with
                                        | ref b =>
                                            cases rest with
                                            | nil =>
                                                refine PBF.bind (PBW.withLocals
                                                  (ihIter m s1.world b hs1)) fun s2 r _ hs2 => ?_
                                                cases r with
                                                | some vv => exact PBF.ok hs2 _
                                                | none => exact PBF.exn hs2 _
                                            | cons d rest' =>
                                                cases rest' with
                                                | nil =>
                                                    refine PBF.bind (PBW.withLocals
                                                      (ihIter m s1.world b hs1))
                                                      fun s2 r _ hs2 => ?_
                                                    cases r with
                                                    | some vv => exact PBF.ok hs2 _
                                                    | none => exact PBF.ok hs2 _
                                                | cons _ _ =>
                                                    simp only [FrameState.swapAt_world,
                                                      World.swapAt_heap,
                                                      RVal.typeNameH_swapAt hs1 htwin]
                                                    exact PBF.exn hs1 _
                                        | _ =>
                                            simp only [FrameState.swapAt_world, World.swapAt_heap,
                                              RVal.typeNameH_swapAt hs1 htwin]
                                            exact PBF.exn hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- ord
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil => exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- chr
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.exn hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.exn hs1 _
                                        | nil => exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- str
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    cases vs with
                                    | nil => exact PBF.ok hs1 _
                                    | cons v rest =>
                                        cases rest with
                                        | cons _ _ => exact PBF.unsupported
                                        | nil =>
                                            simp only [FrameState.swapAt_world, World.swapAt_heap,
                                              strOfValH_swapAt hs1 htwin]
                                            exact PBF.liftRes hs1 _
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  -- input
                                  refine PBF.ite (fun _ => ?_) fun _ => ?_
                                  -- print
                                  · refine PBF.bind (ihEs m st args.toList hslot)
                                      fun s1 vs _ hs1 => ?_
                                    simp only [FrameState.swapAt_world, World.swapAt_heap,
                                      World.swapAt_stdout, strOfArgs_swapAt hs1 htwin]
                                    cases strOfArgs s1.world.heap vs with
                                    | some line => refine PBF.ok ?_ _; exact hs1
                                    | none => exact PBF.unsupported
                                  refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                  -- isModuleDunder
                                  cases Env.lookup st.world.globals fname with
                                  | some gv =>
                                      cases gv with
                                      | ref b =>
                                          refine PBF.bind (ihEs m st args.toList hslot)
                                            fun s1 vs _ hs1 => ?_
                                          refine PBF.ite (fun _ => PBF.exn hs1 _) fun _ => ?_
                                          rcases Heap.get?_swapAt_twin (b := b) hs1 htwin with
                                            heq | ⟨_, _, _, _, _, h1, h2⟩
                                          · simp only [FrameState.swapAt_world,
                                              World.swapAt_heap, heq]
                                            cases hget : Heap.get? s1.world.heap b with
                                            | none => exact PBF.exn hs1 _
                                            | some obj =>
                                                cases obj with
                                                | cell cv => exact PBF.unsupported
                                                | closure nm ps ao lo hg ig bd cap =>
                                                    dsimp only
                                                    rw [cellsFor_swapAt hs1 htwin]
                                                    refine PBF.bind (PBF.liftRes hs1 _)
                                                      fun s cap' _ hs => ?_
                                                    exact PBW.withLocals (ihClosure m _ nm
                                                      ps ao lo ig bd cap' vs.toArray hs)
                                                | _ => exact PBF.exn hs1 _
                                          · simp only [FrameState.swapAt_world,
                                              World.swapAt_heap, h1, h2]
                                            exact PBF.exn hs1 _
                                      | _ =>
                                          exact PBF.bind (ihEs m st args.toList hslot)
                                            fun s1 vs _ hs1 => PBF.exn hs1 _
                                  | none =>
                                      refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                      exact PBF.ite (fun _ => PBF.exn hslot _)
                                        (fun _ => PBF.unsupported)
            | «attribute» recv attr sp' =>
                refine PBF.ite (fun _ => ?_) fun _ => ?_
                -- the trace clock
                · cases args.toList with
                  | cons _ _ => exact PBF.unsupported
                  | nil =>
                      cases st.world.clock with
                      | nil => exact PBF.unsupported
                      | cons t ts => refine PBF.ok ?_ _; exact hslot
                · refine PBF.bind (ihE m st recv hslot) fun s1 r _ hs1 => ?_
                  cases r with
                  | ref b => exact ihAttrCall m s1 b attr args.toList hs1
                  | ntuple tn fs xs =>
                      simp only []
                      cases ntupleCallPlan m tn fs attr with
                      | instMethod qname =>
                          refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                          exact PBW.withLocals (ihIn m s2.world qname _ hs2)
                      | attrMissing => exact PBF.exn hs1 _
                      | _ => exact PBF.unsupported
                  | str sv =>
                      simp only []
                      cases strCallPlan attr with
                      | refuse msg => exact PBF.unsupported
                      | swapcase =>
                          refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                          cases vs with
                          | nil => exact PBF.liftRes hs2 _
                          | cons _ _ => exact PBF.exn hs2 _
                      | isupper =>
                          refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                          cases vs with
                          | nil => exact PBF.liftRes hs2 _
                          | cons _ _ => exact PBF.exn hs2 _
                      | islower =>
                          refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                          cases vs with
                          | nil => exact PBF.liftRes hs2 _
                          | cons _ _ => exact PBF.exn hs2 _
                      | upper =>
                          refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                          cases vs with
                          | nil => exact PBF.liftRes hs2 _
                          | cons _ _ => exact PBF.exn hs2 _
                      | index =>
                          refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                          cases vs with
                          | nil => exact PBF.exn hs2 _
                          | cons v rest =>
                              cases rest with
                              | nil =>
                                  cases v with
                                  | str sub => exact PBF.liftRes hs2 _
                                  | _ =>
                                      simp only [FrameState.swapAt_world, World.swapAt_heap,
                                        RVal.typeNameH_swapAt hs2 htwin]
                                      exact PBF.exn hs2 _
                              | cons _ _ =>
                                  cases v <;>
                                    exact PBF.ite (fun _ => PBF.unsupported)
                                      (fun _ => PBF.exn hs2 _)
                  | _ => exact PBF.unsupported
            | _ => exact PBF.unsupported
          -- ===== H6 KEYWORD TIER =====
          · cases f with
            | name fname sp' =>
                simp only []
                cases Env.lookup st.locals fname with
                | some v =>
                    cases v with
                    | ref b =>
                        refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                        refine PBF.bind (ihEs m s1 (kwargs.toList.map (·.2)) hs1)
                          fun s2 kvs _ hs2 => ?_
                        rcases Heap.get?_swapAt_twin (b := b) hs2 htwin with
                          heq | ⟨_, _, _, _, _, h1, h2⟩
                        · simp only [FrameState.swapAt_world, World.swapAt_heap, heq]
                          cases hget : Heap.get? s2.world.heap b with
                          | none => exact PBF.exn hs2 _
                          | some obj =>
                              cases obj with
                              | cell cv => exact PBF.unsupported
                              | closure nm ps ao lo hg ig bd cap => exact PBF.unsupported
                              | _ => exact PBF.exn hs2 _
                        · simp only [FrameState.swapAt_world, World.swapAt_heap, h1, h2]
                          exact PBF.exn hs2 _
                    | _ =>
                        refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                        refine PBF.bind (ihEs m s1 (kwargs.toList.map (·.2)) hs1)
                          fun s2 kvs _ hs2 => ?_
                        exact PBF.exn hs2 _
                | none =>
                    cases lookupG (moduleGlobals m).1 fname with
                    | some ov =>
                        cases ov with
                        | some gv =>
                            cases gv <;>
                              (refine PBF.bind (ihEs m st args.toList hslot)
                                 fun s1 vs _ hs1 => ?_
                               refine PBF.bind (ihEs m s1 (kwargs.toList.map (·.2)) hs1)
                                 fun s2 kvs _ hs2 => ?_
                               exact PBF.exn hs2 _)
                        | none => exact PBF.unsupported
                    | none =>
                        cases findFunction m fname with
                        | some fdefn =>
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.bind (ihEs m st args.toList hslot) fun s1 vs _ hs1 => ?_
                            refine PBF.bind (ihEs m s1 (kwargs.toList.map (·.2)) hs1)
                              fun s2 kvs _ hs2 => ?_
                            refine PBF.bind (PBF.liftRes hs2 _) fun s3 full _ hs3 => ?_
                            exact PBW.withLocals (ihIn m s3.world fname full hs3)
                        | none =>
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.ite (fun _ => ?_) fun _ => ?_
                            -- dict(k=v, …)
                            · refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                              refine PBF.bind (ihEs m st (kwargs.toList.map (·.2)) hslot)
                                fun s1 kvs _ hs1 => ?_
                              exact PBF.allocDict hs1 _
                            refine PBF.ite (fun _ => ?_) fun _ => ?_
                            -- sorted(…, reverse=…)
                            · refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                              cases kwargs.toList.find? (fun kv => kv.1 != "reverse") with
                              | some kkv =>
                                  obtain ⟨k, kv⟩ := kkv
                                  refine PBF.bind (ihEs m st args.toList hslot)
                                    fun s1 vs _ hs1 => ?_
                                  refine PBF.bind (ihEs m s1 (kwargs.toList.map (·.2)) hs1)
                                    fun s2 kvs _ hs2 => ?_
                                  exact PBF.exn hs2 _
                              | none =>
                                  refine PBF.bind (ihEs m st args.toList hslot)
                                    fun s1 vs _ hs1 => ?_
                                  refine PBF.bind (ihEs m s1 (kwargs.toList.map (·.2)) hs1)
                                    fun s2 kvs _ hs2 => ?_
                                  cases vs with
                                  | nil => exact PBF.exn hs2 _
                                  | cons v rest =>
                                      cases rest with
                                      | cons _ _ => exact PBF.exn hs2 _
                                      | nil =>
                                          cases kvs with
                                          | nil => exact PBF.unsupported
                                          | cons rv rest' =>
                                              cases rest' with
                                              | cons _ _ => exact PBF.unsupported
                                              | nil =>
                                                  simp only [FrameState.swapAt_world,
                                                    World.swapAt_heap, truthyH_swapAt hs2 htwin]
                                                  refine PBF.bind (PBF.liftRes hs2 _)
                                                    fun s3 desc _ hs3 => ?_
                                                  cases v with
                                                  | ref b =>
                                                      rcases Heap.get?_swapAt_twin (b := b) hs3
                                                        htwin with
                                                        heq | ⟨_, _, _, _, _, h1, h2⟩
                                                      · simp only [FrameState.swapAt_world,
                                                          World.swapAt_heap, heq]
                                                        cases hget : Heap.get? s3.world.heap b with
                                                        | none =>
                                                            simp only
                                                              [sortedValH_swapAt hs3 htwin]
                                                            refine PBF.liftMapOk hs3
                                                              fun x hw => ?_
                                                            obtain ⟨h', r⟩ := x
                                                            exact PBF.okWrite
                                                              (sortedValH_slot hs3 hw) _
                                                        | some obj =>
                                                            cases obj with
                                                            | generator qn l cnt stt =>
                                                                refine PBF.bind (PBW.withLocals
                                                                  (ihDrain m s3.world b hs3))
                                                                  fun s4 vals _ hs4 => ?_
                                                                refine PBF.bind
                                                                  (PBF.liftRes hs4 _)
                                                                  fun s5 srt _ hs5 => ?_
                                                                exact PBF.pushRef hs5 _
                                                            | _ =>
                                                                simp only
                                                                  [sortedValH_swapAt hs3 htwin]
                                                                refine PBF.liftMapOk hs3
                                                                  fun x hw => ?_
                                                                obtain ⟨h', r⟩ := x
                                                                exact PBF.okWrite
                                                                  (sortedValH_slot hs3 hw) _
                                                      · simp only [FrameState.swapAt_world,
                                                          World.swapAt_heap, h1, h2]
                                                        refine PBF.bind (PBW.withLocals
                                                          (ihDrain m s3.world b hs3))
                                                          fun s4 vals _ hs4 => ?_
                                                        refine PBF.bind (PBF.liftRes hs4 _)
                                                          fun s5 srt _ hs5 => ?_
                                                        exact PBF.pushRef hs5 _
                                                  | _ =>
                                                      simp only [FrameState.swapAt_world,
                                                        World.swapAt_heap,
                                                        sortedValH_swapAt hs3 htwin]
                                                      refine PBF.liftMapOk hs3 fun x hw => ?_
                                                      obtain ⟨h', r⟩ := x
                                                      exact PBF.okWrite
                                                        (sortedValH_slot hs3 hw) _
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            cases Env.lookup st.world.globals fname with
                            | some _ => exact PBF.unsupported
                            | none =>
                                refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                                exact PBF.ite (fun _ => PBF.exn hslot _)
                                  (fun _ => PBF.unsupported)
            | «attribute» recv attr sp' =>
                refine PBF.bind (ihE m st recv hslot) fun s1 r _ hs1 => ?_
                cases r with
                | ref b =>
                    simp only [FrameState.swapAt_world, World.swapAt_heap,
                      attrCallPlan_swapAt hs1 htwin]
                    cases attrCallPlan m s1.world.heap b attr with
                    | instMethod qname =>
                        simp only []
                        cases findFunction m qname with
                        | none => exact PBF.unsupported
                        | some fdefn =>
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                            refine PBF.bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2)
                              fun s3 kvs _ hs3 => ?_
                            refine PBF.bind (PBF.liftRes hs3 _) fun s4 full _ hs4 => ?_
                            exact PBW.withLocals (ihIn m s4.world qname full hs4)
                    | attrMissing => exact PBF.exn hs1 _
                    | _ => exact PBF.unsupported
                | ntuple tn fs xs =>
                    simp only []
                    cases ntupleCallPlan m tn fs attr with
                    | instMethod qname =>
                        simp only []
                        cases findFunction m qname with
                        | none => exact PBF.unsupported
                        | some fdefn =>
                            refine PBF.ite (fun _ => PBF.unsupported) fun _ => ?_
                            refine PBF.bind (ihEs m s1 args.toList hs1) fun s2 vs _ hs2 => ?_
                            refine PBF.bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2)
                              fun s3 kvs _ hs3 => ?_
                            refine PBF.bind (PBF.liftRes hs3 _) fun s4 full _ hs4 => ?_
                            exact PBW.withLocals (ihIn m s4.world qname full hs4)
                    | attrMissing => exact PBF.exn hs1 _
                    | _ => exact PBF.unsupported
                | _ =>
                    simp only [FrameState.swapAt_world, World.swapAt_heap,
                      RVal.typeNameH_swapAt hs1 htwin]
                    exact PBF.unsupported
            | _ => exact PBF.unsupported

/-! ### The mutual induction on fuel

The eighteen arms above are each a standalone theorem taking `PBAll fuel`
as its hypothesis, so the block's induction is the ONE line this section
exists for: at `fuel + 1` every member is its own arm at the previous
fuel, and at `0` every member is `.timeout` (each one guards on fuel
before anything else). -/

/-- **The whole block, at every fuel.** -/
theorem pbAll (htwin : PayloadTwin o₀ o) : ∀ (fuel : Nat), PBAll pa o₀ o fuel := by
  intro fuel
  induction fuel with
  | zero =>
      -- every member guards on fuel BEFORE it looks at anything, so the whole
      -- block is `.timeout` here and the relation constrains nothing
      exact ⟨fun _ _ _ _ => PBF.timeout, fun _ _ _ _ => PBF.timeout,
        fun _ _ _ _ _ _ => PBF.timeout, fun _ _ _ _ _ _ => PBF.timeout,
        fun _ _ _ _ => PBF.timeout, fun _ _ _ _ => PBF.timeout,
        fun _ _ _ _ _ _ => PBF.timeout, fun _ _ _ _ _ => PBW.timeout,
        fun _ _ _ _ _ _ => PBF.timeout, fun _ _ _ _ _ => PBF.timeout,
        fun _ _ _ _ _ _ _ => PBF.timeout, fun _ _ _ _ _ _ => PBF.timeout,
        fun _ _ _ _ => PBW.timeout, fun _ _ _ _ => PBF.timeout,
        fun _ _ _ _ _ _ => PBF.timeout, fun _ _ _ _ => PBW.timeout,
        fun _ _ _ _ _ => PBW.timeout,
        fun _ _ _ _ _ _ _ _ _ _ _ => PBW.timeout⟩
  | succ n ihn =>
      exact ⟨pbEvalExpr_succ htwin ihn, pbEvalExprs_succ ihn,
        pbEvalBoolChain_succ htwin ihn, pbEvalCompareChain_succ htwin ihn,
        pbExecStmt_succ htwin ihn, pbExecStmts_succ ihn,
        pbExecWhile_succ htwin ihn, pbCallIn_succ ihn,
        pbExecFor_succ htwin ihn, pbEvalDictItems_succ ihn,
        pbExecForList_succ htwin ihn, pbExecAttrCall_succ htwin ihn,
        pbStepIter_succ htwin ihn, pbExecGen_succ htwin ihn,
        pbExecForGen_succ htwin ihn, pbDrainIter_succ ihn,
        pbAnyAllIter_succ htwin ihn, pbCallClosure_succ ihn⟩

end Arms

/-- **THE LOCALITY PROPERTY: the interpreter cannot observe the payload of a
RUNNING generator.** For every fuel, every frame stack and every state whose
heap holds `.generator qname locals₀ cont₀ .running` at `a`, a decided
`execGen` run

1. leaves that slot exactly as it found it (STABILITY — nothing in the run
   can write a running generator, because `stepIter` is the only writer and
   its `.running` arm refuses), and
2. runs identically when the payload is REPLACED (TRANSPORT — same result,
   same locals, same heap off `a`, and the substituted payload still there),

for any other `locals₁`/`cont₁` at the same `qname` and the same `.running`
status. Deliberately narrow on all three counts: an arbitrary OBJECT at `a`
is observable (a list is not a generator), a `.suspended` payload is
observable (`stepIter` resumes it), and `qname` is observable (`repr` and
the type-error messages name it).

§L6 stated this in VCGen.lean and carried it as a hypothesis, because the
proof was an 18-conjunct mutual induction nobody had run. §L7 ran it, so the
definition lives HERE, one line above `payloadBlind` — and VCGen.lean's
generator calculus imports this module and consumes the theorem. -/
def PayloadBlind (m : Module) : Prop :=
  ∀ (F : Nat) (a : Addr) (qname : String) (locals₀ : REnv) (cont₀ : GenCont)
    (st st₁ : FrameState) (k : GenCont) (r : Option (RVal × GenCont)),
    Heap.get? st.world.heap a = some (.generator qname locals₀ cont₀ .running) →
    execGen m F st k = .ok st₁ r →
    Heap.get? st₁.world.heap a = some (.generator qname locals₀ cont₀ .running) ∧
    ∀ (locals₁ : REnv) (cont₁ : GenCont) (h h₁ : Heap),
      Heap.update st.world.heap a (.generator qname locals₁ cont₁ .running) = some h →
      Heap.update st₁.world.heap a (.generator qname locals₁ cont₁ .running) = some h₁ →
      execGen m F ⟨{ st.world with heap := h }, st.locals⟩ k
        = .ok ⟨{ st₁.world with heap := h₁ }, st₁.locals⟩ r

/-! ## The reduction — `PayloadBlind` IS the `execGen` conjunct

What remains after this theorem is exactly the arms: no glue, no side
condition, no consumer-side hypothesis. Both of `PayloadBlind`'s conjuncts
come from the SAME instance of `PBExecGen`, which is the shape finding
§L6 recorded (stability is not a side condition — it is derivable from the
guard transport rests on), now discharged rather than assumed. -/

/-- **The whole property reduces to one conjunct.** Stability is
`PBExecGen` at the IDENTITY twin; transport is `PBExecGen` at the swap the
consumer asks for, with `Heap.update_eq_swapAt` turning its two `update`
hypotheses into the functional form. -/
theorem payloadBlind_of_execGen {m : Module}
    (harm : ∀ (pa : Addr) (o₀ o : Obj), PayloadTwin o₀ o →
      ∀ (fuel : Nat), PBExecGen pa o₀ o fuel) :
    PayloadBlind m := by
  intro F pa qname locals₀ cont₀ st st₁ k r hslot hrun
  refine ⟨?_, fun locals₁ cont₁ h h₁ hset hset₁ => ?_⟩
  · -- STABILITY: the identity twin.
    have htwin : PayloadTwin (.generator qname locals₀ cont₀ .running)
        (.generator qname locals₀ cont₀ .running) :=
      ⟨qname, locals₀, cont₀, locals₀, cont₀, rfl, rfl⟩
    exact ((harm pa _ _ htwin F m st k hslot).1 st₁ r hrun).1
  · -- TRANSPORT: the swap the consumer names.
    have htwin : PayloadTwin (.generator qname locals₀ cont₀ .running)
        (.generator qname locals₁ cont₁ .running) :=
      ⟨qname, locals₀, cont₀, locals₁, cont₁, rfl, rfl⟩
    have hgoal := ((harm pa _ _ htwin F m st k hslot).1 st₁ r hrun).2
    rw [Heap.update_eq_swapAt hset, Heap.update_eq_swapAt hset₁]
    exact hgoal

/-- **THE PROPERTY, PROVED.** `docs/backlog.md` §L6 stated it and priced
its proof; §L7 factored the perturbation as a FUNCTION and this is what
that bought: the reduction above, over the block's own fuel induction. No
hypothesis, no side condition, nothing assumed of the body — the
consumers (`IterDrains.of_genYields`, `gen_moves_drains_ref`) can drop
`PayloadBlind` from their signatures and call this. -/
theorem payloadBlind (m : Module) : PayloadBlind m := by
  refine payloadBlind_of_execGen fun pa o₀ o htwin fuel => ?_
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ihGen, -⟩ := pbAll htwin fuel
  exact ihGen

end LeanModels.Python
