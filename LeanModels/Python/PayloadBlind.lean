import LeanModels.Python.VCGen

/-! # Payload blindness — the interpreter cannot see a RUNNING generator's payload

docs/backlog.md §"L6 LANDED" states `PayloadBlind` (VCGen.lean §L6) and
prices its proof; this module is that proof. The claim: for a slot `a`
holding `.generator qname locals cont .running`, a decided interpreter run
(1) leaves the slot exactly as it found it and (2) runs identically when
the payload is replaced by any other `locals`/`cont` at the same `qname`.

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
EQUATIONS (`f (h.swapAt a o) … = f h …`, §Tier B) rather than two-world
simulations, which is what brings 34 helpers into reach.

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
  | case1 b cls attrs hb | case2 b q l c st hb | case3 b n p a1 a2 a3 a4 bd cp hb
  | case4 b xs hb | case5 b _ _ _ _ =>
      rcases Heap.get?_swapAt_twin (b := b) hslot htwin with heq | ⟨_, _, _, _, _, h1, h2⟩
      · rw [keyHasInstanceRef, keyHasInstanceRef, heq]
      · rw [keyHasInstanceRef, keyHasInstanceRef, h1, h2]
  | case6 xs ih | case7 _ _ xs ih => rw [keyHasInstanceRef, keyHasInstanceRef]; exact ih
  | case8 _ _ _ => rfl
  | case9 t _ _ _ _ => rw [keyHasInstanceRef.eq_def, keyHasInstanceRef.eq_def]; split <;> simp_all
  | case10 => rfl
  | case11 x rest ih1 ih2 => rw [keyHasInstanceRefList, keyHasInstanceRefList, ih1, ih2]

/-- The name CPython would print in `unhashable type: '…'` is blind. -/
theorem unhashableName?_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o) (v : RVal) :
    unhashableName? (Heap.swapAt h pa o) v = unhashableName? h v := by
  induction v using unhashableName?.induct (h := h)
    (motive_2 := fun vs => unhashableNameList? (Heap.swapAt h pa o) vs
      = unhashableNameList? h vs) <;>
  simp_all [unhashableName?, unhashableNameList?, RVal.typeNameH_swapAt hslot htwin]

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

/-- Subscription at the value level is blind. -/
theorem indexValH_swapAt {h : Heap} {pa : Addr} {o₀ o : Obj}
    (hslot : Heap.get? h pa = some o₀) (htwin : PayloadTwin o₀ o)
    (container index : RVal) :
    indexValH (Heap.swapAt h pa o) container index
      = indexValH h container index := by
  unfold indexValH
  split <;>
    simp_all [heapIndex_swapAt hslot htwin, RVal.typeNameH_swapAt hslot htwin]

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

end LeanModels.Python
