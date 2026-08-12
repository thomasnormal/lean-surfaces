import LeanModels.Python.Surface

/-! # Clock erasure — the trace-independence transport theorem (pass 7)

docs/memory-model.md §clock erasure is the recorded design; this module
is its proof. The claim: a run decided `.ok`/`.exn` from a world with
`clock = []` never consulted the clock (the pop arm on `[]` is the loud
underrun `.unsupported`, which nothing converts back — the loudness
invariant), so it runs identically under EVERY seeded trace and returns
the trace untouched. `.timeout` transports too (a run that popped would
have refused, not timed out); `.unsupported` deliberately does NOT — the
underrun itself is the counterexample — and the relation claims nothing
there.

Geometry: `ClockErasedW`/`ClockErasedF` relate the empty-trace BASE run
to the seeded FAMILY; `clockErase` is the 18-conjunct mutual induction
on fuel over the interpreter block, mirroring `fuelMono` arm for arm
(one congruence per `Run` combinator — `bind`/`bindE`/`liftRes`/`ite`/
`withLocals`/`toWorld` — plus `of_seed`, the workhorse closing every
fuel-free tail through the `withClock` simp normal form). The public
payoff is the boundary corollaries at the bottom: every decided
`callFunction`/`CallsIn`/`CallsTo` fact transports to a `∀ tr`
statement over `callFunctionClock` at zero marginal kernel cost. -/

namespace LeanModels.Python

/-! ## Seeding combinators and their normal form -/

/-- Seed a world's clock trace. Deliberately a definition (not unfolded
by the erasure proofs at VARIABLE worlds): goals stay in `withClock`
normal form via the projection and commutation simp lemmas below;
`withClock_mk` unfolds it only at constructor applications, where both
sides of an erasure goal meet in the common `World.mk … tr` form. -/
def World.withClock (w : World) (tr : List Int) : World :=
  { w with clock := tr }

/-- Seed the clock through a frame. -/
def FrameState.withClock (st : FrameState) (tr : List Int) : FrameState :=
  { st with world := st.world.withClock tr }

@[simp] theorem World.withClock_heap (w : World) (tr : List Int) :
    (w.withClock tr).heap = w.heap := rfl
@[simp] theorem World.withClock_globals (w : World) (tr : List Int) :
    (w.withClock tr).globals = w.globals := rfl
@[simp] theorem World.withClock_stdout (w : World) (tr : List Int) :
    (w.withClock tr).stdout = w.stdout := rfl
@[simp] theorem World.withClock_clock (w : World) (tr : List Int) :
    (w.withClock tr).clock = tr := rfl
@[simp] theorem FrameState.withClock_locals (st : FrameState) (tr : List Int) :
    (st.withClock tr).locals = st.locals := rfl
@[simp] theorem FrameState.withClock_world (st : FrameState) (tr : List Int) :
    (st.withClock tr).world = st.world.withClock tr := rfl

/-- Constructor unfolding: `withClock` at a `World.mk` literal computes.
This (with `FrameState.withClock_mk`) is what lets a seeded update
`{ st.withClock tr with world := { … with heap := h } }` and the seeded
BASE leaf meet in one normal form: structure-update syntax elaborates to
constructor applications, the projections rewrite seeded fields, and
these two finish the job. Terminating: the RHS has no `withClock`. -/
@[simp] theorem World.withClock_mk (h : Heap) (g : REnv) (s : List String)
    (c tr : List Int) : (World.mk h g s c).withClock tr = World.mk h g s tr := rfl

@[simp] theorem FrameState.withClock_mk (w : World) (l : REnv) (tr : List Int) :
    (FrameState.mk w l).withClock tr = FrameState.mk (w.withClock tr) l := rfl

/-- Seeding the trace a state already has is the identity (structure eta;
the `h0` discharge of `of_seed` at every fuel-free tail). -/
theorem World.withClock_self {w : World} (h : w.clock = []) :
    w.withClock [] = w := by
  cases w; simp_all [World.withClock]

theorem FrameState.withClock_self {st : FrameState} (h : st.world.clock = []) :
    st.withClock [] = st := by
  cases st with
  | mk w l => simp [FrameState.withClock, World.withClock_self h]

/-- Re-clock a decided run's state; `timeout`/`unsupported` pass through.
The seeded family of a clock-oblivious computation IS `seedF` of its base
run — that equation (`of_seed`) is the workhorse closing every fuel-free
subtree of the erasure induction. -/
def Run.seedF (x : Run FrameState α) (tr : List Int) : Run FrameState α :=
  match x with
  | .ok st v => .ok (st.withClock tr) v
  | .exn st e => .exn (st.withClock tr) e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

/-- The `World`-typed twin. -/
def Run.seedW (x : Run World α) (tr : List Int) : Run World α :=
  match x with
  | .ok w v => .ok (w.withClock tr) v
  | .exn w e => .exn (w.withClock tr) e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

@[simp] theorem Run.seedF_ok {st : FrameState} {v : α} {tr : List Int} :
    (Run.ok st v).seedF tr = .ok (st.withClock tr) v := rfl
@[simp] theorem Run.seedF_exn {st : FrameState} {e : PyErr} {tr : List Int} :
    (Run.exn st e : Run FrameState α).seedF tr = .exn (st.withClock tr) e := rfl
@[simp] theorem Run.seedF_timeout {tr : List Int} :
    (Run.timeout : Run FrameState α).seedF tr = .timeout := rfl
@[simp] theorem Run.seedF_unsupported {msg : String} {tr : List Int} :
    (Run.unsupported msg : Run FrameState α).seedF tr = .unsupported msg := rfl

@[simp] theorem Run.seedW_ok {w : World} {v : α} {tr : List Int} :
    (Run.ok w v).seedW tr = .ok (w.withClock tr) v := rfl
@[simp] theorem Run.seedW_exn {w : World} {e : PyErr} {tr : List Int} :
    (Run.exn w e : Run World α).seedW tr = .exn (w.withClock tr) e := rfl
@[simp] theorem Run.seedW_timeout {tr : List Int} :
    (Run.timeout : Run World α).seedW tr = .timeout := rfl
@[simp] theorem Run.seedW_unsupported {msg : String} {tr : List Int} :
    (Run.unsupported msg : Run World α).seedW tr = .unsupported msg := rfl

/-- `liftRes` is seed-natural: a pure result attached to a seeded state
is the seeded attachment. -/
@[simp] theorem Run.liftRes_withClock {st : FrameState} {tr : List Int}
    {r : Res α} :
    Run.liftRes (st.withClock tr) r = (Run.liftRes st r).seedF tr := by
  cases r <;> rfl

@[simp] theorem Run.liftResW_withClock {w : World} {tr : List Int} {r : Res α} :
    Run.liftRes (w.withClock tr) r = (Run.liftRes w r).seedW tr := by
  cases r <;> rfl

/-- `withLocals` turns a seeded `World` run into the seeded frame run. -/
@[simp] theorem Run.withLocals_seedW {l : REnv} {x : Run World α} {tr : List Int} :
    Run.withLocals l (x.seedW tr) = (Run.withLocals l x).seedF tr := by
  cases x <;> rfl

/-- `toWorld` of a seeded frame run is the seeded world run. -/
@[simp] theorem Run.toWorld_seedF {x : Run FrameState α} {tr : List Int} :
    (x.seedF tr).toWorld = x.toWorld.seedW tr := by
  cases x <;> rfl

/-! ## The clock admission is withClock-invariant -/

@[simp] theorem clockRecvOk_withClock (m : Module) (st : FrameState)
    (tr : List Int) (e : Expr) :
    clockRecvOk m (st.withClock tr) e = clockRecvOk m st e := by
  cases e <;> rfl

@[simp] theorem isClockCall_withClock (m : Module) (st : FrameState)
    (tr : List Int) (recv : Expr) (attr : String) :
    isClockCall m (st.withClock tr) recv attr = isClockCall m st recv attr := by
  simp [isClockCall]

/-! ## The trace-independence relation -/

/-- The trace-independence relation, `World`-typed runs: the base run `x`
(from an EMPTY trace) constrains the seeded family `y` on decided and
timed-out outcomes; refusals constrain nothing (the underrun is the
deliberate counterexample — docs/memory-model.md §clock erasure). -/
abbrev ClockErasedW (x : Run World α) (y : List Int → Run World α) : Prop :=
  (∀ w v, x = .ok w v → w.clock = [] ∧ ∀ tr, y tr = .ok (w.withClock tr) v) ∧
  (∀ w e, x = .exn w e → w.clock = [] ∧ ∀ tr, y tr = .exn (w.withClock tr) e) ∧
  (x = .timeout → ∀ tr, y tr = .timeout)

/-- The `FrameState` twin. -/
abbrev ClockErasedF (x : Run FrameState α) (y : List Int → Run FrameState α) : Prop :=
  (∀ st v, x = .ok st v → st.world.clock = [] ∧ ∀ tr, y tr = .ok (st.withClock tr) v) ∧
  (∀ st e, x = .exn st e → st.world.clock = [] ∧ ∀ tr, y tr = .exn (st.withClock tr) e) ∧
  (x = .timeout → ∀ tr, y tr = .timeout)

namespace ClockErasedF

/-- Decided-ok leaf. -/
theorem ok {st : FrameState} (h : st.world.clock = []) (v : α) :
    ClockErasedF (.ok st v) (fun tr => .ok (st.withClock tr) v) := by
  refine ⟨fun s w hsw => ?_, fun s e hse => ?_, fun ht => ?_⟩
  · cases hsw; exact ⟨h, fun _ => rfl⟩
  · cases hse
  · cases ht

/-- Decided-exn leaf. -/
theorem exn {st : FrameState} (h : st.world.clock = []) (e : PyErr) :
    ClockErasedF (α := α) (.exn st e) (fun tr => .exn (st.withClock tr) e) := by
  refine ⟨fun s w hsw => ?_, fun s e' hse => ?_, fun ht => ?_⟩
  · cases hsw
  · cases hse; exact ⟨h, fun _ => rfl⟩
  · cases ht

/-- Timeout leaf. -/
theorem timeout : ClockErasedF (α := α) .timeout (fun _ => .timeout) := by
  refine ⟨fun s v h => ?_, fun s e h => ?_, fun _ _ => rfl⟩
  · cases h
  · cases h

/-- A refusal on the base side constrains NOTHING — every arm whose
empty-trace run refuses is closed by this, whatever the seeded side
does (the clock-pop arm included). -/
theorem unsupported {msg : String} {y : List Int → Run FrameState α} :
    ClockErasedF (.unsupported msg) y := by
  refine ⟨fun s v h => ?_, fun s e h => ?_, fun h => ?_⟩
  · cases h
  · cases h
  · cases h

/-- THE WORKHORSE: any state-parametric computation whose seeded family
is literally `seedF` of its base run (a fuel-free, clock-oblivious tail —
provable by the withClock simp normal form) is clock-erased. `h0` pins
the base's decided clock: instantiate it by `FrameState.withClock_self`
at the site's emptiness hypothesis. -/
theorem of_seed {x : Run FrameState α} {y : List Int → Run FrameState α}
    (hy : ∀ tr, y tr = x.seedF tr) (h0 : y [] = x) : ClockErasedF x y := by
  have hx : x.seedF [] = x := (hy []).symm.trans h0
  refine ⟨fun s v hsv => ?_, fun s e hse => ?_, fun ht tr => ?_⟩
  · subst hsv
    have hs : s.withClock [] = s := by simpa [Run.seedF] using hx
    have hc : s.world.clock = [] := by
      have := congrArg (fun t => t.world.clock) hs
      simpa using this.symm
    exact ⟨hc, fun tr => by rw [hy tr]; rfl⟩
  · subst hse
    have hs : s.withClock [] = s := by simpa [Run.seedF] using hx
    have hc : s.world.clock = [] := by
      have := congrArg (fun t => t.world.clock) hs
      simpa using this.symm
    exact ⟨hc, fun tr => by rw [hy tr]; rfl⟩
  · subst ht; rw [hy tr]; rfl

/-- `liftRes` congruence: a pure result attached to the threaded state. -/
theorem liftRes {st : FrameState} (h : st.world.clock = []) (r : Res α) :
    ClockErasedF (Run.liftRes st r) (fun tr => Run.liftRes (st.withClock tr) r) := by
  cases r with
  | ok v => exact ok h v
  | exn e => exact exn h e
  | timeout => exact timeout
  | unsupported m => exact unsupported

/-- Bind congruence: the SAME syntactic continuation on both sides, the
head's ok-clause supplying the decided state's emptiness. -/
theorem bind {x : Run FrameState α} {y : List Int → Run FrameState α}
    {f : FrameState → α → Run FrameState β}
    (hx : ClockErasedF x y)
    (hf : ∀ st v, st.world.clock = [] →
      ClockErasedF (f st v) (fun tr => f (st.withClock tr) v)) :
    ClockErasedF (x.bind f) (fun tr => (y tr).bind f) := by
  obtain ⟨hok, hexn, hto⟩ := hx
  cases x with
  | ok s a =>
    obtain ⟨hs, hy⟩ := hok s a rfl
    have := hf s a hs
    refine ⟨?_, ?_, ?_⟩
    · intro st v h
      obtain ⟨h1, h2⟩ := this.1 st v h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro st e h
      obtain ⟨h1, h2⟩ := this.2.1 st e h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro h
      exact fun tr => by simp only [hy tr]; exact this.2.2 h tr
  | exn s e =>
    obtain ⟨hs, hy⟩ := hexn s e rfl
    refine ⟨fun _ _ h => ?_, fun st e' h => ?_, fun h => ?_⟩
    · cases h
    · cases h; exact ⟨hs, fun tr => by simp [hy tr]⟩
    · cases h
  | timeout =>
    refine ⟨fun s v h => ?_, fun s e h => ?_, fun _ tr => ?_⟩
    · cases h
    · cases h
    · simp [hto rfl tr]
  | unsupported m =>
    refine ⟨fun s v h => ?_, fun s e h => ?_, fun h => ?_⟩
    · cases h
    · cases h
    · cases h

/-- `bindE` congruence (the exceptions-tier bind: `stepIter`'s
close-on-exn) — both continuations at the same syntactic shape. -/
theorem bindE {x : Run FrameState α} {y : List Int → Run FrameState α}
    {f : FrameState → α → Run FrameState β}
    {g : FrameState → PyErr → Run FrameState β}
    (hx : ClockErasedF x y)
    (hf : ∀ st v, st.world.clock = [] →
      ClockErasedF (f st v) (fun tr => f (st.withClock tr) v))
    (hg : ∀ st e, st.world.clock = [] →
      ClockErasedF (g st e) (fun tr => g (st.withClock tr) e)) :
    ClockErasedF (x.bindE f g) (fun tr => (y tr).bindE f g) := by
  obtain ⟨hok, hexn, hto⟩ := hx
  cases x with
  | ok s a =>
    obtain ⟨hs, hy⟩ := hok s a rfl
    have := hf s a hs
    refine ⟨?_, ?_, ?_⟩
    · intro st v h
      obtain ⟨h1, h2⟩ := this.1 st v h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro st e h
      obtain ⟨h1, h2⟩ := this.2.1 st e h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro h
      exact fun tr => by simp only [hy tr]; exact this.2.2 h tr
  | exn s e =>
    obtain ⟨hs, hy⟩ := hexn s e rfl
    have := hg s e hs
    refine ⟨?_, ?_, ?_⟩
    · intro st v h
      obtain ⟨h1, h2⟩ := this.1 st v h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro st e' h
      obtain ⟨h1, h2⟩ := this.2.1 st e' h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro h
      exact fun tr => by simp only [hy tr]; exact this.2.2 h tr
  | timeout =>
    refine ⟨fun s v h => ?_, fun s e h => ?_, fun _ tr => ?_⟩
    · cases h
    · cases h
    · simp [hto rfl tr]
  | unsupported m =>
    refine ⟨fun s v h => ?_, fun s e h => ?_, fun h => ?_⟩
    · cases h
    · cases h
    · cases h

/-- `ite` congruence: the condition is trace-independent (it normalized
to the SAME term on both sides), so the fork is shared. -/
theorem ite {c : Prop} [Decidable c] {x z : Run FrameState α}
    {y w : List Int → Run FrameState α}
    (hx : ClockErasedF x y) (hz : ClockErasedF z w) :
    ClockErasedF (if c then x else z) (fun tr => if c then y tr else w tr) := by
  by_cases hc : c
  · simpa [hc] using hx
  · simpa [hc] using hz

end ClockErasedF

namespace ClockErasedW

/-- Decided-ok leaf. -/
theorem ok {w : World} (h : w.clock = []) (v : α) :
    ClockErasedW (.ok w v) (fun tr => .ok (w.withClock tr) v) := by
  refine ⟨fun s a hsa => ?_, fun s e hse => ?_, fun ht => ?_⟩
  · cases hsa; exact ⟨h, fun _ => rfl⟩
  · cases hse
  · cases ht

/-- Decided-exn leaf. -/
theorem exn {w : World} (h : w.clock = []) (e : PyErr) :
    ClockErasedW (α := α) (.exn w e) (fun tr => .exn (w.withClock tr) e) := by
  refine ⟨fun s a hsa => ?_, fun s e' hse => ?_, fun ht => ?_⟩
  · cases hsa
  · cases hse; exact ⟨h, fun _ => rfl⟩
  · cases ht

/-- Timeout leaf. -/
theorem timeout : ClockErasedW (α := α) .timeout (fun _ => .timeout) := by
  refine ⟨fun s v h => ?_, fun s e h => ?_, fun _ _ => rfl⟩
  · cases h
  · cases h

/-- Refusals constrain nothing. -/
theorem unsupported {msg : String} {y : List Int → Run World α} :
    ClockErasedW (.unsupported msg) y := by
  refine ⟨fun s v h => ?_, fun s e h => ?_, fun h => ?_⟩
  · cases h
  · cases h
  · cases h

/-- The `World`-typed workhorse (see `ClockErasedF.of_seed`). -/
theorem of_seed {x : Run World α} {y : List Int → Run World α}
    (hy : ∀ tr, y tr = x.seedW tr) (h0 : y [] = x) : ClockErasedW x y := by
  have hx : x.seedW [] = x := (hy []).symm.trans h0
  refine ⟨fun s v hsv => ?_, fun s e hse => ?_, fun ht tr => ?_⟩
  · subst hsv
    have hs : s.withClock [] = s := by simpa [Run.seedW] using hx
    have hc : s.clock = [] := by
      have := congrArg (fun t => t.clock) hs
      simpa using this.symm
    exact ⟨hc, fun tr => by rw [hy tr]; rfl⟩
  · subst hse
    have hs : s.withClock [] = s := by simpa [Run.seedW] using hx
    have hc : s.clock = [] := by
      have := congrArg (fun t => t.clock) hs
      simpa using this.symm
    exact ⟨hc, fun tr => by rw [hy tr]; rfl⟩
  · subst ht; rw [hy tr]; rfl

/-- `liftRes` congruence. -/
theorem liftRes {w : World} (h : w.clock = []) (r : Res α) :
    ClockErasedW (Run.liftRes w r) (fun tr => Run.liftRes (w.withClock tr) r) := by
  cases r with
  | ok v => exact ok h v
  | exn e => exact exn h e
  | timeout => exact timeout
  | unsupported m => exact unsupported

/-- Bind congruence. -/
theorem bind {x : Run World α} {y : List Int → Run World α}
    {f : World → α → Run World β}
    (hx : ClockErasedW x y)
    (hf : ∀ w v, w.clock = [] →
      ClockErasedW (f w v) (fun tr => f (w.withClock tr) v)) :
    ClockErasedW (x.bind f) (fun tr => (y tr).bind f) := by
  obtain ⟨hok, hexn, hto⟩ := hx
  cases x with
  | ok s a =>
    obtain ⟨hs, hy⟩ := hok s a rfl
    have := hf s a hs
    refine ⟨?_, ?_, ?_⟩
    · intro st v h
      obtain ⟨h1, h2⟩ := this.1 st v h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro st e h
      obtain ⟨h1, h2⟩ := this.2.1 st e h
      exact ⟨h1, fun tr => by simp only [hy tr]; exact h2 tr⟩
    · intro h
      exact fun tr => by simp only [hy tr]; exact this.2.2 h tr
  | exn s e =>
    obtain ⟨hs, hy⟩ := hexn s e rfl
    refine ⟨fun _ _ h => ?_, fun st e' h => ?_, fun h => ?_⟩
    · cases h
    · cases h; exact ⟨hs, fun tr => by simp [hy tr]⟩
    · cases h
  | timeout =>
    refine ⟨fun s v h => ?_, fun s e h => ?_, fun _ tr => ?_⟩
    · cases h
    · cases h
    · simp [hto rfl tr]
  | unsupported m =>
    refine ⟨fun s v h => ?_, fun s e h => ?_, fun h => ?_⟩
    · cases h
    · cases h
    · cases h

/-- `ite` congruence. -/
theorem ite {c : Prop} [Decidable c] {x z : Run World α}
    {y w : List Int → Run World α}
    (hx : ClockErasedW x y) (hz : ClockErasedW z w) :
    ClockErasedW (if c then x else z) (fun tr => if c then y tr else w tr) := by
  by_cases hc : c
  · simpa [hc] using hx
  · simpa [hc] using hz

/-- Lifting a `World` run into a frame (`Run.withLocals`): the locals ride
through on BOTH sides, and a frame seeded at those locals IS the seeded
world at those locals (`rfl` through `FrameState.withClock_mk`). -/
theorem withLocals {l : REnv} {x : Run World α} {y : List Int → Run World α}
    (hx : ClockErasedW x y) :
    ClockErasedF (Run.withLocals l x) (fun tr => Run.withLocals l (y tr)) := by
  obtain ⟨hok, hexn, hto⟩ := hx
  cases x with
  | ok w a =>
    obtain ⟨hw, hy⟩ := hok w a rfl
    refine ⟨fun st v h => ?_, fun st e h => ?_, fun h => ?_⟩
    · cases h; exact ⟨hw, fun tr => by simp [hy tr, Run.withLocals]⟩
    · cases h
    · cases h
  | exn w e =>
    obtain ⟨hw, hy⟩ := hexn w e rfl
    refine ⟨fun st v h => ?_, fun st e' h => ?_, fun h => ?_⟩
    · cases h
    · cases h; exact ⟨hw, fun tr => by simp [hy tr, Run.withLocals]⟩
    · cases h
  | timeout =>
    refine ⟨fun st v h => ?_, fun st e h => ?_, fun h tr => ?_⟩
    · cases h
    · cases h
    · simp [hto rfl tr, Run.withLocals]
  | unsupported m =>
    refine ⟨fun st v h => ?_, fun st e h => ?_, fun h => ?_⟩
    · cases h
    · cases h
    · cases h

end ClockErasedW

/-- Projecting a frame run back to its world (`Run.toWorld`, the return
from a call). -/
theorem ClockErasedF.toWorld {x : Run FrameState α}
    {y : List Int → Run FrameState α} (hx : ClockErasedF x y) :
    ClockErasedW (Run.toWorld x) (fun tr => Run.toWorld (y tr)) := by
  obtain ⟨hok, hexn, hto⟩ := hx
  cases x with
  | ok s a =>
    obtain ⟨hs, hy⟩ := hok s a rfl
    refine ⟨fun w v h => ?_, fun w e h => ?_, fun h => ?_⟩
    · cases h; exact ⟨hs, fun tr => by simp [hy tr, Run.toWorld]⟩
    · cases h
    · cases h
  | exn s e =>
    obtain ⟨hs, hy⟩ := hexn s e rfl
    refine ⟨fun w v h => ?_, fun w e' h => ?_, fun h => ?_⟩
    · cases h
    · cases h; exact ⟨hs, fun tr => by simp [hy tr, Run.toWorld]⟩
    · cases h
  | timeout =>
    refine ⟨fun w v h => ?_, fun w e h => ?_, fun h tr => ?_⟩
    · cases h
    · cases h
    · simp [hto rfl tr, Run.toWorld]
  | unsupported m =>
    refine ⟨fun w v h => ?_, fun w e h => ?_, fun h => ?_⟩
    · cases h
    · cases h
    · cases h



/-- `attrReadResult` (the H3 attribute-read helper, outside the mutual
block) is seed-natural: the plan reads only the heap. -/
theorem attrReadResult_withClock (m : Module) (st : FrameState) (a : Addr)
    (attr : String) (tr : List Int) :
    attrReadResult m (st.withClock tr) a attr =
      (attrReadResult m st a attr).seedF tr := by
  unfold attrReadResult
  simp only [FrameState.withClock_world, World.withClock_heap]
  cases attrReadPlan m st.world.heap a attr <;> simp

/-- The relational form of `attrReadResult_withClock`. -/
theorem ceAttrReadResult {m : Module} {st : FrameState} {a : Addr}
    {attr : String} (h : st.world.clock = []) :
    ClockErasedF (attrReadResult m st a attr)
      (fun tr => attrReadResult m (st.withClock tr) a attr) :=
  .of_seed (fun tr => attrReadResult_withClock m st a attr tr)
    (by simp only [FrameState.withClock_self h])

/-- Normalize seeded-state projections (the withClock normal form). -/
macro "ce_norm" : tactic =>
  `(tactic| try simp only [FrameState.withClock_world, FrameState.withClock_locals,
      World.withClock_heap, World.withClock_globals, World.withClock_stdout,
      World.withClock_clock, isClockCall_withClock, clockRecvOk_withClock])

/-! ## The per-member erasure statements (fuelMono's conjunct order) -/

abbrev CEEvalExpr (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (e : Expr), st.world.clock = [] →
    ClockErasedF (evalExpr m fuel st e)
      (fun tr => evalExpr m fuel (st.withClock tr) e)

abbrev CEEvalExprs (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (es : List Expr), st.world.clock = [] →
    ClockErasedF (evalExprs m fuel st es)
      (fun tr => evalExprs m fuel (st.withClock tr) es)

abbrev CEEvalBoolChain (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (op : BoolOp) (e : Expr) (rest : List Expr),
    st.world.clock = [] →
    ClockErasedF (evalBoolChain m fuel st op e rest)
      (fun tr => evalBoolChain m fuel (st.withClock tr) op e rest)

abbrev CEEvalCompareChain (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (lhs : RVal) (ops : List CmpOp)
    (cs : List Expr), st.world.clock = [] →
    ClockErasedF (evalCompareChain m fuel st lhs ops cs)
      (fun tr => evalCompareChain m fuel (st.withClock tr) lhs ops cs)

abbrev CEExecStmt (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (s : Stmt), st.world.clock = [] →
    ClockErasedF (execStmt m fuel st s)
      (fun tr => execStmt m fuel (st.withClock tr) s)

abbrev CEExecStmts (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (ss : List Stmt), st.world.clock = [] →
    ClockErasedF (execStmts m fuel st ss)
      (fun tr => execStmts m fuel (st.withClock tr) ss)

abbrev CEExecWhile (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (test : Expr) (body orelse : List Stmt),
    st.world.clock = [] →
    ClockErasedF (execWhile m fuel st test body orelse)
      (fun tr => execWhile m fuel (st.withClock tr) test body orelse)

abbrev CECallIn (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (fname : String) (args : Array RVal),
    w.clock = [] →
    ClockErasedW (callIn m fuel w fname args)
      (fun tr => callIn m fuel (w.withClock tr) fname args)

abbrev CEExecFor (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (target : Expr) (xs : List RVal)
    (body : List Stmt), st.world.clock = [] →
    ClockErasedF (execFor m fuel st target xs body)
      (fun tr => execFor m fuel (st.withClock tr) target xs body)

abbrev CEEvalDictItems (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (keys values : List Expr),
    st.world.clock = [] →
    ClockErasedF (evalDictItems m fuel st keys values)
      (fun tr => evalDictItems m fuel (st.withClock tr) keys values)

abbrev CEExecForList (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (target : Expr) (a : Addr) (i : Nat)
    (body : List Stmt), st.world.clock = [] →
    ClockErasedF (execForList m fuel st target a i body)
      (fun tr => execForList m fuel (st.withClock tr) target a i body)

abbrev CEExecAttrCall (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (a : Addr) (attr : String)
    (args : List Expr), st.world.clock = [] →
    ClockErasedF (execAttrCall m fuel st a attr args)
      (fun tr => execAttrCall m fuel (st.withClock tr) a attr args)

abbrev CEStepIter (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (a : Addr), w.clock = [] →
    ClockErasedW (stepIter m fuel w a)
      (fun tr => stepIter m fuel (w.withClock tr) a)

abbrev CEExecGen (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (k : GenCont), st.world.clock = [] →
    ClockErasedF (execGen m fuel st k)
      (fun tr => execGen m fuel (st.withClock tr) k)

abbrev CEExecForGen (fuel : Nat) : Prop :=
  ∀ (m : Module) (st : FrameState) (target : Expr) (a : Addr)
    (body : List Stmt), st.world.clock = [] →
    ClockErasedF (execForGen m fuel st target a body)
      (fun tr => execForGen m fuel (st.withClock tr) target a body)

abbrev CEDrainIter (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (a : Addr), w.clock = [] →
    ClockErasedW (drainIter m fuel w a)
      (fun tr => drainIter m fuel (w.withClock tr) a)

abbrev CEAnyAllIter (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (a : Addr) (isAll : Bool), w.clock = [] →
    ClockErasedW (anyAllIter m fuel w a isAll)
      (fun tr => anyAllIter m fuel (w.withClock tr) a isAll)

abbrev CECallClosure (fuel : Nat) : Prop :=
  ∀ (m : Module) (w : World) (name : String) (params : Array Param)
    (ao lo ig : Bool) (body : Array Stmt) (cap : REnv) (args : Array RVal),
    w.clock = [] →
    ClockErasedW (callClosure m fuel w name params ao lo ig body cap args)
      (fun tr => callClosure m fuel (w.withClock tr) name params ao lo ig body cap args)

/-- The whole-block statement, fuelMono's conjunct order. -/
abbrev CE (fuel : Nat) : Prop :=
  CEEvalExpr fuel ∧ CEEvalExprs fuel ∧ CEEvalBoolChain fuel ∧
  CEEvalCompareChain fuel ∧ CEExecStmt fuel ∧ CEExecStmts fuel ∧
  CEExecWhile fuel ∧ CECallIn fuel ∧ CEExecFor fuel ∧ CEEvalDictItems fuel ∧
  CEExecForList fuel ∧ CEExecAttrCall fuel ∧ CEStepIter fuel ∧
  CEExecGen fuel ∧ CEExecForGen fuel ∧ CEDrainIter fuel ∧
  CEAnyAllIter fuel ∧ CECallClosure fuel

/-! ## The succ-step arm lemmas -/

section Arms
variable {fuel : Nat}

theorem ceEvalExprs_succ (ih : CE fuel) : CEEvalExprs (fuel + 1) := by
  obtain ⟨ihE, ihEs, -⟩ := ih
  intro m st es h
  cases es with
  | nil => simp only [evalExprs]; exact .ok h _
  | cons e rest =>
    simp only [evalExprs]
    exact .bind (ihE m st e h) fun s v hs =>
      .bind (ihEs m s rest hs) fun s2 vs hs2 => .ok hs2 _

theorem ceEvalDictItems_succ (ih : CE fuel) : CEEvalDictItems (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, -⟩ := ih
  intro m st keys values h
  cases keys with
  | nil =>
    cases values with
    | nil => simp only [evalDictItems]; exact .ok h _
    | cons v vs => simp only [evalDictItems]; exact .unsupported
  | cons k ks =>
    cases values with
    | nil => simp only [evalDictItems]; exact .unsupported
    | cons v vs =>
      simp only [evalDictItems]
      exact .bind (ihE m st k h) fun s kv hs =>
        .bind (ihE m s v hs) fun s2 vv hs2 =>
          .bind (ihItems m s2 ks vs hs2) fun s3 rest hs3 => .ok hs3 _

theorem ceEvalBoolChain_succ (ih : CE fuel) : CEEvalBoolChain (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, -⟩ := ih
  intro m st op e rest h
  simp only [evalBoolChain]
  refine .bind (ihE m st e h) fun s v hs => ?_
  cases rest with
  | nil => exact .ok hs _
  | cons e2 rest2 =>
    refine .bind (.liftRes hs _) fun s2 b hs2 => ?_
    cases op with
    | and => exact .ite (ihB m s2 .and e2 rest2 hs2) (.ok hs2 _)
    | or => exact .ite (.ok hs2 _) (ihB m s2 .or e2 rest2 hs2)

theorem ceEvalCompareChain_succ (ih : CE fuel) : CEEvalCompareChain (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, -⟩ := ih
  intro m st lhs ops cs h
  cases ops with
  | nil =>
    cases cs with
    | nil => simp only [evalCompareChain]; exact .ok h _
    | cons c cs2 => simp only [evalCompareChain]; exact .unsupported
  | cons op ops2 =>
    cases cs with
    | nil => simp only [evalCompareChain]; exact .unsupported
    | cons e rest =>
      simp only [evalCompareChain]
      refine .bind (ihE m st e h) fun s rhs hs => ?_
      refine .bind (.liftRes hs _) fun s2 b hs2 => ?_
      exact .ite (ihC m s2 rhs ops2 rest hs2) (.ok hs2 _)


theorem ceExecStmts_succ (ih : CE fuel) : CEExecStmts (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, -⟩ := ih
  intro m st ss h
  cases ss with
  | nil => simp only [execStmts]; exact .ok h _
  | cons s rest =>
    simp only [execStmts]
    refine .bind (ihS m st s h) fun s2 flow hs2 => ?_
    cases flow with
    | next => exact ihSs m s2 rest hs2
    | ret v => exact .ok hs2 _
    | brk => exact .ok hs2 _
    | cont => exact .ok hs2 _

theorem ceExecFor_succ (ih : CE fuel) : CEExecFor (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, -⟩ := ih
  intro m st target xs body h
  cases xs with
  | nil => simp only [execFor]; exact .ok h _
  | cons x rest =>
    simp only [execFor, FrameState.withClock_world, FrameState.withClock_locals,
      World.withClock_heap]
    refine .bind (.liftRes h _) fun s env1 hs => ?_
    refine .bind (ihSs m { s with locals := env1 } body hs) fun s2 flow hs2 => ?_
    cases flow with
    | next => exact ihFor m s2 target rest body hs2
    | cont => exact ihFor m s2 target rest body hs2
    | brk => exact .ok hs2 _
    | ret v => exact .ok hs2 _

theorem ceExecForList_succ (ih : CE fuel) : CEExecForList (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, ihForG, -⟩ := ih
  intro m st target a i body h
  simp only [execForList, FrameState.withClock_world, FrameState.withClock_locals,
    World.withClock_heap]
  cases hobj : Heap.get? st.world.heap a with
  | none => exact .unsupported
  | some obj =>
    cases obj with
    | list xs =>
      refine .ite ?_ (.ok h _)
      refine .bind (.liftRes h _) fun s env1 hs => ?_
      refine .bind (ihSs m { s with locals := env1 } body hs) fun s2 flow hs2 => ?_
      cases flow with
      | next => exact ihForL m s2 target a (i + 1) body hs2
      | cont => exact ihForL m s2 target a (i + 1) body hs2
      | brk => exact .ok hs2 _
      | ret v => exact .ok hs2 _
    | dict entries ver => exact .unsupported
    | «instance» cid attrs => exact .exn h _
    | generator qn l k stat => exact .ite .unsupported (ihForG m st target a body h)
    | closure nm ps ao lo hg ig bd cap => exact .unsupported
    | pyset xs => exact .unsupported

theorem ceExecWhile_succ (ih : CE fuel) : CEExecWhile (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, -⟩ := ih
  intro m st test body orelse h
  simp only [execWhile]
  refine .bind (ihE m st test h) fun s t hs => ?_
  refine .bind (.liftRes hs _) fun s2 b hs2 => ?_
  refine .ite ?_ (ihSs m s2 orelse hs2)
  refine .bind (ihSs m s2 body hs2) fun s3 flow hs3 => ?_
  cases flow with
  | next => exact ihW m s3 test body orelse hs3
  | cont => exact ihW m s3 test body orelse hs3
  | brk => exact .ok hs3 _
  | ret v => exact .ok hs3 _

theorem ceCallIn_succ (ih : CE fuel) : CECallIn (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, -⟩ := ih
  intro m w fname args h
  simp only [callIn]
  cases hf : findFunction m fname with
  | none => exact .exn h _
  | some f =>
    refine .ite .unsupported (.ite .unsupported (.ite (.exn h _) (.ite ?_ ?_)))
    · exact .of_seed (fun tr => by simp) (by simp only [World.withClock_self h])
    · refine ClockErasedF.toWorld
        (.bind (ihSs m ⟨w, mkCallEnv f.params args⟩ f.body.toList h)
          fun s flow hs => ?_)
      cases flow with
      | ret v => exact .ok hs _
      | next => exact .ok hs _
      | brk => exact .unsupported
      | cont => exact .unsupported

theorem ceCallClosure_succ (ih : CE fuel) : CECallClosure (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, -⟩ := ih
  intro m w name params ao lo ig body cap args h
  simp only [callClosure]
  refine .ite .unsupported (.ite .unsupported (.ite (.exn h _) (.ite ?_ ?_)))
  · exact .of_seed (fun tr => by simp) (by simp only [World.withClock_self h])
  · refine ClockErasedF.toWorld
      (.bind (ihSs m ⟨w, mkCallEnv params args ++ cap⟩ body.toList h)
        fun s flow hs => ?_)
    cases flow with
    | ret v => exact .ok hs _
    | next => exact .ok hs _
    | brk => exact .unsupported
    | cont => exact .unsupported

theorem ceStepIter_succ (ih : CE fuel) : CEStepIter (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, -⟩ := ih
  intro m w a h
  simp only [stepIter, World.withClock_heap]
  cases hobj : Heap.get? w.heap a with
  | none => exact .unsupported
  | some obj =>
    cases obj with
    | generator qname locals cont status =>
      cases status with
      | closed => exact .ok h _
      | running => exact .exn h _
      | created =>
        dsimp only
        cases hupd : Heap.update w.heap a (.generator qname locals cont .running) with
        | none => exact .unsupported
        | some h1 =>
          refine ClockErasedF.toWorld
            (.bindE (ihGen m ⟨{ w with heap := h1 }, locals⟩ cont h)
              (fun s r hs => ?_) (fun s e hs => ?_))
          · refine .of_seed (fun tr => ?_) (by simp only [FrameState.withClock_self hs])
            cases r with
            | none =>
              cases hu2 : Heap.update s.world.heap a (.generator qname s.locals [] .closed) <;>
                simp [hu2]
            | some vc =>
              cases vc with
              | mk v cont2 =>
                cases hu2 : Heap.update s.world.heap a
                    (.generator qname s.locals cont2 .suspended) <;> simp [hu2]
          · refine .of_seed (fun tr => ?_) (by simp only [FrameState.withClock_self hs])
            cases hu2 : Heap.update s.world.heap a (.generator qname s.locals [] .closed) <;>
              simp [hu2]
      | suspended =>
        dsimp only
        cases hupd : Heap.update w.heap a (.generator qname locals cont .running) with
        | none => exact .unsupported
        | some h1 =>
          refine ClockErasedF.toWorld
            (.bindE (ihGen m ⟨{ w with heap := h1 }, locals⟩ cont h)
              (fun s r hs => ?_) (fun s e hs => ?_))
          · refine .of_seed (fun tr => ?_) (by simp only [FrameState.withClock_self hs])
            cases r with
            | none =>
              cases hu2 : Heap.update s.world.heap a (.generator qname s.locals [] .closed) <;>
                simp [hu2]
            | some vc =>
              cases vc with
              | mk v cont2 =>
                cases hu2 : Heap.update s.world.heap a
                    (.generator qname s.locals cont2 .suspended) <;> simp [hu2]
          · refine .of_seed (fun tr => ?_) (by simp only [FrameState.withClock_self hs])
            cases hu2 : Heap.update s.world.heap a (.generator qname s.locals [] .closed) <;>
              simp [hu2]
    | list xs => exact .exn h _
    | dict entries ver => exact .exn h _
    | «instance» cid attrs => exact .exn h _
    | closure nm ps ao lo hg ig bd cap => exact .exn h _
    | pyset xs => exact .exn h _

theorem ceExecForGen_succ (ih : CE fuel) : CEExecForGen (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, ihForG, -⟩ := ih
  intro m st target a body h
  simp only [execForGen, FrameState.withClock_world, FrameState.withClock_locals]
  refine .bind (ClockErasedW.withLocals (ihStep m st.world a h)) fun s r hs => ?_
  cases r with
  | none => exact .ok hs _
  | some v =>
    refine .bind (.liftRes hs _) fun s2 env1 hs2 => ?_
    refine .bind (ihSs m { s2 with locals := env1 } body hs2) fun s3 flow hs3 => ?_
    cases flow with
    | next => exact ihForG m s3 target a body hs3
    | cont => exact ihForG m s3 target a body hs3
    | brk => exact .ok hs3 _
    | ret v => exact .ok hs3 _

theorem ceDrainIter_succ (ih : CE fuel) : CEDrainIter (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, ihForG, ihDrain, -⟩ := ih
  intro m w a h
  simp only [drainIter]
  refine .bind (ihStep m w a h) fun w2 r hw2 => ?_
  cases r with
  | none => exact .ok hw2 _
  | some v =>
    exact .bind (ihDrain m w2 a hw2) fun w3 vs hw3 => .ok hw3 _

theorem ceAnyAllIter_succ (ih : CE fuel) : CEAnyAllIter (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, ihForG, ihDrain, ihAnyAll, -⟩ := ih
  intro m w a isAll h
  simp only [anyAllIter]
  refine .bind (ihStep m w a h) fun w2 r hw2 => ?_
  cases r with
  | none => exact .ok hw2 _
  | some v =>
    refine .bind (.liftRes hw2 _) fun w3 b hw3 => ?_
    exact .ite (.ok hw3 _) (ihAnyAll m w3 a isAll hw3)


theorem ceExecGen_succ (ih : CE fuel) : CEExecGen (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, -⟩ := ih
  intro m st k h
  cases k with
  | nil => simp only [execGen]; exact .ok h _
  | cons fr k' =>
    cases fr with
    | block bs =>
      cases bs with
      | nil => simp only [execGen]; exact ihGen m st k' h
      | cons s ss =>
        simp only [execGen]
        cases hp : genPlan s with
        | delegate =>
          refine .bind (ihS m st s h) fun s2 flow hs2 => ?_
          cases flow with
          | next => exact ihGen m s2 (.block ss :: k') hs2
          | ret v =>
            cases v with
            | none => exact .ok hs2 _
            | bool b => exact .unsupported
            | int n => exact .unsupported
            | str sv => exact .unsupported
            | tuple xs => exact .unsupported
            | listV xs => exact .unsupported
            | ntuple tn fs xs => exact .unsupported
            | rangeV lo hi step => exact .unsupported
            | ref a => exact .unsupported
          | brk =>
            cases hb : genBreak k' with
            | some k2 => exact ihGen m s2 k2 hs2
            | none => exact .unsupported
          | cont =>
            cases hb : genContinue k' with
            | some k2 => exact ihGen m s2 k2 hs2
            | none => exact .unsupported
        | yieldHere e =>
          exact .bind (ihE m st e h) fun s2 v hs2 => .ok hs2 _
        | branch test body orelse =>
          refine .bind (ihE m st test h) fun s2 t hs2 => ?_
          refine .bind (.liftRes hs2 _) fun s3 b hs3 => ?_
          exact ihGen m s3 _ hs3
        | whileHere test body orelse => exact ihGen m st _ h
        | forHere target iter body =>
          refine .bind (ihE m st iter h) fun s2 it hs2 => ?_
          cases it with
          | none => exact .exn hs2 _
          | bool b => exact .exn hs2 _
          | int n => exact .exn hs2 _
          | str sv => exact ihGen m s2 _ hs2
          | tuple xs => exact ihGen m s2 _ hs2
          | listV xs => exact ihGen m s2 _ hs2
          | ntuple tn fs xs => exact ihGen m s2 _ hs2
          | rangeV lo hi step =>
            exact .bind (.liftRes hs2 _) fun s3 xs hs3 => ihGen m s3 _ hs3
          | ref ad =>
            simp only [FrameState.withClock_world, World.withClock_heap]
            cases hobj : Heap.get? s2.world.heap ad with
            | none => exact .unsupported
            | some obj =>
              cases obj with
              | list xs => exact ihGen m s2 _ hs2
              | generator qn l cont stat => exact ihGen m s2 _ hs2
              | dict entries ver => exact .unsupported
              | «instance» cid attrs => exact .exn hs2 _
              | closure nm ps ao lo hg ig bd cap => exact .exn hs2 _
              | pyset xs => exact .unsupported
        | refuse msg => exact .unsupported
    | forSeq target xs body =>
      cases xs with
      | nil => simp only [execGen]; exact ihGen m st k' h
      | cons x rest =>
        simp only [execGen]
        refine .bind (.liftRes h _) fun s2 env1 hs2 => ?_
        exact ihGen m { s2 with locals := env1 } _ hs2
    | forList target ad i body =>
      simp only [execGen, FrameState.withClock_world, World.withClock_heap]
      cases hobj : Heap.get? st.world.heap ad with
      | none => exact .unsupported
      | some obj =>
        cases obj with
        | list xs =>
          refine .ite ?_ (ihGen m st k' h)
          refine .bind (.liftRes h _) fun s2 env1 hs2 => ?_
          exact ihGen m { s2 with locals := env1 } _ hs2
        | dict entries ver => exact .unsupported
        | «instance» cid attrs => exact .exn h _
        | generator qn l cont stat => exact .unsupported
        | closure nm ps ao lo hg ig bd cap => exact .unsupported
        | pyset xs => exact .unsupported
    | forGen target ad body =>
      simp only [execGen, FrameState.withClock_world, FrameState.withClock_locals]
      refine .bind (ClockErasedW.withLocals (ihStep m st.world ad h)) fun s2 r hs2 => ?_
      cases r with
      | none => exact ihGen m s2 k' hs2
      | some v =>
        refine .bind (.liftRes hs2 _) fun s3 env1 hs3 => ?_
        exact ihGen m { s3 with locals := env1 } _ hs3
    | whileLoop test body orelse =>
      simp only [execGen]
      refine .bind (ihE m st test h) fun s2 t hs2 => ?_
      refine .bind (.liftRes hs2 _) fun s3 b hs3 => ?_
      exact .ite (ihGen m s3 _ hs3) (ihGen m s3 _ hs3)
    | enumSeq i xs =>
      cases xs with
      | nil => simp only [execGen]; exact ihGen m st k' h
      | cons x rest => simp only [execGen]; exact .ok h _
    | enumList i ad cur =>
      simp only [execGen, FrameState.withClock_world, World.withClock_heap]
      cases hobj : Heap.get? st.world.heap ad with
      | none => exact .unsupported
      | some obj =>
        cases obj with
        | list xs => exact .ite (.ok h _) (ihGen m st k' h)
        | dict entries ver => exact .unsupported
        | «instance» cid attrs => exact .unsupported
        | generator qn l cont stat => exact .unsupported
        | closure nm ps ao lo hg ig bd cap => exact .unsupported
        | pyset xs => exact .unsupported
    | countFrom cur step => simp only [execGen]; exact .ok h _


theorem ceExecStmt_succ (ih : CE fuel) : CEExecStmt (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, ihForG, ihDrain, ihAnyAll, ihClosure⟩ := ih
  intro m st s h
  cases s with
  | ret v sp =>
    cases v with
    | none => simp only [execStmt]; exact .ok h _
    | some e =>
      simp only [execStmt]
      exact .bind (ihE m st e h) fun s2 v hs2 => .ok hs2 _
  | assign targets value sp =>
    simp only [execStmt]
    cases hts : targets.toList with
    | nil => exact .unsupported
    | cons t rest =>
      cases rest with
      | cons t2 r2 => cases t <;> exact .unsupported
      | nil =>
        cases t <;>
          try (refine .bind (ihE m st value h) fun s2 v hs2 => ?_;
               ce_norm;
               exact .bind (.liftRes hs2 _) fun s3 env2 hs3 =>
                 .of_seed (fun tr => by simp)
                   (by simp only [FrameState.withClock_self hs3]))
        case subscript dE kE sp2 =>
          refine .bind (ihE m st value h) fun s2 v hs2 =>
            .bind (ihE m s2 dE hs2) fun s3 c hs3 =>
            .bind (ihE m s3 kE hs3) fun s4 k hs4 => ?_
          cases c <;> try exact .exn hs4 _
          case listV xs => exact .unsupported
          case ref a =>
            ce_norm
            exact .bind (.liftRes hs4 _) fun s5 h2 hs5 =>
              .of_seed (fun tr => by simp)
                (by simp only [FrameState.withClock_self hs5])
        case «attribute» recvE attr sp2 =>
          refine .bind (ihE m st value h) fun s2 v hs2 =>
            .bind (ihE m s2 recvE hs2) fun s3 r hs3 => ?_
          cases r <;> try exact .exn hs3 _
          case ref a =>
            ce_norm
            exact .bind (.liftRes hs3 _) fun s4 h2 hs4 =>
              .of_seed (fun tr => by simp)
                (by simp only [FrameState.withClock_self hs4])
        case tuple elts sp2 =>
          refine .ite ?_ ?_
          · refine .bind (ihE m st value h) fun s2 v hs2 => ?_
            ce_norm
            exact .bind (.liftRes hs2 _) fun s3 env2 hs3 =>
              .of_seed (fun tr => by simp)
                (by simp only [FrameState.withClock_self hs3])
          · refine .bind (ihE m st value h) fun s2 v hs2 => ?_
            ce_norm
            refine .bind (.liftRes hs2 _) fun s3 xs hs3 => ?_
            ce_norm
            refine .bind (.liftRes hs3 _) fun s4 he hs4 => ?_
            obtain ⟨h2, env2⟩ := he
            exact .of_seed (fun tr => by simp)
              (by simp only [FrameState.withClock_self hs4])
  | augAssign target op value sp =>
    simp only [execStmt]
    cases target <;> try exact .unsupported
    case name id sp2 =>
      ce_norm
      cases hl : Env.lookup st.locals id with
      | none => exact .exn h _
      | some v0 =>
        cases v0 <;> try
          exact .bind (ihE m st value h) fun s2 v hs2 =>
            .bind (.liftRes hs2 _) fun s3 r hs3 =>
              .of_seed (fun tr => by simp)
                (by simp only [FrameState.withClock_self hs3])
        case listV xs => exact .unsupported
        case ref a => exact .unsupported
    case «attribute» recvE attr sp2 =>
      refine .bind (ihE m st recvE h) fun s2 r hs2 => ?_
      cases r <;> try exact .exn hs2 _
      case ref a =>
        refine .bind (ceAttrReadResult hs2) fun s3 old hs3 => ?_
        cases old <;> try
          (refine .bind (ihE m s3 value hs3) fun s4 v hs4 => ?_;
           refine .bind (.liftRes hs4 _) fun s5 res hs5 => ?_;
           ce_norm;
           exact .bind (.liftRes hs5 _) fun s6 h2 hs6 =>
             .of_seed (fun tr => by simp)
               (by simp only [FrameState.withClock_self hs6]))
        case listV xs => exact .unsupported
        case ref a2 => exact .unsupported
  | whileLoop test body orelse sp =>
    simp only [execStmt]
    exact ihW m st test body.toList orelse.toList h
  | forStmt target iter body orelse sp =>
    simp only [execStmt]
    cases ho : orelse.toList with
    | cons o os => exact .unsupported
    | nil =>
      refine .bind (ihE m st iter h) fun s2 it hs2 => ?_
      cases it with
      | listV xs => exact ihFor m s2 target xs.toList body.toList hs2
      | tuple xs => exact ihFor m s2 target xs.toList body.toList hs2
      | ntuple tn fs xs => exact ihFor m s2 target xs.toList body.toList hs2
      | str sv => exact ihFor m s2 target (strCharVals sv) body.toList hs2
      | rangeV lo hi step =>
        exact .bind (.liftRes hs2 _) fun s3 xs hs3 =>
          ihFor m s3 target xs body.toList hs3
      | ref a => exact ihForL m s2 target a 0 body.toList hs2
      | none => exact .exn hs2 _
      | bool b => exact .exn hs2 _
      | int n => exact .exn hs2 _
  | ifStmt test body orelse sp =>
    simp only [execStmt]
    refine .bind (ihE m st test h) fun s2 t hs2 => ?_
    ce_norm
    refine .bind (.liftRes hs2 _) fun s3 b hs3 => ?_
    exact .ite (ihSs m s3 body.toList hs3) (ihSs m s3 orelse.toList hs3)
  | exprStmt e sp =>
    simp only [execStmt]
    exact .bind (ihE m st e h) fun s2 v hs2 => .ok hs2 _
  | yieldStmt e sp => simp only [execStmt]; exact .unsupported
  | yieldFromStmt e sp => simp only [execStmt]; exact .unsupported
  | defStmt name params argsOk localsOk hasGlobal isGenerator body captures sp =>
    simp only [execStmt]
    ce_norm
    cases hcap : capturesSnapshot st.locals captures.toList with
    | none => exact .unsupported
    | some cap =>
      exact .of_seed (fun tr => by simp) (by simp [h])
  | raiseStmt exc cause sp =>
    simp only [execStmt]
    ce_norm
    cases cause with
    | some c => exact .unsupported
    | none =>
      cases exc with
      | none => exact .unsupported
      | some e2 =>
        cases e2 <;> try exact .unsupported
        case name id sp2 =>
          refine .ite .unsupported ?_
          cases hfc : findClass m id with
          | none => exact .unsupported
          | some pr =>
            cases pr with
            | mk ci cdef => exact .ite (.exn h _) .unsupported
  | tryStmt body excName handler tryUnsupported sp =>
    simp only [execStmt]
    ce_norm
    cases tryUnsupported with
    | some reason => exact .unsupported
    | none =>
      refine .ite .unsupported ?_
      cases hfc : findClass m excName with
      | none => exact .unsupported
      | some pr =>
        cases pr with
        | mk ci cdef =>
          dsimp only
          refine .ite .unsupported ?_
          obtain ⟨hok, hexn, hto⟩ := ihSs m st body.toList h
          cases hrun : execStmts m fuel st body.toList with
          | ok s2 fl =>
            obtain ⟨h2, hy⟩ := hok s2 fl hrun
            simp only [hy]
            exact .ok h2 _
          | exn s2 e =>
            obtain ⟨h2, hy⟩ := hexn s2 e hrun
            simp only [hy]
            cases e <;> try exact .exn h2 _
            case user cid nm =>
              exact .ite (ihSs m s2 handler.toList h2) (.exn h2 _)
          | timeout =>
            simp only [hto hrun]
            exact .timeout
          | unsupported msg => exact .unsupported
  | pass sp => simp only [execStmt]; exact .ok h _
  | brk sp => simp only [execStmt]; exact .ok h _
  | cont sp => simp only [execStmt]; exact .ok h _
  | unsupported pyKind txt sp => simp only [execStmt]; exact .unsupported


theorem ceExecAttrCall_succ (ih : CE fuel) : CEExecAttrCall (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, -⟩ := ih
  intro m st a attr args h
  simp only [execAttrCall]
  ce_norm
  cases hp : attrCallPlan m st.world.heap a attr with
  | instMethod qname =>
    refine .bind (ihEs m st args h) fun s2 vs hs2 => ?_
    ce_norm
    exact ClockErasedW.withLocals (ihCall m s2.world qname _ hs2)
  | instAttrValue => exact .unsupported
  | attrMissing => exact .exn h _
  | dictGet =>
    refine .bind (ihEs m st args h) fun s2 vs hs2 => ?_
    cases vs with
    | nil => exact .exn hs2 _
    | cons k t =>
      cases t with
      | nil => ce_norm; exact .liftRes hs2 _
      | cons d t2 =>
        cases t2 with
        | nil => ce_norm; exact .liftRes hs2 _
        | cons e t3 => exact .exn hs2 _
  | dictClear =>
    refine .bind (ihEs m st args h) fun s2 vs hs2 => ?_
    cases vs with
    | cons v t => exact .exn hs2 _
    | nil =>
      refine .of_seed (fun tr => ?_)
        (by simp only [FrameState.withClock_self hs2])
      ce_norm
      cases hg : Heap.get? s2.world.heap a with
      | none => simp
      | some obj =>
        cases obj <;> try simp
        case dict entries ver =>
          cases hu : Heap.update s2.world.heap a (.dict #[] (ver + 1)) <;> simp
  | listAppend =>
    refine .bind (ihEs m st args h) fun s2 vs hs2 => ?_
    cases vs with
    | nil => exact .exn hs2 _
    | cons v t =>
      cases t with
      | cons d t2 => exact .exn hs2 _
      | nil =>
        ce_norm
        exact .bind (.liftRes hs2 _) fun s3 h2 hs3 =>
          .of_seed (fun tr => by simp)
            (by simp only [FrameState.withClock_self hs3])
  | listPop =>
    refine .bind (ihEs m st args h) fun s2 vs hs2 => ?_
    cases vs with
    | nil =>
      dsimp only
      ce_norm
      refine .bind (.liftRes hs2 _) fun s3 hr hs3 => ?_
      obtain ⟨h2, v2⟩ := hr
      exact .of_seed (fun tr => by simp)
        (by simp only [FrameState.withClock_self hs3])
    | cons i t =>
      cases t with
      | cons d t2 => exact .exn hs2 _
      | nil =>
        dsimp only
        cases hai : asInt i with
        | none => exact .exn hs2 _
        | some n =>
          ce_norm
          refine .bind (.liftRes hs2 _) fun s3 hr hs3 => ?_
          obtain ⟨h2, v2⟩ := hr
          exact .of_seed (fun tr => by simp)
            (by simp only [FrameState.withClock_self hs3])
  | refuse msg => exact .unsupported
  | dangling => exact .unsupported


set_option maxHeartbeats 1600000 in
theorem ceEvalExpr_succ (ih : CE fuel) : CEEvalExpr (fuel + 1) := by
  obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
    ihAttrC, ihStep, ihGen, ihForG, ihDrain, ihAnyAll, ihClosure⟩ := ih
  intro m st e h
  cases e with
  | constant cv sp => simp only [evalExpr]; exact .ok h _
  | name id sp =>
    simp only [evalExpr]
    ce_norm
    cases hl : Env.lookup st.locals id with
    | some v => exact .ok h _
    | none =>
      cases hg : lookupG (moduleGlobals m).1 id with
      | some ov =>
        cases ov with
        | some v => exact .ok h _
        | none =>
          cases hlive : Env.lookup st.world.globals id with
          | some v => exact .ok h _
          | none => exact .unsupported
      | none =>
        refine .ite .unsupported (.ite .unsupported (.ite .unsupported
          (.ite .unsupported (.ite .unsupported ?_))))
        cases hlive : Env.lookup st.world.globals id with
        | some v => exact .ok h _
        | none => exact .ite .unsupported (.ite (.exn h _) .unsupported)
  | binOp l op r sp =>
    simp only [evalExpr]
    exact .bind (ihE m st l h) fun s1 a hs1 =>
      .bind (ihE m s1 r hs1) fun s2 b hs2 => .liftRes hs2 _
  | unaryOp op operand sp =>
    simp only [evalExpr]
    refine .bind (ihE m st operand h) fun s1 v hs1 => ?_
    ce_norm
    exact .liftRes hs1 _
  | boolOp op values sp =>
    simp only [evalExpr]
    cases values.toList with
    | nil => exact .unsupported
    | cons e0 es => exact ihB m st op e0 es h
  | compare l ops comparators sp =>
    simp only [evalExpr]
    exact .bind (ihE m st l h) fun s1 a hs1 =>
      ihC m s1 a ops.toList comparators.toList hs1
  | list elts sp =>
    simp only [evalExpr]
    refine .bind (ihEs m st elts.toList h) fun s2 vs hs2 => ?_
    exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs2, hs2])
  | tuple elts sp =>
    simp only [evalExpr]
    exact .bind (ihEs m st elts.toList h) fun s2 vs hs2 => .ok hs2 _
  | subscript v idx sp =>
    simp only [evalExpr]
    refine .bind (ihE m st v h) fun s1 cv hs1 =>
      .bind (ihE m s1 idx hs1) fun s2 i hs2 => ?_
    ce_norm
    exact .liftRes hs2 _
  | dict keys values sp =>
    simp only [evalExpr]
    refine .bind (ihItems m st keys.toList values.toList h) fun s2 items hs2 => ?_
    ce_norm
    refine .bind (.liftRes hs2 _) fun s3 entries hs3 => ?_
    exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs3, hs3])
  | «attribute» recv attr sp =>
    simp only [evalExpr]
    refine .bind (ihE m st recv h) fun s2 r hs2 => ?_
    cases r <;> try exact .unsupported
    case ref a => exact ceAttrReadResult hs2
    case ntuple tn fields xs => exact .liftRes hs2 _
  | ifExp t b o sp =>
    simp only [evalExpr]
    refine .bind (ihE m st t h) fun s1 tv hs1 => ?_
    ce_norm
    refine .bind (.liftRes hs1 _) fun s2 cond hs2 => ?_
    exact .ite (ihE m s2 b hs2) (ihE m s2 o hs2)
  | slice v l u stp sp =>
    simp only [evalExpr]
    exact .bind (ihE m st v h) fun s1 cv hs1 =>
      .bind (ihE m s1 l hs1) fun s2 lv hs2 =>
      .bind (ihE m s2 u hs2) fun s3 uv hs3 =>
      .bind (ihE m s3 stp hs3) fun s4 sv hs4 => .liftRes hs4 _
  | genExp elt target iter ifs wb sp => simp only [evalExpr]; exact .unsupported
  | unsupported pyKind txt sp => simp only [evalExpr]; exact .unsupported
  | call f args kwargs cu sp =>
    cases cu with
    | some reason => simp only [evalExpr]; exact .unsupported
    | none =>
      simp only [evalExpr]
      ce_norm
      refine .ite ?pos ?kw
      case pos =>
        cases f <;> try exact .unsupported
        case name fname sp2 =>
          ce_norm
          cases hl : Env.lookup st.locals fname with
          | some v0 =>
            cases v0 <;> try
              exact .bind (ihEs m st args.toList h) fun s2 vs hs2 => .exn hs2 _
            case ref a =>
              refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
              refine .ite (.exn hs2 _) ?_
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .exn hs2 _
              | some obj =>
                cases obj <;> try exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap =>
                  ce_norm
                  exact ClockErasedW.withLocals
                    (ihClosure m s2.world nm ps ao lo ig bd cap vs.toArray hs2)
          | none =>
            cases hg : lookupG (moduleGlobals m).1 fname with
            | some ov =>
              cases ov with
              | some vv =>
                cases vv <;>
                  exact .bind (ihEs m st args.toList h) fun s2 vs hs2 => .exn hs2 _
              | none =>
                cases hlive : Env.lookup st.world.globals fname with
                | none => exact .unsupported
                | some lv =>
                  cases lv <;> try
                    exact .bind (ihEs m st args.toList h) fun s2 vs hs2 => .exn hs2 _
                  case ref a =>
                    refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                    refine .ite (.exn hs2 _) ?_
                    ce_norm
                    cases hh : Heap.get? s2.world.heap a with
                    | none => exact .exn hs2 _
                    | some obj =>
                      cases obj <;> try exact .exn hs2 _
                      case closure nm ps ao lo hg2 ig bd cap =>
                        ce_norm
                        exact ClockErasedW.withLocals
                          (ihClosure m s2.world nm ps ao lo ig bd cap vs.toArray hs2)
            | none =>
              refine .ite (.ite .unsupported ?fcall) ?classes
              case fcall =>
                refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                ce_norm
                exact ClockErasedW.withLocals (ihCall m s2.world fname vs.toArray hs2)
              case classes =>
                cases hfc : findClass m fname with
                | some pr =>
                  obtain ⟨ci, cdef⟩ := pr
                  try dsimp only
                  refine .ite .unsupported (.ite .unsupported ?ntb)
                  case ntb =>
                    cases hnb : cdef.ntBase with
                    | some nt =>
                      refine .ite .unsupported (.ite .unsupported (.ite .unsupported ?ctor))
                      case ctor =>
                        exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                          .ite (.ok hs2 _) (.exn hs2 _)
                    | none =>
                      refine .ite .unsupported (.ite .unsupported ?inst)
                      case inst =>
                        refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                        try dsimp only
                        ce_norm
                        refine .ite ?init ?noinit
                        case init =>
                          refine .bind
                            (ClockErasedW.withLocals
                              (ihCall m _ (fname ++ ".__init__") _ hs2))
                            fun s3 r hs3 => ?_
                          cases r <;> try exact .exn hs3 _
                          case none => exact .ok hs3 _
                        case noinit =>
                          cases vs with
                          | nil =>
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [hs2])
                          | cons v t => exact .exn hs2 _
                | none =>
                  cases hnt : findNamedTuple m fname with
                  | some nt =>
                    exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                      .ite (.ok hs2 _) (.exn hs2 _)
                  | none =>
                    refine .ite ?blen (.ite ?bsorted (.ite ?bmax (.ite ?bmin
                      (.ite ?banyall (.ite ?bset (.ite ?babs (.ite ?bint
                      (.ite ?bsum (.ite ?btuple (.ite ?brange (.ite ?benum
                      (.ite ?bcount (.ite ?bnext (.ite ?bord (.ite ?bchr
                      (.ite ?bstr (.ite .unsupported (.ite .unsupported
                        (.ite .unsupported ?blive)))))))))))))))))))
                    case blen =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | nil => ce_norm; exact .liftRes hs2 _
                        | cons d t2 => exact .exn hs2 _
                    case bsorted =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | cons d t2 => exact .exn hs2 _
                        | nil =>
                          cases v
                          case none =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case bool b =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case int n =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case str s0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case tuple xs0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case listV xs0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case ntuple tn0 fs0 xs0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case rangeV lo0 hi0 st0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                            obtain ⟨h9, r9⟩ := hr
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case ref a =>
                            ce_norm
                            cases hh : Heap.get? s2.world.heap a with
                            | some obj =>
                              cases obj
                              case list xs0 =>
                                ce_norm
                                refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                                obtain ⟨h9, r9⟩ := hr
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                              case dict entries ver =>
                                ce_norm
                                refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                                obtain ⟨h9, r9⟩ := hr
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                              case «instance» cid attrs =>
                                ce_norm
                                refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                                obtain ⟨h9, r9⟩ := hr
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                              case closure nm ps ao lo hg2 ig bd cap =>
                                ce_norm
                                refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                                obtain ⟨h9, r9⟩ := hr
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                              case pyset xs0 =>
                                ce_norm
                                refine .bind (.liftRes hs2 _) fun s9 hr hs9 => ?_
                                obtain ⟨h9, r9⟩ := hr
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                              case generator qn l k stat =>
                                refine .bind
                                  (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                                  fun s3 vals hs3 => ?_
                                ce_norm
                                refine .bind (.liftRes hs3 _) fun s4 sorted2 hs4 => ?_
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs4, hs4])
                            | none =>
                              ce_norm
                              refine .bind (.liftRes hs2 _) fun s3 hr hs3 => ?_
                              obtain ⟨h2, r2⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs3, hs3])
                    case bmax =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => ce_norm; exact .liftRes hs2 _
                      | cons v t =>
                        cases t with
                        | cons d t2 => ce_norm; exact .liftRes hs2 _
                        | nil =>
                          cases v <;> try (ce_norm; exact .liftRes hs2 _)
                          case ref a =>
                            ce_norm
                            cases hh : Heap.get? s2.world.heap a with
                            | none => ce_norm; exact .liftRes hs2 _
                            | some obj =>
                              cases obj <;> try (ce_norm; exact .liftRes hs2 _)
                              case generator qn l k stat =>
                                refine .ite .unsupported ?_
                                refine .bind
                                  (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                                  fun s3 vals hs3 => ?_
                                exact .liftRes hs3 _
                    case bmin =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => ce_norm; exact .liftRes hs2 _
                      | cons v t =>
                        cases t with
                        | cons d t2 => ce_norm; exact .liftRes hs2 _
                        | nil =>
                          cases v <;> try (ce_norm; exact .liftRes hs2 _)
                          case ref a =>
                            ce_norm
                            cases hh : Heap.get? s2.world.heap a with
                            | none => ce_norm; exact .liftRes hs2 _
                            | some obj =>
                              cases obj <;> try (ce_norm; exact .liftRes hs2 _)
                              case generator qn l k stat =>
                                refine .ite .unsupported ?_
                                refine .bind
                                  (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                                  fun s3 vals hs3 => ?_
                                exact .liftRes hs3 _
                    case banyall =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | cons d t2 => exact .exn hs2 _
                        | nil =>
                          cases v <;> try (ce_norm; exact .liftRes hs2 _)
                          case none => exact .exn hs2 _
                          case bool b => exact .exn hs2 _
                          case int n => exact .exn hs2 _
                          case ref a =>
                            ce_norm
                            cases hh : Heap.get? s2.world.heap a with
                            | none => exact .unsupported
                            | some obj =>
                              cases obj <;> try exact .unsupported
                              case list xs => ce_norm; exact .liftRes hs2 _
                              case «instance» cid attrs => exact .exn hs2 _
                              case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                              case generator qn l k stat =>
                                refine .bind
                                  (ClockErasedW.withLocals (ihAnyAll m s2.world a _ hs2))
                                  fun s3 b hs3 => ?_
                                exact .ok hs3 _
                    case bset =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil =>
                        exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs2, hs2])
                      | cons v t =>
                        cases t with
                        | cons d t2 => exact .exn hs2 _
                        | nil =>
                          cases v
                          case str s0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 es hs9 => ?_
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case tuple xs0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 es hs9 => ?_
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case ntuple tn0 fs0 xs0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 es hs9 => ?_
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case listV xs0 =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s9 es hs9 => ?_
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                          case none => exact .exn hs2 _
                          case bool b => exact .exn hs2 _
                          case int n => exact .exn hs2 _
                          case rangeV lo hi step =>
                            ce_norm
                            refine .bind (.liftRes hs2 _) fun s3 xs hs3 => ?_
                            ce_norm
                            refine .bind (.liftRes hs3 _) fun s4 es hs4 => ?_
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs4, hs4])
                          case ref a =>
                            ce_norm
                            cases hh : Heap.get? s2.world.heap a with
                            | none => exact .unsupported
                            | some obj =>
                              cases obj <;> try exact .unsupported
                              case list xs =>
                                ce_norm
                                refine .bind (.liftRes hs2 _) fun s3 es hs3 => ?_
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs3, hs3])
                              case pyset xs =>
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [hs2])
                              case «instance» cid attrs => exact .exn hs2 _
                              case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                              case generator qn l k stat =>
                                refine .bind
                                  (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                                  fun s3 vals hs3 => ?_
                                ce_norm
                                refine .bind (.liftRes hs3 _) fun s4 es hs4 => ?_
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs4, hs4])
                    case babs =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | nil => exact .liftRes hs2 _
                        | cons d t2 => exact .exn hs2 _
                    case bint =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .ok hs2 _
                      | cons v t =>
                        cases t with
                        | nil => exact .liftRes hs2 _
                        | cons d t2 => exact .unsupported
                    case bsum =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases hsa : sumArgs vs with
                      | none => exact .exn hs2 _
                      | some pr =>
                        obtain ⟨v, start⟩ := pr
                        try dsimp only
                        cases start with
                        | str s0 => exact .exn hs2 _
                        | none =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | bool b0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | int n0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | tuple xs0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | listV xs0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | ntuple tn0 fs0 xs0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | rangeV lo0 hi0 st0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                        | ref a0 =>
            cases v <;> try exact .liftRes hs2 _
            case ref a =>
              ce_norm
              cases hh : Heap.get? s2.world.heap a with
              | none => exact .unsupported
              | some obj =>
                cases obj <;> try exact .unsupported
                case list xs => exact .liftRes hs2 _
                case «instance» cid attrs => exact .exn hs2 _
                case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                case generator qn l k stat =>
                  refine .ite .unsupported ?_
                  refine .bind (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                    fun s3 vals hs3 => ?_
                  exact .liftRes hs3 _
            case none => exact .exn hs2 _
            case bool b => exact .exn hs2 _
            case int n => exact .exn hs2 _
                    case btuple =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .ok hs2 _
                      | cons v t =>
                        cases t with
                        | cons d t2 => exact .exn hs2 _
                        | nil =>
                          cases v <;> try exact .ok hs2 _
                          case none => exact .exn hs2 _
                          case bool b => exact .exn hs2 _
                          case int n => exact .exn hs2 _
                          case rangeV lo hi step => exact .liftRes hs2 _
                          case ref a =>
                            ce_norm
                            cases hh : Heap.get? s2.world.heap a with
                            | none => exact .unsupported
                            | some obj =>
                              cases obj <;> try exact .unsupported
                              case list xs => exact .ok hs2 _
                              case «instance» cid attrs => exact .exn hs2 _
                              case closure nm ps ao lo hg2 ig bd cap => exact .exn hs2 _
                              case generator qn l k stat =>
                                refine .ite .unsupported ?_
                                refine .bind
                                  (ClockErasedW.withLocals (ihDrain m s2.world a hs2))
                                  fun s3 vals hs3 => ?_
                                exact .ok hs3 _
                    case brange =>
                      exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                        .liftRes hs2 _
                    case benum =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v rest =>
                        dsimp only
                        cases hes : enumStart rest with
                        | none => exact .ite (.exn hs2 _) (.exn hs2 _)
                        | some i0 =>
                          ce_norm
                          cases hef : enumFrame s2.world.heap i0 v with
                          | ok fr =>
                            exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [hs2])
                          | exn e2 => exact .exn hs2 _
                          | timeout => exact .timeout
                          | unsupported msg => exact .unsupported
                    case bcount =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases hca : countArgs vs with
                      | none => exact .exn hs2 _
                      | some pr =>
                        obtain ⟨start, step⟩ := pr
                        exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs2, hs2])
                    case bnext =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | nil =>
                          try dsimp only
                          cases v <;> try (ce_norm; exact .exn hs2 _)
                          case ref a =>
                            ce_norm
                            refine .bind
                              (ClockErasedW.withLocals (ihStep m s2.world a hs2))
                              fun s3 r hs3 => ?_
                            cases r with
                            | some v2 => exact .ok hs3 _
                            | none => exact .exn hs3 _
                        | cons d t2 =>
                          cases t2 with
                          | cons d2 t3 => ce_norm; exact .exn hs2 _
                          | nil =>
                            try dsimp only
                            cases v <;> try (ce_norm; exact .exn hs2 _)
                            case ref a =>
                              ce_norm
                              refine .bind
                                (ClockErasedW.withLocals (ihStep m s2.world a hs2))
                                fun s3 r hs3 => ?_
                              cases r with
                              | some v2 => exact .ok hs3 _
                              | none => exact .ok hs3 _
                    case bord =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | nil => exact .liftRes hs2 _
                        | cons d t2 => exact .exn hs2 _
                    case bchr =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .exn hs2 _
                      | cons v t =>
                        cases t with
                        | nil => exact .liftRes hs2 _
                        | cons d t2 => exact .exn hs2 _
                    case bstr =>
                      refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                      cases vs with
                      | nil => exact .ok hs2 _
                      | cons v t =>
                        cases t with
                        | nil => exact .liftRes hs2 _
                        | cons d t2 => exact .unsupported
                    case blive =>
                      cases hlive : Env.lookup st.world.globals fname with
                      | none => exact .ite .unsupported (.ite (.exn h _) .unsupported)
                      | some lv =>
                        cases lv <;> try
                          exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                            .exn hs2 _
                        case ref a =>
                          refine .bind (ihEs m st args.toList h) fun s2 vs hs2 => ?_
                          refine .ite (.exn hs2 _) ?_
                          ce_norm
                          cases hh : Heap.get? s2.world.heap a with
                          | none => exact .exn hs2 _
                          | some obj =>
                            cases obj <;> try exact .exn hs2 _
                            case closure nm ps ao lo hg2 ig bd cap =>
                              ce_norm
                              exact ClockErasedW.withLocals
                                (ihClosure m s2.world nm ps ao lo ig bd cap
                                  vs.toArray hs2)
        case «attribute» recv attr sp2 =>
          refine .ite ?clock ?dispatch
          case clock =>
            cases hargs : args.toList with
            | cons a0 t => exact .unsupported
            | nil =>
              simp only [h]
              exact .unsupported
          case dispatch =>
            refine .bind (ihE m st recv h) fun s2 r hs2 => ?_
            cases r <;> try exact .unsupported
            case ref a => exact ihAttrC m s2 a attr args.toList hs2
            case ntuple tn fs xs =>
              try dsimp only
              cases hp : ntupleCallPlan m tn fs attr with
              | instMethod qname =>
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 => ?_
                ce_norm
                exact ClockErasedW.withLocals (ihCall m s3.world qname _ hs3)
              | attrMissing => exact .exn hs2 _
              | refuse msg => exact .unsupported
              | instAttrValue => exact .unsupported
              | dictGet => exact .unsupported
              | dictClear => exact .unsupported
              | listAppend => exact .unsupported
              | listPop => exact .unsupported
              | dangling => exact .unsupported
            case str sv =>
              try dsimp only
              cases hp : strCallPlan attr with
              | swapcase =>
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 => ?_
                cases vs with
                | nil => exact .liftRes hs3 _
                | cons v t => exact .exn hs3 _
              | isupper =>
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 => ?_
                cases vs with
                | nil => exact .liftRes hs3 _
                | cons v t => exact .exn hs3 _
              | islower =>
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 => ?_
                cases vs with
                | nil => exact .liftRes hs3 _
                | cons v t => exact .exn hs3 _
              | upper =>
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 => ?_
                cases vs with
                | nil => exact .liftRes hs3 _
                | cons v t => exact .exn hs3 _
              | index =>
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 => ?_
                cases vs with
                | nil => exact .exn hs3 _
                | cons v t =>
                  cases t with
                  | nil =>
                    cases v <;> try (ce_norm; exact .exn hs3 _)
                    case str sub => exact .liftRes hs3 _
                  | cons d t2 => cases v <;> exact .ite .unsupported (.exn hs3 _)
              | refuse msg => exact .unsupported
      case kw =>
        cases f <;> try exact .unsupported
        case name fname sp2 =>
          ce_norm
          cases hl : Env.lookup st.locals fname with
          | some v0 =>
            cases v0 <;> try
              exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                .bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2) fun s3 kvs hs3 =>
                  .exn hs3 _
            case ref a =>
              refine .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                .bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2) fun s3 kvs hs3 => ?_
              ce_norm
              cases hh : Heap.get? s3.world.heap a with
              | none => exact .exn hs3 _
              | some obj =>
                cases obj <;> try exact .exn hs3 _
                case closure nm ps ao lo hg2 ig bd cap => exact .unsupported
          | none =>
            cases hg : lookupG (moduleGlobals m).1 fname with
            | some ov =>
              cases ov with
              | some vv =>
                cases vv <;>
                  exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                    .bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2) fun s3 kvs hs3 =>
                      .exn hs3 _
              | none => exact .unsupported
            | none =>
              cases hff : findFunction m fname with
              | some fdefn =>
                try dsimp only
                refine .ite .unsupported (.ite .unsupported ?merge)
                case merge =>
                  refine .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                    .bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2) fun s3 kvs hs3 => ?_
                  refine .bind (.liftRes hs3 _) fun s4 full hs4 => ?_
                  ce_norm
                  exact ClockErasedW.withLocals (ihCall m s4.world fname full hs4)
              | none =>
                refine .ite .unsupported (.ite .unsupported
                  (.ite ?bsortedkw (.ite .unsupported (.ite .unsupported ?livekw))))
                case bsortedkw =>
                  refine .ite .unsupported ?_
                  cases hfk : kwargs.toList.find? (fun kv => kv.1 != "reverse") with
                  | some kv =>
                    obtain ⟨k0, v0⟩ := kv
                    exact .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                      .bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2) fun s3 kvs hs3 =>
                        .exn hs3 _
                  | none =>
                    refine .bind (ihEs m st args.toList h) fun s2 vs hs2 =>
                      .bind (ihEs m s2 (kwargs.toList.map (·.2)) hs2) fun s3 kvs hs3 => ?_
                    cases vs with
                    | nil => exact .exn hs3 _
                    | cons v t =>
                      cases t with
                      | cons d t2 => exact .exn hs3 _
                      | nil =>
                        cases kvs with
                        | nil => exact .unsupported
                        | cons rv t2 =>
                          cases t2 with
                          | cons rv2 t3 => exact .unsupported
                          | nil =>
                            ce_norm
                            refine .bind (.liftRes hs3 _) fun s4 desc hs4 => ?_
                            cases v
                            case none =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case bool b =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case int n =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case str s0 =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case tuple xs0 =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case listV xs0 =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case ntuple tn0 fs0 xs0 =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case rangeV lo0 hi0 st0 =>
                              ce_norm
                              refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                              obtain ⟨h9, r9⟩ := hr
                              exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                            case ref a =>
                              ce_norm
                              cases hh : Heap.get? s4.world.heap a with
                              | some obj =>
                                cases obj
                                case list xs0 =>
                                  ce_norm
                                  refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                                  obtain ⟨h9, r9⟩ := hr
                                  exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                                case dict entries ver =>
                                  ce_norm
                                  refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                                  obtain ⟨h9, r9⟩ := hr
                                  exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                                case «instance» cid attrs =>
                                  ce_norm
                                  refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                                  obtain ⟨h9, r9⟩ := hr
                                  exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                                case closure nm ps ao lo hg2 ig bd cap =>
                                  ce_norm
                                  refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                                  obtain ⟨h9, r9⟩ := hr
                                  exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                                case pyset xs0 =>
                                  ce_norm
                                  refine .bind (.liftRes hs4 _) fun s9 hr hs9 => ?_
                                  obtain ⟨h9, r9⟩ := hr
                                  exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs9, hs9])
                                case generator qn l k stat =>
                                  refine .bind
                                    (ClockErasedW.withLocals (ihDrain m s4.world a hs4))
                                    fun s5 vals hs5 => ?_
                                  ce_norm
                                  refine .bind (.liftRes hs5 _) fun s6 sorted2 hs6 => ?_
                                  exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs6, hs6])
                              | none =>
                                ce_norm
                                refine .bind (.liftRes hs4 _) fun s5 hr hs5 => ?_
                                obtain ⟨h2, r2⟩ := hr
                                exact .of_seed (fun tr => by first | rfl | simp) (by first | rfl | simp [FrameState.withClock_self hs5, hs5])
                case livekw =>
                  cases hlive : Env.lookup st.world.globals fname with
                  | some lv => exact .unsupported
                  | none => exact .ite .unsupported (.ite (.exn h _) .unsupported)
        case «attribute» recv attr sp2 =>
          refine .bind (ihE m st recv h) fun s2 r hs2 => ?_
          cases r <;> try (ce_norm; exact .unsupported)
          case ref a =>
            ce_norm
            cases hp : attrCallPlan m s2.world.heap a attr with
            | instMethod qname =>
              try dsimp only
              cases hff : findFunction m qname with
              | none => exact .unsupported
              | some fdefn =>
                try dsimp only
                refine .ite .unsupported ?_
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 =>
                  .bind (ihEs m s3 (kwargs.toList.map (·.2)) hs3) fun s4 kvs hs4 => ?_
                refine .bind (.liftRes hs4 _) fun s5 full hs5 => ?_
                ce_norm
                exact ClockErasedW.withLocals (ihCall m s5.world qname full hs5)
            | instAttrValue => exact .unsupported
            | attrMissing => exact .exn hs2 _
            | dictGet => exact .unsupported
            | dictClear => exact .unsupported
            | listAppend => exact .unsupported
            | listPop => exact .unsupported
            | refuse msg => exact .unsupported
            | dangling => exact .unsupported
          case ntuple tn fs xs =>
            try dsimp only
            cases hp : ntupleCallPlan m tn fs attr with
            | instMethod qname =>
              try dsimp only
              cases hff : findFunction m qname with
              | none => exact .unsupported
              | some fdefn =>
                try dsimp only
                refine .ite .unsupported ?_
                refine .bind (ihEs m s2 args.toList hs2) fun s3 vs hs3 =>
                  .bind (ihEs m s3 (kwargs.toList.map (·.2)) hs3) fun s4 kvs hs4 => ?_
                refine .bind (.liftRes hs4 _) fun s5 full hs5 => ?_
                ce_norm
                exact ClockErasedW.withLocals (ihCall m s5.world qname full hs5)
            | attrMissing => exact .exn hs2 _
            | refuse msg => exact .unsupported
            | instAttrValue => exact .unsupported
            | dictGet => exact .unsupported
            | dictClear => exact .unsupported
            | listAppend => exact .unsupported
            | listPop => exact .unsupported
            | dangling => exact .unsupported


/-- The zero-fuel base: every member is `.timeout`, the relation's bottom. -/
theorem ceZero : CE 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m st e _ => by simp only [evalExpr]; exact .timeout
  · exact fun m st es _ => by simp only [evalExprs]; exact .timeout
  · exact fun m st op e rest _ => by simp only [evalBoolChain]; exact .timeout
  · exact fun m st lhs ops cs _ => by simp only [evalCompareChain]; exact .timeout
  · exact fun m st s _ => by simp only [execStmt]; exact .timeout
  · exact fun m st ss _ => by simp only [execStmts]; exact .timeout
  · exact fun m st test body orelse _ => by simp only [execWhile]; exact .timeout
  · exact fun m w fname args _ => by simp only [callIn]; exact .timeout
  · exact fun m st target xs body _ => by simp only [execFor]; exact .timeout
  · exact fun m st keys values _ => by simp only [evalDictItems]; exact .timeout
  · exact fun m st target a i body _ => by simp only [execForList]; exact .timeout
  · exact fun m st a attr args _ => by simp only [execAttrCall]; exact .timeout
  · exact fun m w a _ => by simp only [stepIter]; exact .timeout
  · exact fun m st k _ => by simp only [execGen]; exact .timeout
  · exact fun m st target a body _ => by simp only [execForGen]; exact .timeout
  · exact fun m w a _ => by simp only [drainIter]; exact .timeout
  · exact fun m w a isAll _ => by simp only [anyAllIter]; exact .timeout
  · exact fun m w name params ao lo ig body cap args _ => by
      simp only [callClosure]; exact .timeout

/-- **CLOCK ERASURE** (docs/memory-model.md §clock erasure): for every
interpreter function and every input whose world carries the EMPTY clock
trace, the run is trace-independent — decided (`.ok`/`.exn`) and
timed-out outcomes are identical under every seeded trace, which rides
through untouched. One conjunction over the mutual block, by induction on
fuel, mirroring `fuelMono` arm for arm. -/
theorem clockErase : ∀ fuel, CE fuel := by
  intro fuel
  induction fuel with
  | zero => exact ceZero
  | succ fuel ih =>
    exact ⟨ceEvalExpr_succ ih, ceEvalExprs_succ ih, ceEvalBoolChain_succ ih,
      ceEvalCompareChain_succ ih, ceExecStmt_succ ih, ceExecStmts_succ ih,
      ceExecWhile_succ ih, ceCallIn_succ ih, ceExecFor_succ ih,
      ceEvalDictItems_succ ih, ceExecForList_succ ih, ceExecAttrCall_succ ih,
      ceStepIter_succ ih, ceExecGen_succ ih, ceExecForGen_succ ih,
      ceDrainIter_succ ih, ceAnyAllIter_succ ih, ceCallClosure_succ ih⟩

/-! ### Per-member projections (the fuelMono `_mono` discipline):
consume the induction through these, never by hand-counting `.2`s. -/

theorem evalExpr_clockErased (fuel : Nat) : CEEvalExpr fuel :=
  (clockErase fuel).1

theorem evalExprs_clockErased (fuel : Nat) : CEEvalExprs fuel :=
  (clockErase fuel).2.1

theorem evalBoolChain_clockErased (fuel : Nat) : CEEvalBoolChain fuel :=
  (clockErase fuel).2.2.1

theorem evalCompareChain_clockErased (fuel : Nat) : CEEvalCompareChain fuel :=
  (clockErase fuel).2.2.2.1

theorem execStmt_clockErased (fuel : Nat) : CEExecStmt fuel :=
  (clockErase fuel).2.2.2.2.1

theorem execStmts_clockErased (fuel : Nat) : CEExecStmts fuel :=
  (clockErase fuel).2.2.2.2.2.1

theorem execWhile_clockErased (fuel : Nat) : CEExecWhile fuel :=
  (clockErase fuel).2.2.2.2.2.2.1

theorem callIn_clockErased (fuel : Nat) : CECallIn fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.1

theorem execFor_clockErased (fuel : Nat) : CEExecFor fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.1

theorem evalDictItems_clockErased (fuel : Nat) : CEEvalDictItems fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.1

theorem execForList_clockErased (fuel : Nat) : CEExecForList fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.1

theorem execAttrCall_clockErased (fuel : Nat) : CEExecAttrCall fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.1

theorem stepIter_clockErased (fuel : Nat) : CEStepIter fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem execGen_clockErased (fuel : Nat) : CEExecGen fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem execForGen_clockErased (fuel : Nat) : CEExecForGen fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem drainIter_clockErased (fuel : Nat) : CEDrainIter fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem anyAllIter_clockErased (fuel : Nat) : CEAnyAllIter fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem callClosure_clockErased (fuel : Nat) : CECallClosure fuel :=
  (clockErase fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The public boundary corollaries -/

/-- `initWorld` never seeds a clock (the empty trace is the pinned-file
regime; a boundary seeds it explicitly — `callFunctionClock`). -/
theorem initWorld_clock (m : Module) : (initWorld m).clock = [] := by
  unfold initWorld
  cases initFoldLive m initExecFuel #[] [] #[] m.topLevel.toList
  rfl

/-- The `[]`-boundary identity, propositionally: `callFunctionClock` at
the EMPTY trace is `callFunction` — `initWorld` carries `clock = []`,
so re-seeding `[]` is the identity (`World.withClock_self`). -/
theorem callFunctionClock_nil {m : Module} {f : String} {args : Array Val}
    {fuel : Nat} :
    callFunctionClock m f args [] fuel = callFunction m f args fuel := by
  unfold callFunctionClock callFunction
  rw [show ({ initWorld m with clock := [] } : World) =
        (initWorld m).withClock [] from rfl,
      World.withClock_self (initWorld_clock m)]

/-- Transport a decided-`.ok` public call to EVERY seeded trace:
`callFunction` is `callFunctionClock` at `[]`, and a run decided from the
empty trace never consulted the clock. -/
theorem callFunctionClock_ok {m : Module} {fname : String} {args : Array Val}
    {fuel : Nat} {v : Val}
    (h : callFunction m fname args fuel = .ok v) (tr : List Int) :
    callFunctionClock m fname args tr fuel = .ok v := by
  obtain ⟨hok, hexn, hto⟩ :=
    callIn_clockErased fuel m (initWorld m) fname (RVal.thawArgs args)
      (initWorld_clock m)
  unfold callFunction at h
  unfold callFunctionClock
  rw [show ({ initWorld m with clock := tr } : World) = (initWorld m).withClock tr
    from rfl]
  cases hrun : callIn m fuel (initWorld m) fname (RVal.thawArgs args) with
  | ok w rv =>
    obtain ⟨hw, hy⟩ := hok w rv hrun
    simp only [hy]; rw [hrun] at h; simpa using h
  | exn w e => rw [hrun] at h; simp at h
  | timeout => rw [hrun] at h; simp at h
  | unsupported msg => rw [hrun] at h; simp at h

/-- The `.exn` transport twin. -/
theorem callFunctionClock_exn {m : Module} {fname : String} {args : Array Val}
    {fuel : Nat} {e : PyErr}
    (h : callFunction m fname args fuel = .exn e) (tr : List Int) :
    callFunctionClock m fname args tr fuel = .exn e := by
  obtain ⟨hok, hexn, hto⟩ :=
    callIn_clockErased fuel m (initWorld m) fname (RVal.thawArgs args)
      (initWorld_clock m)
  unfold callFunction at h
  unfold callFunctionClock
  rw [show ({ initWorld m with clock := tr } : World) = (initWorld m).withClock tr
    from rfl]
  cases hrun : callIn m fuel (initWorld m) fname (RVal.thawArgs args) with
  | ok w rv =>
    obtain ⟨hw, hy⟩ := hok w rv hrun
    simp only [hy]; rw [hrun] at h; simpa using h
  | exn w e2 =>
    obtain ⟨hw, hy⟩ := hexn w e2 hrun
    simp only [hy]; rw [hrun] at h; simpa using h
  | timeout => rw [hrun] at h; simp at h
  | unsupported msg => rw [hrun] at h; simp at h

/-- The `.timeout` transport (a run that popped would have refused, not
timed out — so empty-trace timeouts are trace-independent too). -/
theorem callFunctionClock_timeout {m : Module} {fname : String}
    {args : Array Val} {fuel : Nat}
    (h : callFunction m fname args fuel = .timeout) (tr : List Int) :
    callFunctionClock m fname args tr fuel = .timeout := by
  obtain ⟨hok, hexn, hto⟩ :=
    callIn_clockErased fuel m (initWorld m) fname (RVal.thawArgs args)
      (initWorld_clock m)
  unfold callFunction at h
  unfold callFunctionClock
  rw [show ({ initWorld m with clock := tr } : World) = (initWorld m).withClock tr
    from rfl]
  cases hrun : callIn m fuel (initWorld m) fname (RVal.thawArgs args) with
  | ok w rv =>
    obtain ⟨hw, hy⟩ := hok w rv hrun
    simp only [hy]; rw [hrun] at h; simpa using h
  | exn w e2 =>
    obtain ⟨hw, hy⟩ := hexn w e2 hrun
    simp only [hy]; rw [hrun] at h; exact h
  | timeout => simp only [hto hrun]; rfl
  | unsupported msg => rw [hrun] at h; simp at h

/-- `CallsIn` transport: a stateful call decided from an empty-clock world
runs identically from the same world under ANY seeded trace, returning the
trace untouched in the after-world. -/
theorem CallsIn.clock_erased {m : Module} {w w' : World} {fname : String}
    {args : Array RVal} {v : RVal}
    (h : CallsIn m w fname args w' v) (hw : w.clock = []) (tr : List Int) :
    CallsIn m (w.withClock tr) fname args (w'.withClock tr) v := by
  obtain ⟨fuel, hf⟩ := h
  obtain ⟨hok, -, -⟩ := callIn_clockErased fuel m w fname args hw
  obtain ⟨-, hy⟩ := hok w' v hf
  exact ⟨fuel, hy tr⟩

/-- `CallsTo` transport: every total public fact holds verbatim under
every seeded trace — the `∀ tr` form of the whole existing pin corpus. -/
theorem CallsTo.clock_erased {m : Module} {f : String} {args : Array Val}
    {v : Val} (h : CallsTo m f args v) (tr : List Int) :
    ∃ fuel, callFunctionClock m f args tr fuel = .ok v := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, callFunctionClock_ok hf tr⟩

end Arms

end LeanModels.Python
