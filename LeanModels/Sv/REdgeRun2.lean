import LeanModels.Sv.CycleMachine
import LeanModels.Sv.Mono2

/-!
# `REdgeRun2`: a closed-form clock cycle over `run2`, the target R-EDGE must produce

**Status: provisional over `run2`** (library, never trusted). Imported by nothing in the tree.

## What it is

`REdgeRun2 d enc Inv pre post n` says that one clock cycle of `d` has a **closed form**. The states
are encoded from a parameter type `X` (`enc`); `Inv` is the invariant on `X`. From an encoded state
satisfying `Inv`, under every schedule, every stimulus entry `e` and every fuel from `n` on:
* the part of the cycle before the edge (`cyclePre2`) ends in `enc (pre x e)`;
* the whole cycle (`cycleStep2`) ends in `enc (post x e)`.
The schedule counters are left free.

**Why the name.** This is the `run2` form of the conclusion of R-EDGE (ARCH-NOTE §4.3; experiment X4,
agent A). In a slot where only the clock edge occurs, the closed store is
`settle(commit(⋃ next(pre)))`, independent of the schedule. When R-EDGE (with R-COMB for the settles)
is proved from E, it should deliver exactly this shape generically, for every design in its fragment.
Until then each clocked design proves it over `run2` by hand (`cnt_redge`, `rf_redge`).

## What it buys (the plumbing every clocked design paid twice)

* `REdgeRun2.samples`: the two samples of ANY completed cycle observation are the closed form, at any
  fuel. This is the fuel-monotonicity argument, once.
* `REdgeRun2.terminates`: an invariant kept by the closed form gives `Terminates2`.
* `REdgeRun2.rcycle`: R-CYCLE (`rcycle_run2`) reduced to pure facts about `pre`, `post` and the
  machine: no cycle observation, no fuel, no schedule.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv

/-- `⊑`-monotonicity of the pre part of a cycle (settle, then the reset-event phase). -/
theorem cyclePre2_le (d : Design2) (σ : ScheduleOracle) {fuel fuel' : Nat} (h : fuel ≤ fuel')
    (inputs st : SvState) (k : Nat) :
    cyclePre2 d σ fuel inputs st k ⊑ cyclePre2 d σ fuel' inputs st k := by
  unfold cyclePre2 resetPhase2
  refine Res.le_bind (combSettle2_le d σ h _ k) fun p => ?_
  obtain ⟨st1, k1⟩ := p
  dsimp only
  split
  · exact Res.le_refl _
  · refine Res.le_bind (resetPass2_le d h _ st1 []) fun q => ?_
    obtain ⟨a, b⟩ := q
    exact combSettle2_le d σ h _ _

/-- **A closed-form clock cycle over `run2`**: the `run2` shape of R-EDGE's conclusion. -/
def REdgeRun2 (d : Design2) {X : Type} (enc : X → SvState) (Inv : X → Prop)
    (pre post : X → SvState → X) (n : Nat) : Prop :=
  ∀ (σ : ScheduleOracle) (e : SvState) (x : X) (k f : Nat), Inv x →
    (∃ k1, cyclePre2 d σ (f + n) e (enc x) k = .ok (enc (pre x e), k1)) ∧
    (∃ k', cycleStep2 d σ (f + n) e (enc x) k = .ok (enc (post x e), k'))

namespace REdgeRun2

variable {d : Design2} {X : Type} {enc : X → SvState} {Inv : X → Prop} {pre post : X → SvState → X}
  {n : Nat}

/-- **The samples of any completed cycle are the closed form**, at any fuel. -/
theorem samples (hC : REdgeRun2 d enc Inv pre post n) {σ : ScheduleOracle} {e : SvState} {x : X}
    {k F : Nat} {o : CycleObs SvState} {k' : Nat} (hI : Inv x)
    (h : cycleObs2 d σ F e (enc x) k = .ok (o, k')) :
    o.pre = enc (pre x e) ∧ o.post = enc (post x e) := by
  unfold cycleObs2 at h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨⟨p, k2⟩, h1, ⟨q, k3⟩, h2, h3⟩ := h
  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨⟨k1, hpre⟩, ⟨k'', hstep⟩⟩ := hC σ e x k F hI
  have hp := Res.le_eq (cyclePre2_le d σ (Nat.le_add_right F n) e (enc x) k) (by rw [h1]; simp)
  rw [h1, hpre] at hp
  simp only [Res.ok.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  refine ⟨rfl, ?_⟩
  have hs : cycleStep2 d σ F e (enc x) k = .ok (q, k3) := by
    rw [cycleStep2_eq_pre_post, h1, Res.ok_bind]; exact h2
  have hs' := cycleStep2_mono hs (by simp) (F + n) (Nat.le_add_right F n)
  rw [hstep] at hs'
  simp only [Res.ok.injEq, Prod.mk.injEq] at hs'
  exact hs'.1.symm

/-- **Termination from the closed form**: if the start state is encoded from an `Inv` value and the
closed form keeps `Inv`, every schedule and every stimulus completes (for a design with no qualified
`case`: master's `run2` runs the qualified-case trace check, `Terminates2.of_invariant`'s `hnoq`). -/
theorem terminates (hC : REdgeRun2 d enc Inv pre post n) {x0 : X} (h0 : initState2 d = enc x0)
    (hI0 : Inv x0) (hpost : ∀ x e, Inv x → Inv (post x e))
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false) : Terminates2 d :=
  Terminates2.of_invariant (fun st => ∃ x, Inv x ∧ st = enc x) ⟨x0, hI0, h0⟩ (fun σ =>
    ⟨0 + n, fun e st k ⟨x, hx, hst⟩ => by
      subst hst
      obtain ⟨-, k', hk⟩ := hC σ e x k 0 hx
      exact ⟨_, k', hk, post x e, hpost x e hx, rfl⟩⟩) hnq

/-- **R-CYCLE from the closed form**: a cycle machine `m` with an abstraction `abs` between the
encoded state and (store, held inputs) that the closed form respects (both samples are `m.out`, and
`post` stays abstracted by `m.next`) runs exactly like the design over `Obs_run2`. -/
theorem rcycle (hC : REdgeRun2 d enc Inv pre post n) (m : CycleMachine) (t : m.Tick)
    (hold : m.In → SvState → m.In) (i0 : m.In) (abs : X → m.Store → m.In → Prop)
    {x0 : X} {s0 : m.Store} (h0 : initState2 d = enc x0) (hI0 : Inv x0) (hs0 : m.init s0)
    (habs0 : abs x0 s0 i0)
    (hstep : ∀ x s i e, Inv x → abs x s i →
      Obs_run2.sample d (enc (pre x e)) = m.out s (hold i e) ∧
      Obs_run2.sample d (enc (post x e)) = m.out (m.next s (hold i e) t) (hold i e) ∧
      Inv (post x e) ∧ abs (post x e) (m.next s (hold i e) t) (hold i e)) :
    ∀ σ stim b, Obs_run2.Behaves d σ stim b →
      ∃ s, m.init s ∧ b = m.run t s (heldInputs hold i0 stim) := by
  refine rcycle_run2 m t hold i0 (fun st s i => ∃ x, st = enc x ∧ Inv x ∧ abs x s i) s0 hs0
    ⟨x0, h0, hI0, habs0⟩ ?_
  rintro σ F e prev k o k' s i ⟨x, rfl, hx, hab⟩ h
  obtain ⟨hpre, hpost⟩ := hC.samples hx h
  obtain ⟨h1, h2, h3, h4⟩ := hstep x s i e hx hab
  exact ⟨by rw [hpre, h1], by rw [hpost, h2], ⟨post x e, hpost, h3, h4⟩⟩

end REdgeRun2

#print axioms cyclePre2_le
#print axioms REdgeRun2.samples
#print axioms REdgeRun2.terminates
#print axioms REdgeRun2.rcycle

end LeanModels.Sv.Observe
