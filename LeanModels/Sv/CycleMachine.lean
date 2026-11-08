import LeanModels.Sv.Observe

/-!
# The cycle machine (D6) and a provisional R-CYCLE over `run2`

**Status.** `CycleMachine` and `CycleMachine.run` are the D6 view's shape: a derived view, never
trusted. `rcycle_run2` and `Obs_run2.safe_of_rcycle` are **provisional over `run2`**: R-CYCLE stated
against `Obs_run2`, not against E. Imported by nothing in the tree.

## What D6 is (ARCH-NOTE §4.2)

Per module at a parameter point, a cycle machine has:
* `Store`: the state the machine carries across clock ticks (the registers);
* `In`: the inputs held during a cycle;
* `Tick`: which clock ticked (`Unit` for one clock; several clocks, negedge and gating extend it
  later without changing the signature);
* `init`: the **start policy**, the stores a run may start from (over `run2`: initializers, else
  `x`);
* `out s i`: the **Mealy, settled** output, here the whole trusted port sample of store `s` under held
  inputs `i`;
* `next s i t`: the store after tick `t`.

`run` gives one `CycleObs` per cycle: `pre = out s i` (the edge reads the old store under this
cycle's inputs) and `post = out (next s i t) i` (the new store, inputs still held). This is
ARCH-NOTE R-CYCLE's equation.

Not here yet: `arcs` (combinational dependencies at bit or field granularity), which come with the
contracts and composition work (D9, D11). The uniform `Store := VarId → Val` comes with E; here
`Store` is a parameter.

## R-CYCLE over `run2` (provisional)

`rcycle_run2`: given a simulation `R` between `run2` states and (store, held inputs), established at
`initState2` and preserved by every cycle in the shape above (`hcyc`, the one-cycle obligation), every
completed `Obs_run2` behaviour IS the machine's run on the held inputs: exact on observations. The
held inputs are computed from the stimulus by `heldInputs` (each entry updates the held values; the
stimulus is the environment, so no observation feeds back). The obligation `hcyc` is where R-EDGE,
R-COMB and the register-transfer view (D5) will discharge things generically. Over `run2` it is one
per-design lemma: the counter's comes from its closed-form cycle (`CounterMachine.lean`).

`Obs_run2.safe_of_rcycle`: a safety statement proved for every run of the machine holds of the
design over `Obs_run2`. Proofs then live on the pure machine, with no schedule, no fuel and no
`SvState` (ARCH-NOTE §5.6, item 3).
-/

namespace LeanModels.Sv.Observe

/-- **The cycle machine (D6)**, at one parameter point. -/
structure CycleMachine where
  Store : Type
  In : Type
  Tick : Type
  /-- The start policy: the stores a run may start from. -/
  init : Store → Prop
  /-- The settled (Mealy) port sample of store `s` under held inputs `i`. -/
  out : Store → In → PortSample
  /-- The store after a clock tick. -/
  next : Store → In → Tick → Store

namespace CycleMachine

/-- The machine's run from store `s` on a list of held inputs: per cycle, `pre = out s i` and
`post = out (next s i t) i`. -/
def run (m : CycleMachine) (t : m.Tick) : m.Store → List m.In → List (CycleObs PortSample)
  | _, [] => []
  | s, i :: is => ⟨m.out s i, m.out (m.next s i t) i⟩ :: run m t (m.next s i t) is

/-- The store after the first `n` cycles. -/
def storeAt (m : CycleMachine) (t : m.Tick) : m.Store → List m.In → m.Store
  | s, [] => s
  | s, i :: is => storeAt m t (m.next s i t) is

@[simp] theorem run_nil (m : CycleMachine) (t : m.Tick) (s : m.Store) : m.run t s [] = [] := rfl

@[simp] theorem run_cons (m : CycleMachine) (t : m.Tick) (s : m.Store) (i : m.In)
    (is : List m.In) :
    m.run t s (i :: is) = ⟨m.out s i, m.out (m.next s i t) i⟩ :: m.run t (m.next s i t) is := rfl

theorem length_run (m : CycleMachine) (t : m.Tick) :
    ∀ (s : m.Store) (is : List m.In), (m.run t s is).length = is.length
  | _, [] => rfl
  | s, _ :: is => by simp [length_run m t _ is]

/-- Dropping `c` cycles of a run is running from the store after them. -/
theorem run_drop (m : CycleMachine) (t : m.Tick) :
    ∀ (c : Nat) (s : m.Store) (is : List m.In),
      (m.run t s is).drop c = m.run t (m.storeAt t s (is.take c)) (is.drop c)
  | 0, s, is => by simp [storeAt]
  | _ + 1, s, [] => by simp [storeAt]
  | c + 1, s, i :: is => by
      simp only [run_cons, List.drop_succ_cons, List.take_succ_cons, storeAt]
      exact run_drop m t c _ is

end CycleMachine

/-- The held inputs of a `run2` stimulus: entry `c` updates the values held since entry `c - 1`
(`hold`), starting from `i0`. -/
def heldInputs {In : Type} (hold : In → SvState → In) : In → List SvState → List In
  | _, [] => []
  | i, e :: es => hold i e :: heldInputs hold (hold i e) es

/-- **R-CYCLE over `run2`, along `runFromObs2`**: under the one-cycle obligation, the trusted
observations of a completed run from a state related to `(s, i)` are the machine's run from `s` on
the held inputs. -/
theorem rcycle_runFrom {d : Design2} (m : CycleMachine) (t : m.Tick) (hold : m.In → SvState → m.In)
    (R : SvState → m.Store → m.In → Prop)
    (hcyc : ∀ (σ : ScheduleOracle) (F : Nat) (e prev : SvState) (k : Nat) (o : CycleObs SvState)
        (k' : Nat) (s : m.Store) (i : m.In), R prev s i →
        cycleObs2 d σ F e prev k = .ok (o, k') →
        Obs_run2.sample d o.pre = m.out s (hold i e) ∧
        Obs_run2.sample d o.post = m.out (m.next s (hold i e) t) (hold i e) ∧
        R o.post (m.next s (hold i e) t) (hold i e))
    {σ : ScheduleOracle} {F : Nat} :
    ∀ (stim : List SvState) (st : SvState) (k : Nat) (s : m.Store) (i : m.In)
      (r : List (CycleObs SvState)), R st s i → runFromObs2 d σ F st k stim = .ok r →
      r.map (CycleObs.map (Obs_run2.sample d)) = m.run t s (heldInputs hold i stim)
  | [], st, k, s, i, r, _, h => by
      simp only [runFromObs2, Res.ok.injEq] at h
      subst h; rfl
  | e :: rest, st, k, s, i, r, hR, h => by
      simp only [runFromObs2, Res.bind_eq_ok] at h
      obtain ⟨⟨o, k'⟩, h1, os, h2, h3⟩ := h
      simp only [Res.pure_eq, Res.ok.injEq] at h3
      subst h3
      obtain ⟨hpre, hpost, hR'⟩ := hcyc σ F e st k o k' s i hR h1
      rw [List.map_cons, rcycle_runFrom m t hold R hcyc rest o.post k' _ _ os hR' h2]
      simp only [heldInputs, CycleMachine.run_cons, CycleObs.map, hpre, hpost]

/-- **R-CYCLE, provisional over `run2`** (ARCH-NOTE §4.3 R-CYCLE's shape: exact on observations).
Given a simulation `R` between `run2` states and (store, held inputs), true at `initState2` for a
store in the start policy, and the one-cycle obligation `hcyc`: every completed `Obs_run2` behaviour
is the machine's run, from a start-policy store, on the stimulus's held inputs. -/
theorem rcycle_run2 {d : Design2} (m : CycleMachine) (t : m.Tick) (hold : m.In → SvState → m.In)
    (i0 : m.In) (R : SvState → m.Store → m.In → Prop) (s0 : m.Store) (hs0 : m.init s0)
    (hR0 : R (initState2 d) s0 i0)
    (hcyc : ∀ (σ : ScheduleOracle) (F : Nat) (e prev : SvState) (k : Nat) (o : CycleObs SvState)
        (k' : Nat) (s : m.Store) (i : m.In), R prev s i →
        cycleObs2 d σ F e prev k = .ok (o, k') →
        Obs_run2.sample d o.pre = m.out s (hold i e) ∧
        Obs_run2.sample d o.post = m.out (m.next s (hold i e) t) (hold i e) ∧
        R o.post (m.next s (hold i e) t) (hold i e)) :
    ∀ σ stim b, Obs_run2.Behaves d σ stim b →
      ∃ s, m.init s ∧ b = m.run t s (heldInputs hold i0 stim) := by
  rintro σ stim b ⟨r, ⟨F, hrun⟩, rfl⟩
  have hrunFrom : runFromObs2 d σ F (initState2 d) 0 stim = .ok r := by
    unfold runObs2 at hrun
    cases hg : run2ClockGuard d with
    | ok u => simpa [hg] using hrun
    | timeout => simp [hg] at hrun
    | unsupported msg => simp [hg] at hrun
  exact ⟨s0, hs0, rcycle_runFrom m t hold R hcyc stim _ 0 s0 i0 r hR0 hrunFrom⟩

/-- **Safety statements move from the machine to the design**: under R-CYCLE, a safety statement
that holds of every machine run from the start policy holds of the design over `Obs_run2`, for every
clocking. Proofs about the design then reason about the pure machine only. -/
theorem Obs_run2.safe_of_rcycle {d : Design2} (m : CycleMachine) (t : m.Tick)
    (hold : m.In → SvState → m.In) (i0 : m.In)
    (hrc : ∀ σ stim b, Obs_run2.Behaves d σ stim b →
      ∃ s, m.init s ∧ b = m.run t s (heldInputs hold i0 stim))
    {k : Clocking} {Q : Iface → List (CycleObs PortSample) → Prop}
    (hQ : ∀ s, m.init s → ∀ is, Q (Obs_run2.iface d) (m.run t s is)) :
    Obs_run2.Safe k d Q := by
  intro σ stim b _ hb
  obtain ⟨s, hs, rfl⟩ := hrc σ stim b hb
  exact hQ s hs _

#print axioms CycleMachine.length_run
#print axioms CycleMachine.run_drop
#print axioms rcycle_runFrom
#print axioms rcycle_run2
#print axioms Obs_run2.safe_of_rcycle

end LeanModels.Sv.Observe
