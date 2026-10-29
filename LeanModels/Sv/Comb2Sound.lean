import LeanModels.Sv.Comb2Base

/-!
# Combinational settle ⇒ fixpoint equations (`LeanModels.Sv` — Design2)

The fuel-agnostic SOUNDNESS direction of the combinational settle theorem
(the `Comb2Base`/`Comb2Sound`/`Comb2Term`/`Comb2` layer): whenever
`combSettle2` returns on a comb design, the state it returns satisfies every
assign's equation (`CombEqs`), keeps the comb shape (`StateShape`), and
holds every undriven signal (inputs, constants, undriven nets) at its value
in the starting state. No acyclicity is needed — a cyclic design that happens
to settle settles to a solution of its equations; whether it settles at all
is `Comb2Term.lean`'s question.

## API index

* `combPass2_fixpoint_eqs_of_nodup` / `combPass2_fixpoint_eqs`: a pass over a
  duplicate-free order that covers every process and leaves the state
  unchanged proves `CombEqs` (the second form takes the `Perm` of the process
  range that `σ.choose` produces). The inductive core is
  `combPass2_fixpoint_aux` (the window-by-window argument below).
* `combSettle2_eqs` — **the soundness theorem**: `combSettle2 … = .ok (S, k')`
  ⇒ `CombEqs d S ∧ StateShape d S ∧` undriven signals held.
* Converse direction (the fixpoint is stable; no `Nodup`/coverage needed):
  `combPass2_of_combEqs` (a pass from a `CombEqs` state returns it, above the
  right-hand sides' sizes) and `combSettle2_of_combEqs` (settle from it returns
  it after ONE pass); `combPass2_of_combEqs_combFuel` /
  `combSettle2_of_combEqs_combFuel` take the fuel bound as
  `Design2.combFuel ≤ fuel`.
* Cycle level: `cycleStep2_eqs` — a successful comb-only cycle ends in a
  `CombEqs`/`StateShape` state whose undriven signals are those of the
  input-applied state.

## Design laws

* **Fuel never appears in a conclusion.** Every hypothesis is a successful
  run (`= .ok …`) at an arbitrary fuel; the right-hand sides are read back
  through `evalPure2` (`runCombProcess2_assign_ok`, which goes through
  `evalPure2_of_evalExpr2_ok`). Only the converse lemmas take a fuel bound
  (they run the interpreter forward).
* **The fixpoint argument is one process at a time, one window at a time.**
  If a pass over a duplicate-free order maps `st` to itself, then its FIRST
  process already maps `st` to itself: each window `(n, lo, w)` it wrote holds
  its slice right after the process (`CombDesign.combWrite_readBack`, which
  needs `CombDesign.selfDisjoint` for a concatenated target) and is not
  touched by any later process (`CombDesign.disjoint` + `Nodup`), so by
  `combPass2_frame` it holds that slice in the final state — which is `st`;
  writing every window's current content is the identity
  (`combWrite_eq_self`). So every intermediate state of the pass IS `st`, and
  each right-hand side was evaluated on `st` itself. Induction on the order
  carries this through the pass without ever naming the intermediate states.
* **`==` is `=`.** `combSettle2` returns exactly when `st' == st` on
  `SvState = List (String × LVec)`; the `LawfulBEq LVec` instance (Obs.lean)
  makes that propositional equality (`eq_of_beq`).

## Deviations from the original statement

* (2026-10-27, concatenation targets) `combPass2_fixpoint_aux` is stated per
  PLACED window (`((n, lo, w), off) ∈ Win.placed (t.wins d)`), like the
  generalized `CombEqs` (`Comb2Base.lean`, deviations); the theorems below it
  keep their statements.
* None in the main theorem's statement. `combPass2_fixpoint_eqs` is stated
  for an order that is a permutation of `List.range d.processes.size` (what
  `CombDesign.choose_perm_range` gives for every `σ.choose k d.combIndices`);
  the general form `combPass2_fixpoint_eqs_of_nodup` takes `Nodup` + coverage.

The smoke section at the end instantiates the settle and cycle theorems at
`Comb2Base`'s hand-built full adder (`Comb2Smoke.faDesign`).
-/

namespace LeanModels.Sv

variable {d : Design2}

/-! ## The fixpoint pass -/

/-- **Inductive core of the fixpoint argument.** A pass over a
duplicate-free index list from a shaped state that returns that same state
satisfies the equation of every listed process, evaluated on the state
itself: every placed window of its target holds its slice of the resized
right-hand side. -/
theorem combPass2_fixpoint_aux (hd : CombDesign d) {fuel : Nat} :
    ∀ {is : List Nat} {st : SvState}, is.Nodup → StateShape d st →
      combPass2 d fuel st is = .ok st →
      ∀ i ∈ is, ∀ (t : Lhs2) (e : Expr2) (n : String) (lo w off : Nat),
        d.processes[i]? = some (.assign t e) → ((n, lo, w), off) ∈ Win.placed (t.wins d) →
        ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
          old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w
  | [], _, _, _, _ => fun _ hi => absurd hi List.not_mem_nil
  | i :: rest, st, hnd, hs, h => by
      have hi_rest : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      rcases combPass2_cons_ok hd hs h with ⟨hnone, h⟩ | ⟨t, e, v, hp, hv, h⟩
      · -- out-of-range head: nothing ran, the tail is the whole pass
        intro j hj t' e' n' lo' w' off' hp' hw'
        rcases List.mem_cons.mp hj with rfl | hj
        · rw [hnone] at hp'; cases hp'
        · exact combPass2_fixpoint_aux hd hnd' hs h j hj t' e' n' lo' w' off' hp' hw'
      · -- the head wrote its windows; no later process touches any of them
        have hframe := (combPass2_frame hd (hs.combWrite t v) h).2
        -- so in the final state `st` every one of them holds its slice …
        have hwin : ∀ (n : String) (lo w off : Nat), ((n, lo, w), off) ∈ Win.placed (t.wins d) →
            ∃ old, SvState.lookup st n = some old ∧
              old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w := by
          intro n lo w off hm
          have hW : d.Writes i (n, lo, w) := ⟨t, e, hp, Win.mem_of_mem_placed hm⟩
          obtain ⟨u, hu, hue⟩ := hd.combWrite_readBack hs hp v hm
          have hagree := hframe (.win n lo w) (fun j hj wn hWj => by
            have hij : i ≠ j := fun hij => hi_rest (hij ▸ hj)
            exact hd.disjoint i j (n, lo, w) wn hij hW hWj)
          simp only [ReadWin.agree, hu, Option.map_some] at hagree
          cases ho : SvState.lookup st n with
          | none => rw [ho] at hagree; cases hagree
          | some old =>
              rw [ho] at hagree
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hagree
              exact ⟨old, rfl, hagree.2.symm.trans hue⟩
        -- … so the head's write was the identity, and the tail pass starts at `st`
        rw [combWrite_eq_self hwin] at h
        intro j hj t' e' n' lo' w' off' hp' hw'
        rcases List.mem_cons.mp hj with rfl | hj
        · rw [hp] at hp'
          simp only [Option.some.injEq, Process2.assign.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          obtain ⟨old, hold, hext⟩ := hwin n' lo' w' off' hw'
          exact ⟨old, v, hold, hv, hext⟩
        · exact combPass2_fixpoint_aux hd hnd' hs h j hj t' e' n' lo' w' off' hp' hw'

/-- **A fixpoint pass proves the equations** (general order). If a pass over
a duplicate-free order that lists every process index returns its input
state, that state satisfies `CombEqs`. -/
theorem combPass2_fixpoint_eqs_of_nodup (hd : CombDesign d) {fuel : Nat} {order : List Nat}
    (hnd : order.Nodup) (hcov : ∀ i, i < d.processes.size → i ∈ order) {st : SvState}
    (hs : StateShape d st) (h : combPass2 d fuel st order = .ok st) : CombEqs d st := by
  intro i t e n lo w off hp hw
  have hi : i < d.processes.size := by
    rcases Nat.lt_or_ge i d.processes.size with hi | hi
    · exact hi
    · rw [Array.getElem?_eq_none hi] at hp; cases hp
  exact combPass2_fixpoint_aux hd hnd hs h i (hcov i hi) t e n lo w off hp hw

/-- **A fixpoint pass proves the equations.** If a pass over a permutation
of all process indices (every `σ.choose k d.combIndices` is one —
`CombDesign.choose_perm_range`) returns its input state, that state
satisfies `CombEqs`. -/
theorem combPass2_fixpoint_eqs (hd : CombDesign d) {fuel : Nat} {order : List Nat}
    (hperm : order.Perm (List.range d.processes.size)) {st : SvState}
    (hs : StateShape d st) (h : combPass2 d fuel st order = .ok st) : CombEqs d st :=
  combPass2_fixpoint_eqs_of_nodup hd (hperm.nodup_iff.mpr List.nodup_range)
    (fun _ hi => hperm.mem_iff.mpr (List.mem_range.mpr hi)) hs h

/-! ## The settle loop -/

/-- **Soundness of the combinational settle.** On a comb design, from a
shaped state, whenever `combSettle2` returns (any schedule, any fuel), the
returned state satisfies every assign's equation, keeps the comb shape, and
holds every undriven signal at its starting value. -/
theorem combSettle2_eqs {σ : ScheduleOracle} {fuel : Nat} {st S : SvState} {k k' : Nat}
    (hd : CombDesign d) (hs : StateShape d st)
    (h : combSettle2 d σ fuel st k = .ok (S, k')) :
    CombEqs d S ∧ StateShape d S ∧
      (∀ n, NotDriven d n → SvState.lookup S n = SvState.lookup st n) := by
  induction fuel generalizing st k with
  | zero => simp [combSettle2] at h
  | succ f ih =>
      simp only [combSettle2, Res.bind_eq_ok] at h
      obtain ⟨st', hpass, hrest⟩ := h
      by_cases heq : (st' == st) = true
      · rw [if_pos heq] at hrest
        have hst' : st' = st := eq_of_beq heq
        subst hst'
        simp only [Res.ok.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, -⟩ := hrest
        exact ⟨combPass2_fixpoint_eqs hd (hd.choose_perm_range σ k) hs hpass, hs,
          fun _ _ => rfl⟩
      · rw [if_neg heq] at hrest
        have hs' : StateShape d st' := (combPass2_frame hd hs hpass).1
        obtain ⟨heqs, hsS, hnd⟩ := ih hs' hrest
        exact ⟨heqs, hsS, fun n hn => (hnd n hn).trans (combPass2_notDriven hd hs hpass hn)⟩

/-! ## The converse: a solution of the equations is a fixpoint -/

/-- **A pass from a solution is the identity** (any index list, fuel above
every right-hand side's size): each process rewrites its window with the
content it already holds. -/
theorem combPass2_of_combEqs (hd : CombDesign d) {fuel : Nat}
    (hf : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
      e.size < fuel)
    {st : SvState} (hs : StateShape d st) (heqs : CombEqs d st) :
    ∀ is : List Nat, combPass2 d fuel st is = .ok st
  | [] => rfl
  | i :: is => by
      cases hpi : d.processes[i]? with
      | none =>
          rw [combPass2_cons_none hpi]
          exact combPass2_of_combEqs hd hf hs heqs is
      | some p =>
          obtain ⟨t, e, ws, rfl, -⟩ := hd.assign i p hpi
          obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hpi
          have hid : combWrite d st t v = st := combWrite_eq_self fun n lo w off hm => by
            obtain ⟨old, v', hold, hv', hext⟩ := heqs i t e n lo w off hpi hm
            rw [hv] at hv'
            cases hv'
            exact ⟨old, hold, hext⟩
          rw [combPass2_cons_write hd hs hpi (hf i t e hpi) hv, hid]
          exact combPass2_of_combEqs hd hf hs heqs is

/-- `combPass2_of_combEqs` at any fuel from `Design2.combFuel` on. -/
theorem combPass2_of_combEqs_combFuel (hd : CombDesign d) {fuel : Nat}
    (hf : d.combFuel ≤ fuel) {st : SvState} (hs : StateShape d st) (heqs : CombEqs d st)
    (is : List Nat) : combPass2 d fuel st is = .ok st :=
  combPass2_of_combEqs hd
    (fun _ _ _ hp => Nat.lt_of_lt_of_le (Design2.size_lt_combFuel hp) hf) hs heqs is

/-- **Settle from a solution returns it after one pass** (fuel one above
every right-hand side's size). -/
theorem combSettle2_of_combEqs (hd : CombDesign d) {fuel : Nat}
    (hf : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
      e.size < fuel)
    {st : SvState} (hs : StateShape d st) (heqs : CombEqs d st) (σ : ScheduleOracle) (k : Nat) :
    combSettle2 d σ (fuel + 1) st k = .ok (st, k + 1) := by
  simp only [combSettle2, combPass2_of_combEqs hd hf hs heqs, Res.ok_bind, beq_self_eq_true,
    if_true]

/-- `combSettle2_of_combEqs` at any fuel above `Design2.combFuel`. -/
theorem combSettle2_of_combEqs_combFuel (hd : CombDesign d) {fuel : Nat}
    (hf : d.combFuel < fuel) {st : SvState} (hs : StateShape d st) (heqs : CombEqs d st)
    (σ : ScheduleOracle) (k : Nat) :
    combSettle2 d σ fuel st k = .ok (st, k + 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  exact combSettle2_of_combEqs hd
    (fun _ _ _ hp => Nat.lt_of_lt_of_le (Design2.size_lt_combFuel hp) (by omega)) hs heqs σ k

/-! ## The comb-only cycle -/

/-- **Soundness of a comb-only cycle.** A successful `cycleStep2` from a
shaped state ends in a state satisfying the equations, with the comb shape,
whose undriven signals are those of the input-applied state (inputs take the
stimulus, everything else undriven is held). -/
theorem cycleStep2_eqs {σ : ScheduleOracle} {fuel : Nat} {inputs st S : SvState} {k k' : Nat}
    (hd : CombDesign d) (hs : StateShape d st)
    (h : cycleStep2 d σ fuel inputs st k = .ok (S, k')) :
    CombEqs d S ∧ StateShape d S ∧
      (∀ n, NotDriven d n →
        SvState.lookup S n = SvState.lookup (applyInputs2 d inputs st) n) := by
  rw [cycleStep2_of_comb hd, Res.bind_eq_ok] at h
  obtain ⟨⟨st1, k1⟩, h1, h2⟩ := h
  obtain ⟨-, hs1, hnd1⟩ := combSettle2_eqs hd (StateShape.of_applyInputs2 hd hs inputs) h1
  obtain ⟨heqs, hsS, hnd2⟩ := combSettle2_eqs hd hs1 h2
  exact ⟨heqs, hsS, fun n hn => (hnd2 n hn).trans (hnd1 n hn)⟩

/-! ## Smoke test: the full adder of `Comb2Base`

Every settle and every cycle of `Comb2Smoke.faDesign` (any schedule, any
fuel) ends on a solution of its equations. -/

namespace Comb2Smoke

example {σ : ScheduleOracle} {fuel : Nat} {st S : SvState} {k k' : Nat}
    (hs : StateShape faDesign st) (h : combSettle2 faDesign σ fuel st k = .ok (S, k')) :
    CombEqs faDesign S :=
  (combSettle2_eqs fa_comb hs h).1

example {σ : ScheduleOracle} {fuel : Nat} {inputs S : SvState} {k k' : Nat}
    (h : cycleStep2 faDesign σ fuel inputs (initState2 faDesign) k = .ok (S, k')) :
    CombEqs faDesign S ∧ StateShape faDesign S :=
  let r := cycleStep2_eqs fa_comb (StateShape.of_initState2 fa_comb) h
  ⟨r.1, r.2.1⟩

end Comb2Smoke

end LeanModels.Sv
