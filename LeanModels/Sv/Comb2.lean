import LeanModels.Sv.Comb2Sound
import LeanModels.Sv.Comb2Term

/-!
# Combinational designs at run level (`LeanModels.Sv` — Design2)

The run-level layer of the combinational settle theorem (the
`Comb2Base`/`Comb2Sound`/`Comb2Term`/`Comb2` layer): what a challenge
statement about a comb design consumes. `Comb2Sound.lean` proved that a
successful settle (and a successful comb-only cycle) lands on a solution of
the design's equations;
`Comb2Term.lean` proved that, under an acyclicity certificate, every settle
returns. This file lifts both through `Runs2` / `⊨₂` / `Terminates2`
(`Spec2.lean`), so a correctness theorem about a comb design is stated and
proved against the fixpoint equations `CombEqs` alone — no fuel, no schedule,
no interpreter step in sight.

## API index

* Snapshots of a completed run (`Runs2`):
  `Runs2.comb_shape` (every snapshot has the comb shape),
  `Runs2.comb_snapshot` — **the snapshot theorem**: every snapshot satisfies
  `CombEqs` and `StateShape`, and its input ports hold whatever the stimulus
  entry of that cycle supplied;
  `Runs2.comb_snapshot_step` — the full characterization (every undriven
  signal of snapshot `c` is that of the previous snapshot with cycle `c`'s
  inputs applied) and its corollary `Runs2.comb_held` (an undriven signal the
  stimulus does not supply keeps its previous value).
* `⊨₂` introduction: `Models2.of_comb` (the basic form: the property
  follows from the per-snapshot equations and shape),
  `Models2.of_comb_inputs` (the hypothesis also receives the per-cycle input
  agreement), `Models2.of_comb_pointwise` (a per-state property that follows
  from `CombEqs`/`StateShape` holds of every snapshot).
* Non-vacuity: `cycleStep2_comb_ok` (a comb-only cycle succeeds from every
  shaped state at every fuel from `Design2.settleFuel` on, and keeps the
  shape) and `Terminates2.of_acyclic` — **the termination theorem**
  `CombDesign d → Acyclic d → Terminates2 d` (dotted like `Spec2`'s
  `Terminates2.of_invariant`; `terminates2_of_acyclic` is the same theorem
  under a root name).
* Reading the equations of one process: `LVec.extract_full` (the window
  `[0, v.width)` of `v` is `v`), `CombEqs.lookup_ident` (a
  whole-signal assign: the signal IS its resized right-hand side),
  `CombEqs.extract_slice` (a slice assign: the window holds it),
  `CombEqs.extract_index` (a constant-index assign), all three through
  `CombEqs.extract_window` (any leaf target); for a CONCATENATED target
  `CombEqs.concat_part` (each placed window holds its slice of the
  right-hand side resized to the target's total width) and
  `CombEqs.concat_part_ident` (a whole-signal part IS that slice) —
  `Comb2ConcatExample.lean` is the worked example.

## Design laws

* **Fuel never reaches a statement.** Every theorem here quantifies over
  `Runs2` / `⊨₂` / `Terminates2`; the one fuel-carrying lemma,
  `cycleStep2_comb_ok`, is the step of the `Terminates2.of_invariant`
  construction, at the explicit bound `Design2.settleFuel`.
* **One invariant: `StateShape`.** `initState2 d` has it
  (`StateShape.of_initState2`, through the `CombDesign.initWidth` field),
  `applyInputs2` keeps it (inputs are never driven), and every successful
  settle keeps it (`combSettle2_eqs`). The comb-only cycle is input settle
  then post-edge settle (`cycleStep2_of_comb`: no reset processes, the edge
  pass runs over `σ.choose k [] = []`, the NBA queue is empty), so the
  snapshot is the second settle's result and the shape flows through every
  cycle. Snapshot facts are proved by induction on the cycle index
  (`Runs2.forall_of_step`), not by unfolding the run.
* **Value-agnostic.** Like the other `Comb2*` files, this one is 4-state: no
  `BitVec`, no `Known2`. The known-value reading of the equations is the
  consumer's business (`Comb2Example.lean` shows the pattern on a full adder).

## Deviations from the original statement

* None in the statements of `Models2.of_comb` and `Terminates2.of_acyclic`.
  `Runs2.comb_snapshot` states its third conjunct (originally the
  placeholder "inputs of `st` = inputs applied from `stim` at cycle `c`, held
  otherwise") as: for the stimulus entry `inputs` of cycle `c`, every input
  port the entry binds holds that value. The "held otherwise" half is the
  separate `Runs2.comb_held`, and the exact undriven-signal equation is
  `Runs2.comb_snapshot_step`.
-/

namespace LeanModels.Sv

variable {d : Design2}

/-! ## Snapshots of a completed comb run -/

/-- Every snapshot of a completed run of a comb design has the comb shape. -/
theorem Runs2.comb_shape {σ : ScheduleOracle} {stim tr : List SvState} (hd : CombDesign d)
    (hr : Runs2 d σ stim tr) :
    ∀ (c : Nat) (st : SvState), tr[c]? = some st → StateShape d st :=
  hr.forall_of_step (I := StateShape d) (StateShape.of_initState2 hd)
    (fun _ _ _ _ _ _ hprev h => (cycleStep2_eqs hd hprev h).2.1)

/-- The state a cycle starts from (`initState2 d` at cycle 0, the previous
snapshot afterwards) has the comb shape. -/
private theorem Runs2.comb_prev_shape {σ : ScheduleOracle} {stim tr : List SvState}
    (hd : CombDesign d) (hr : Runs2 d σ stim tr) {c : Nat} {prev : SvState}
    (hp : (initState2 d :: tr)[c]? = some prev) : StateShape d prev := by
  cases c with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact StateShape.of_initState2 hd
  | succ c =>
      simp only [List.getElem?_cons_succ] at hp
      exact hr.comb_shape hd c prev hp

/-- **Snapshot characterization.** Snapshot `c` of a completed run of a comb
design satisfies the equations and the shape, and every undriven signal
(inputs, constants, undriven nets) holds its value in the previous snapshot
(`initState2 d` at cycle 0) after cycle `c`'s stimulus entry was applied. -/
theorem Runs2.comb_snapshot_step {σ : ScheduleOracle} {stim tr : List SvState}
    (hd : CombDesign d) (hr : Runs2 d σ stim tr) {c : Nat} {st : SvState}
    (hc : tr[c]? = some st) :
    ∃ inputs prev, stim[c]? = some inputs ∧ (initState2 d :: tr)[c]? = some prev ∧
      StateShape d prev ∧ CombEqs d st ∧ StateShape d st ∧
      ∀ n, NotDriven d n →
        SvState.lookup st n = SvState.lookup (applyInputs2 d inputs prev) n := by
  obtain ⟨_, inputs, prev, _, _, hi, hp, hs⟩ := hr.snapshot_step hc
  have hprev := Runs2.comb_prev_shape hd hr hp
  obtain ⟨heqs, hsh, hnd⟩ := cycleStep2_eqs hd hprev hs
  exact ⟨inputs, prev, hi, hp, hprev, heqs, hsh, hnd⟩

/-- **Every snapshot of a comb run solves the equations** (the snapshot
theorem). Snapshot `c` of a completed run (any schedule, any stimulus)
satisfies `CombEqs` and `StateShape`, and every input port that cycle `c`'s
stimulus entry binds holds exactly that value (the profile's
`CombDesign.inFourState`: a 2-state input would squash x/z). The "held otherwise" half —
an undriven signal the entry does not supply keeps its previous value — is
`Runs2.comb_held`; the exact undriven-signal equation is
`Runs2.comb_snapshot_step`. -/
theorem Runs2.comb_snapshot {σ : ScheduleOracle} {stim tr : List SvState} (hd : CombDesign d)
    (hr : Runs2 d σ stim tr) {c : Nat} {st : SvState} (hc : tr[c]? = some st) :
    CombEqs d st ∧ StateShape d st ∧
      ∀ inputs, stim[c]? = some inputs → ∀ n ∈ d.inputNames.toList, ∀ v,
        SvState.lookup inputs n = some v → SvState.lookup st n = some v := by
  obtain ⟨inputs, prev, hi, -, -, heqs, hsh, hnd⟩ := hr.comb_snapshot_step hd hc
  refine ⟨heqs, hsh, fun inputs' hi' n hn v hv => ?_⟩
  rw [hi, Option.some.injEq] at hi'
  subst hi'
  rw [hnd n (hd.notDriven_of_input hn), lookup_applyInputs2 d inputs prev n hd.inFourState,
    if_pos hn, hv]
  rfl

/-- **Held otherwise.** An undriven signal that cycle `c`'s stimulus entry
does not supply (not an input port, or not bound by the entry) keeps its
value from the previous snapshot (`initState2 d` at cycle 0). -/
theorem Runs2.comb_held {σ : ScheduleOracle} {stim tr : List SvState} (hd : CombDesign d)
    (hr : Runs2 d σ stim tr) {c : Nat} {st inputs prev : SvState} (hc : tr[c]? = some st)
    (hi : stim[c]? = some inputs) (hp : (initState2 d :: tr)[c]? = some prev) {n : String}
    (hn : NotDriven d n) (hns : n ∉ d.inputNames.toList ∨ SvState.lookup inputs n = none) :
    SvState.lookup st n = SvState.lookup prev n := by
  obtain ⟨inputs', prev', hi', hp', -, -, -, hnd⟩ := hr.comb_snapshot_step hd hc
  rw [hi, Option.some.injEq] at hi'
  rw [hp, Option.some.injEq] at hp'
  subst hi' hp'
  rw [hnd n hn, lookup_applyInputs2 d inputs prev n hd.inFourState]
  by_cases hin : n ∈ d.inputNames.toList
  · rw [if_pos hin, hns.resolve_left (fun h => h hin)]
    rfl
  · rw [if_neg hin]

/-! ## `⊨₂` introduction for comb designs -/

/-- **`⊨₂` from the equations** (the basic form). A stimulus/trace
property that follows from "every snapshot satisfies `CombEqs` and
`StateShape`" holds of every completed run of a comb design, under every
schedule. -/
theorem Models2.of_comb (hd : CombDesign d) {P : List SvState → List SvState → Prop}
    (hP : ∀ stim tr,
      (∀ (c : Nat) (st : SvState), tr[c]? = some st → CombEqs d st ∧ StateShape d st) →
        P stim tr) :
    d ⊨₂ spec2 P :=
  fun _ stim tr hr => hP stim tr fun _ _ hc =>
    let h := hr.comb_snapshot hd hc
    ⟨h.1, h.2.1⟩

/-- **`⊨₂` from the equations and the applied inputs.** `Models2.of_comb`
whose hypothesis also receives, per cycle, that every input port bound by the
cycle's stimulus entry holds that value in the snapshot. -/
theorem Models2.of_comb_inputs (hd : CombDesign d) {P : List SvState → List SvState → Prop}
    (hP : ∀ stim tr,
      (∀ (c : Nat) (st : SvState), tr[c]? = some st → CombEqs d st ∧ StateShape d st ∧
        ∀ inputs, stim[c]? = some inputs → ∀ n ∈ d.inputNames.toList, ∀ v,
          SvState.lookup inputs n = some v → SvState.lookup st n = some v) →
        P stim tr) :
    d ⊨₂ spec2 P :=
  fun _ stim tr hr => hP stim tr fun _ _ hc => hr.comb_snapshot hd hc

/-- **Pointwise `⊨₂`.** A property of single states that follows from
`CombEqs` and `StateShape` holds of every snapshot of every completed run. -/
theorem Models2.of_comb_pointwise (hd : CombDesign d) {Q : SvState → Prop}
    (hQ : ∀ st, CombEqs d st → StateShape d st → Q st) :
    d ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st → Q st :=
  Models2.of_comb hd fun _ _ h c st hc => hQ st (h c st hc).1 (h c st hc).2

/-! ## Termination -/

/-- **A comb-only cycle succeeds and keeps the shape**: on a comb design
with an acyclicity certificate, from every shaped state, every `cycleStep2`
(any schedule, inputs, and schedule counter) at fuel `≥ Design2.settleFuel d`
returns `.ok` into a shaped state. -/
theorem cycleStep2_comb_ok (hd : CombDesign d) (ha : Acyclic d) {fuel : Nat}
    (hf : d.settleFuel ≤ fuel) (σ : ScheduleOracle) (inputs st : SvState) (k : Nat)
    (hs : StateShape d st) :
    ∃ S k', cycleStep2 d σ fuel inputs st k = .ok (S, k') ∧ StateShape d S := by
  have hs0 := StateShape.of_applyInputs2 hd hs inputs
  obtain ⟨S1, k1, h1⟩ := combSettle2_terminates_of_le hd ha hf σ _ k hs0
  have hs1 := (combSettle2_eqs hd hs0 h1).2.1
  obtain ⟨S2, k2, h2⟩ := combSettle2_terminates_of_le hd ha hf σ S1 (k1 + 1) hs1
  refine ⟨S2, k2, ?_, (combSettle2_eqs hd hs1 h2).2.1⟩
  rw [cycleStep2_of_comb hd, h1, Res.ok_bind]
  exact h2

/-- **Acyclic comb designs terminate** (the termination theorem): every
schedule and every stimulus has a completed run. Together with
`Models2.of_comb` this makes a `⊨₂` theorem about a comb design non-vacuous.
Named like `Spec2`'s `Terminates2.of_invariant`, the general way to build
`Terminates2`; `terminates2_of_acyclic` is the same theorem under a root
name. -/
theorem Terminates2.of_acyclic (hd : CombDesign d) (ha : Acyclic d) : Terminates2 d :=
  Terminates2.of_invariant (StateShape d) (StateShape.of_initState2 hd) fun σ =>
    ⟨d.settleFuel, fun inputs st k hs =>
      cycleStep2_comb_ok hd ha (Nat.le_refl _) σ inputs st k hs⟩

/-- Root-name alias of `Terminates2.of_acyclic` (acyclic comb designs
terminate). -/
theorem terminates2_of_acyclic (hd : CombDesign d) (ha : Acyclic d) : Terminates2 d :=
  Terminates2.of_acyclic hd ha

/-! ## Reading one equation -/

/-- The full window — starting at bit 0, as wide as the vector — is the
vector itself. -/
theorem LVec.extract_full (v : LVec) : v.extract 0 v.width = v := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, Nat.zero_add]

/-- **A leaf assign, read back** (the common core of the three leaf forms
below). In a solution of the equations, the window `(n, lo, w)` of a leaf
target holds the right-hand side's value resized to `w`. -/
theorem CombEqs.extract_window {st : SvState} (heqs : CombEqs d st) {i : Nat} {t : Lhs2}
    {e : Expr2} (hp : d.processes[i]? = some (.assign t e)) {n : String} {lo w : Nat}
    (ht : t.window? d = some (n, lo, w)) {v : LVec} (hv : evalPure2 st e = .ok v) :
    ∃ old, SvState.lookup st n = some old ∧ old.extract lo w = v.resizeU w := by
  have hwins := Lhs2.wins_of_window? ht
  obtain ⟨old, v', hold, hv', hext⟩ := heqs i t e n lo w 0 hp (by simp [hwins])
  rw [hv, Res.ok.injEq] at hv'
  subst hv'
  refine ⟨old, hold, ?_⟩
  rw [hext, hwins]
  simp only [Win.sumWidth_cons, Win.sumWidth_nil, Nat.add_zero]
  exact LVec.extract_zero_of_width (LVec.width_resizeU _ _)

/-- **A whole-signal assign, read back.** In a shaped solution of the
equations, the target of `assign n = e` holds `e`'s value resized to `n`'s
declared width. -/
theorem CombEqs.lookup_ident (hd : CombDesign d) {st : SvState} (heqs : CombEqs d st)
    (hs : StateShape d st) {i : Nat} {n : String} {e : Expr2}
    (hp : d.processes[i]? = some (.assign (.ident n) e)) {v : LVec} (hv : evalPure2 st e = .ok v)
    {w : Nat} (hw : d.declWidth n = some w) : SvState.lookup st n = some (v.resizeU w) := by
  have hwin : (Lhs2.ident n).window? d = some (n, 0, w) := by simp [Lhs2.window?, hw]
  obtain ⟨old, hold, hext⟩ := heqs.extract_window hp hwin hv
  obtain ⟨old', hold', -, hdw⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hwin)
  rw [hold] at hold'
  cases hold'
  rw [hw, Option.some.injEq] at hdw
  subst hdw
  rw [hold, ← hext, LVec.extract_full]

/-- **A slice assign, read back.** In a solution of the equations, the
window `[lo, lo + w)` of the target of `assign n[lo +: w] = e` holds `e`'s
value resized to `w`. -/
theorem CombEqs.extract_slice {st : SvState} (heqs : CombEqs d st) {i : Nat} {n : String}
    {lo w : Nat} {e : Expr2} (hp : d.processes[i]? = some (.assign (.slice n lo w) e)) {v : LVec}
    (hv : evalPure2 st e = .ok v) :
    ∃ old, SvState.lookup st n = some old ∧ old.extract lo w = v.resizeU w :=
  heqs.extract_window hp rfl hv

/-- **A constant-index assign, read back.** In a solution of the equations,
element `k` (window `[k·elemW, (k+1)·elemW)`) of the target of
`assign n[c] = e` (literal `c` with value `k`) holds `e`'s value resized to
`elemW`. -/
theorem CombEqs.extract_index {st : SvState} (heqs : CombEqs d st) {i : Nat} {n : String}
    {c : LVec} {k elemW : Nat} {e : Expr2}
    (hp : d.processes[i]? = some (.assign (.index n (.lit c) elemW) e)) (hk : c.toNat? = some k)
    {v : LVec} (hv : evalPure2 st e = .ok v) :
    ∃ old, SvState.lookup st n = some old ∧
      old.extract (k * elemW) elemW = v.resizeU elemW :=
  heqs.extract_window hp (by simp [Lhs2.window?, hk]) hv

/-- **A concatenation part, read back.** In a solution of the equations,
every placed window `(n, lo, w)` (offset `off`, `Win.placed`) of an assign's
target — `assign {p₀, …, pₖ} = e`, nested concatenations flattened — holds
bits `[off, off + w)` of `e`'s value resized to the target's total width
`Win.sumWidth (t.wins d)` (the first part gets the high slice). -/
theorem CombEqs.concat_part {st : SvState} (heqs : CombEqs d st) {i : Nat} {t : Lhs2}
    {e : Expr2} (hp : d.processes[i]? = some (.assign t e)) {v : LVec}
    (hv : evalPure2 st e = .ok v) {n : String} {lo w off : Nat}
    (hm : ((n, lo, w), off) ∈ Win.placed (t.wins d)) :
    ∃ old, SvState.lookup st n = some old ∧
      old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w := by
  obtain ⟨old, v', hold, hv', hext⟩ := heqs i t e n lo w off hp hm
  rw [hv, Res.ok.injEq] at hv'
  subst hv'
  exact ⟨old, hold, hext⟩

/-- **A whole-signal concatenation part, read back.** In a shaped solution of
the equations, a part `n` of a concatenated target (window `(n, 0, w)` with
`w` the declared width, offset `off`) holds bits `[off, off + w)` of the
right-hand side's value resized to the target's total width — e.g. for
`assign {co, s} = e` with `s` `N` bits: `s = (v.resizeU (1 + N)).extract 0 N`
and `co = (v.resizeU (1 + N)).extract N 1`. -/
theorem CombEqs.concat_part_ident (hd : CombDesign d) {st : SvState} (heqs : CombEqs d st)
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {v : LVec} (hv : evalPure2 st e = .ok v)
    {n : String} {w off : Nat} (hm : ((n, 0, w), off) ∈ Win.placed (t.wins d))
    (hw : d.declWidth n = some w) :
    SvState.lookup st n = some ((v.resizeU (Win.sumWidth (t.wins d))).extract off w) := by
  obtain ⟨old, hold, hext⟩ := heqs.concat_part hp hv hm
  obtain ⟨old', hold', -, hdw⟩ := hd.lookup_writes hs ⟨t, e, hp, Win.mem_of_mem_placed hm⟩
  rw [hold] at hold'
  cases hold'
  rw [hw, Option.some.injEq] at hdw
  subst hdw
  rw [hold, ← hext, LVec.extract_full]

/-! ## Smoke test: the full adder of `Comb2Base`

`Comb2Smoke.faDesign` terminates and every snapshot of every run solves its
equations; `Comb2Example.lean` turns the equations into the full-adder
truth (with the `Known2` calculus). -/

namespace Comb2Smoke

example : Terminates2 faDesign := terminates2_of_acyclic fa_comb fa_acyclic

example : faDesign ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
    CombEqs faDesign st ∧ StateShape faDesign st :=
  Models2.of_comb_pointwise fa_comb fun _ h1 h2 => ⟨h1, h2⟩

end Comb2Smoke

end LeanModels.Sv
