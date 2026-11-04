import LeanModels.Sv.CycleMachine

/-!
# Module contracts (D11) over the observation interface

**Status: derived view (D11), DRAFT.** It is stated over the abstract `ObservationModel`
(`Observe.lean`), not over `run2`, so it survives the backend swap (lead's steer, Day 7).
Imported by nothing in the tree. The `run2` instance and the full adder are in
`ContractFA.lean`.

## The shape (ARCH-NOTE §4.2 D11, §4.3 R-CONTRACT; the circuit lane's `Behavior.lean`)

A `Contract` names:
* **the ports** (`iface`), **the clocking** its rely assumes (`clocking`), and **the free inputs**
  (`free`): the inputs the environment controls in every cycle, every input except the clock;
* **ghost state** (`Ghost`, `ginit`, `gnext`): a function of the observed history, so a rely or a
  guarantee can speak about the past (counters, outstanding requests, last written values);
* **a rely** on each cycle's pre sample (the inputs held at the edge) given the ghost state, causal
  by construction (the ghost state sees only earlier cycles);
* **a guarantee** on each cycle's observation (pre and post samples) given the ghost state:
  relational within a run;
* **arcs**: the same-cycle combinational dependencies, input window to output window, at bit or
  field granularity (`PortWin = (port, lo, width)`);
* **a direction** (`Direction`): exact, over-approximation or under-approximation.

## What `Sat` asks (`Contract.Sat`)

`C.Sat M d` bundles four things:
* the interface;
* **realizability** (`Realizable`, the circuit lane's `RealizableUnder`): every disciplined
  environment has a behaviour, under every choice;
* **receptiveness** (`Receptive`, `ReceptiveUnder`): every sequence of known values on the free
  inputs appears in the pre samples of some behaviour;
* **safety**: every disciplined behaviour satisfies the contract (`Holds`). At each cycle, if the
  rely held at every cycle up to and including it, the guarantee holds there.

Safety and non-vacuity are separate, as in the circuit lane: safety over an empty behaviour set is not
a correctness result.

## The direction discipline (review verdict 8, the lead's steer)

* `Contract.safety_sound`: a satisfied contract's guarantee holds of every behaviour, and of every
  behaviour of any backend included in this one (`Safe.of_included`). It holds for EVERY direction.
* Two-run properties need exactness. `Contract.SatExact` requires `C.dir = .exact`, by definition,
  plus completeness: every rely-respecting observation sequence the contract allows is a behaviour.
  Only `SatExact` feeds `Contract.equiv_sound`: two designs satisfying one exact contract have the
  same rely-respecting behaviours. No lemma lets an over-approximating contract carry a two-run
  property, because none takes a plain `Sat`.
* `ArcsSoundOn` (arcs) is likewise two-run (it compares two input valuations), so it is stated on an
  exact view, a cycle machine (`CycleMachine.lean` shape), not on a contract's behaviour set.

## Composition (R-CONTRACT, safety only)

`compose_holds`: take one run of a parent with children `k`. Child `k` sees the projection `proj k`
of the parent's PROOF observations, because a child's ports are wired to the parent's internal nets,
the cut points. The parent contract holds of the parent's trusted view when:
* every child's contract holds on its projection;
* the children's relies are discharged, by the parent's rely, by any child's guarantee in an EARLIER
  cycle, or by a lower-ranked child's guarantee in the same cycle (the acyclic arcs, as a rank);
* the abstract parent turns the children's guarantees and its own rely into its guarantee.
`compose_safe_inv` lifts this to a design, given that every parent run projects to a behaviour of
each child (`ProjectsTo`, the hierarchy refinement R-HIER: over `run2`, the map from the flattened
processes back to instance `k`), and lets the rely discharge and the abstract parent use any
invariant `Inv` of the parent's runs. That is where the parent's own glue processes enter (port
connections, `c[0] = cin`): they hold on runs, not on every probe list. `compose_safe` is the
special case `Inv := fun _ => True`. Safety only: nothing here composes a two-run property.
-/

namespace LeanModels.Sv.Observe

/-! ## Valuations, windows, arcs, directions -/

/-- A known value for every port signature: `v p : BitVec p.2`. -/
abbrev Valuation := (p : Sig) → BitVec p.2

/-- The sample `s` holds the known value `v p` on every port `p` of `sigs`. -/
def HoldsOn (s : PortSample) (sigs : List Sig) (v : Valuation) : Prop :=
  ∀ p ∈ sigs, s.read p.1 = some (LVec.ofBitVec (v p))

/-- A window of a port: name, lowest bit, width (a bit when the width is 1, a field otherwise). -/
abbrev PortWin := String × Nat × Nat

/-- Two samples agree on a window. -/
def WinAgree (s s' : PortSample) (w : PortWin) : Prop :=
  (s.read w.1).map (·.extract w.2.1 w.2.2) = (s'.read w.1).map (·.extract w.2.1 w.2.2)

/-- A same-cycle combinational dependency: output window `dst` may depend on input window `src`. -/
structure Arc where
  src : PortWin
  dst : PortWin
deriving DecidableEq, Repr

/-- The direction in which a view or a contract approximates the design (ARCH-NOTE §4.3). -/
inductive Direction where
  | exact
  | overApprox
  | underApprox
deriving DecidableEq, Repr

/-! ## Contracts -/

/-- **A module contract (D11).** -/
structure Contract where
  iface : Iface
  clocking : Clocking
  free : List Sig
  Ghost : Type
  ginit : Ghost
  gnext : Ghost → CycleObs PortSample → Ghost
  rely : Ghost → PortSample → Prop
  guar : Ghost → CycleObs PortSample → Prop
  arcs : List Arc
  dir : Direction

namespace Contract

variable (C : Contract)

/-- The ghost state before each cycle of an observed history. -/
def ghosts : C.Ghost → List (CycleObs PortSample) → List C.Ghost
  | _, [] => []
  | g, o :: os => g :: ghosts (C.gnext g o) os

/-- The rely holds at cycle `c` (vacuous past the end). -/
def RelyAt (b : List (CycleObs PortSample)) (c : Nat) : Prop :=
  ∀ g o, (C.ghosts C.ginit b)[c]? = some g → b[c]? = some o → C.rely g o.pre

/-- The guarantee holds at cycle `c` (vacuous past the end). -/
def GuarAt (b : List (CycleObs PortSample)) (c : Nat) : Prop :=
  ∀ g o, (C.ghosts C.ginit b)[c]? = some g → b[c]? = some o → C.guar g o

/-- **The contract on one behaviour (safety)**: at every cycle, if the rely held at every cycle up
to and including it, the guarantee holds there. -/
def Holds (b : List (CycleObs PortSample)) : Prop :=
  ∀ c, (∀ c' ≤ c, C.RelyAt b c') → C.GuarAt b c

/-- **Realizability** (`RealizableUnder`): under every choice, every environment disciplined for the
contract's clocking has a completed behaviour. -/
def Realizable (M : ObservationModel) (d : M.Design) : Prop :=
  M.Progress C.clocking d

/-- **Receptiveness** (`ReceptiveUnder`): under every choice, every finite sequence of known values
on the free inputs appears in the pre samples of some behaviour in a disciplined environment, one
cycle per entry. -/
def Receptive (M : ObservationModel) (d : M.Design) : Prop :=
  ∀ (ch : M.Choice) (s : List Valuation), ∃ env b, M.Disciplined C.clocking env ∧
    M.Behaves d ch env b ∧ b.length = s.length ∧
    ∀ (c : Nat) (o : CycleObs PortSample) (v : Valuation), b[c]? = some o → s[c]? = some v →
      HoldsOn o.pre C.free v

/-- **`d ⊨ C`**: interface, realizability, receptiveness, and safety. Valid for every direction;
it is what `safety_sound` consumes. -/
structure Sat (M : ObservationModel) (d : M.Design) : Prop where
  iface : M.iface d = C.iface
  realizable : C.Realizable M d
  receptive : C.Receptive M d
  safe : M.Safe C.clocking d fun _ b => C.Holds b

/-- **Exact satisfaction**: only for a contract labelled `exact`. Besides `Sat`, completeness: every
observation sequence on which the rely holds everywhere and the contract holds is a behaviour in a
disciplined environment. The only entry point of two-run reasoning (`equiv_sound`). -/
structure SatExact (M : ObservationModel) (d : M.Design) : Prop where
  sat : C.Sat M d
  exact : C.dir = .exact
  complete : ∀ b, (∀ c, C.RelyAt b c) → C.Holds b →
    ∃ ch env, M.Disciplined C.clocking env ∧ M.Behaves d ch env b

/-- **Safety soundness** (every direction): the guarantee holds of every disciplined behaviour,
under the rely. -/
theorem safety_sound {M : ObservationModel} {d : M.Design} (h : C.Sat M d) :
    ∀ ch env b, M.Disciplined C.clocking env → M.Behaves d ch env b → C.Holds b :=
  h.safe

/-- **Safety soundness across backends**: if `M₁`'s behaviours of `d₁` are included in `M₂`'s of
`d₂` (for instance `run2` in E, by R-DESIGN2), a contract `d₂` satisfies over `M₂` holds of `d₁`'s
behaviours over `M₁`. Safety only. -/
theorem safety_sound_of_included {M₁ M₂ : ObservationModel} {d₁ : M₁.Design} {d₂ : M₂.Design}
    (hinc : Included M₁ M₂ C.clocking d₁ d₂) (h : C.Sat M₂ d₂) :
    M₁.Safe C.clocking d₁ fun _ b => C.Holds b :=
  Safe.of_included hinc h.safe

/-- **Safety soundness across backends, on restricted environments** (the general form): if
`M₁`'s behaviours of `d₁` are included in `M₂`'s on the environments satisfying `P` (for instance
`run2` in E on typed stimuli), a contract `d₂` satisfies over `M₂` holds of `d₁`'s behaviours there.
Safety only. -/
theorem safety_sound_of_includedOn {M₁ M₂ : ObservationModel} {d₁ : M₁.Design} {d₂ : M₂.Design}
    {P : M₁.Env → Prop} (hinc : IncludedOn M₁ M₂ C.clocking d₁ d₂ P) (h : C.Sat M₂ d₂) :
    M₁.SafeOn C.clocking d₁ P fun _ b => C.Holds b :=
  SafeOn.of_includedOn hinc h.safe

/-- **Equivalence soundness (two-run; exact contracts only)**: two designs that satisfy one exact
contract have the same rely-respecting behaviours. There is no version for `Sat` alone, and so none
for an over-approximating contract. -/
theorem equiv_sound {M : ObservationModel} {d₁ d₂ : M.Design} (h₁ : C.SatExact M d₁)
    (h₂ : C.SatExact M d₂) (b : List (CycleObs PortSample)) (hr : ∀ c, C.RelyAt b c) :
    (∃ ch env, M.Disciplined C.clocking env ∧ M.Behaves d₁ ch env b) ↔
      (∃ ch env, M.Disciplined C.clocking env ∧ M.Behaves d₂ ch env b) := by
  constructor
  · rintro ⟨ch, env, hk, hb⟩
    exact h₂.complete b hr (h₁.sat.safe ch env b hk hb)
  · rintro ⟨ch, env, hk, hb⟩
    exact h₁.complete b hr (h₂.sat.safe ch env b hk hb)

end Contract

/-! ## Arcs on an exact view -/

/-- **Arc soundness on a cycle machine** (a two-run property, so stated on an exact view): under one
store, two input valuations whose pre samples agree on every source window of the arcs into an
output window `w` give pre samples that agree on `w`. An output window no arc reaches is constant in
the inputs of the cycle. -/
def ArcsSoundOn (arcs : List Arc) (outs : List PortWin) (m : CycleMachine) : Prop :=
  ∀ (s : m.Store) (i i' : m.In), ∀ w ∈ outs,
    (∀ a ∈ arcs, a.dst = w → WinAgree (m.out s i) (m.out s i') a.src) →
      WinAgree (m.out s i) (m.out s i') w

/-! ## Composition (R-CONTRACT, safety only)

A child's ports are generally wired to the parent's INTERNAL nets (in `ripple_fa`, instance `k`'s
`cin` is the carry net `c[k]`), which trusted samples do not hold (ports only, review verdict 7).
So composition reads the children off the parent's **proof observation** (`M.Probe`, the cut points):
the parent's trusted behaviour is `r.map (CycleObs.map (M.sample d))` of a run `r` of probes, and
child `k` sees `r.map (proj k)`. -/

namespace Contract

/-- **Composition on one run (safety only).** A run `r` of the parent (any observation type `α`),
whose trusted view is `r.map top` and whose child `k` sees `r.map (proj k)`, satisfies the parent
contract `C` when:
* `hchild`: each child's contract holds on its projection;
* `hrely` (the rely discharge): a child's rely at cycle `c` follows from the parent's rely up to `c`,
  every child's guarantee at earlier cycles, and the guarantees at `c` of the children of lower rank
  (the acyclic arcs, as a rank);
* `hpar` (the abstract parent): the parent's guarantee at `c` follows from its rely up to `c` and
  every child's guarantee at `c`. -/
theorem compose_holds (C : Contract) {α K : Type} (child : K → Contract)
    (top : α → CycleObs PortSample) (proj : K → α → CycleObs PortSample) (rank : K → Nat)
    (r : List α)
    (hchild : ∀ k, (child k).Holds (r.map (proj k)))
    (hrely : ∀ k c, (∀ c' ≤ c, C.RelyAt (r.map top) c') →
      (∀ j c', c' < c → (child j).GuarAt (r.map (proj j)) c') →
      (∀ j, rank j < rank k → (child j).GuarAt (r.map (proj j)) c) →
      (child k).RelyAt (r.map (proj k)) c)
    (hpar : ∀ c, (∀ c' ≤ c, C.RelyAt (r.map top) c') →
      (∀ k, (child k).GuarAt (r.map (proj k)) c) → C.GuarAt (r.map top) c) :
    C.Holds (r.map top) := by
  -- every child's guarantee at every cycle up to `c`, by induction on `c`, then on the rank
  have all : ∀ c, (∀ c' ≤ c, C.RelyAt (r.map top) c') →
      ∀ c' ≤ c, ∀ k, (child k).GuarAt (r.map (proj k)) c' := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ihc =>
      intro hR c' hc' k
      -- the earlier cycles, from the outer hypothesis
      have hpast : ∀ j c'', c'' < c' → (child j).GuarAt (r.map (proj j)) c'' := by
        intro j c'' hlt
        rcases Nat.lt_or_ge c' c with hlt' | hge
        · exact ihc c' hlt' (fun c₀ h₀ => hR c₀ (by omega)) c'' (by omega) j
        · exact ihc c'' (by omega) (fun c₀ h₀ => hR c₀ (by omega)) c'' (Nat.le_refl _) j
      -- cycle `c'` itself, by strong induction on the rank
      have hrank : ∀ n k, rank k = n → (child k).GuarAt (r.map (proj k)) c' := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihr =>
          intro k hk
          refine hchild k c' fun c₀ h₀ => ?_
          rcases Nat.lt_or_ge c₀ c' with hlt | hge
          · -- an earlier cycle: the rely of child `k` there, from the past
            exact hrely k c₀ (fun c₁ h₁ => hR c₁ (by omega)) (fun j c₁ h₁ => hpast j c₁ (by omega))
              (fun j _ => hpast j c₀ hlt)
          · obtain rfl : c₀ = c' := by omega
            exact hrely k c₀ (fun c₁ h₁ => hR c₁ (by omega)) hpast
              (fun j hj => ihr (rank j) (hk ▸ hj) j rfl)
      exact hrank (rank k) k rfl
  intro c hR
  exact hpar c hR fun k => all c hR c (Nat.le_refl _) k

end Contract

/-- **Hierarchy refinement, as the composition rule needs it**: every disciplined run of the parent
`d`, read at the cut points by `proj` (from the parent's proof observation to the child's port
sample), is a disciplined behaviour of the child `d'`. Over `run2`, where the loader flattens
instances, this is the map from the flattened processes back to one instance (WP-I-NOTE route C;
R-HIER in E-core-2). -/
def ProjectsTo (M : ObservationModel) (k : Clocking) (d : M.Design)
    (proj : CycleObs M.Probe → CycleObs PortSample) (M' : ObservationModel) (k' : Clocking)
    (d' : M'.Design) : Prop :=
  ∀ ch env r, M.Disciplined k env → M.Runs d ch env r →
    ∃ ch' env', M'.Disciplined k' env' ∧ M'.Behaves d' ch' env' (r.map proj)

namespace Contract

/-- **R-CONTRACT (safety only) for a design, with a run invariant** (the general form): children `k`
with designs `dk k` satisfying their contracts (over any backends), a parent whose runs project onto
each child's behaviours, and an invariant `Inv` of every disciplined parent run; the rely discharge
and the abstract parent (both over the parent's proof observations) may use `Inv`. Over `run2`, for
a comb-profile parent, `Inv r` can be "every probe of `r` solves the parent's equations"
(`Obs_run2.comb_samples`); over E, R-COMB-0's closed store. -/
theorem compose_safe_inv (C : Contract) {M : ObservationModel} {d : M.Design} {K : Type}
    (child : K → Contract) (MK : K → ObservationModel) (dk : (k : K) → (MK k).Design)
    (proj : K → CycleObs M.Probe → CycleObs PortSample) (rank : K → Nat)
    (Inv : List (CycleObs M.Probe) → Prop)
    (hinv : ∀ ch env r, M.Disciplined C.clocking env → M.Runs d ch env r → Inv r)
    (hsat : ∀ k, (child k).Sat (MK k) (dk k))
    (hproj : ∀ k, ProjectsTo M C.clocking d (proj k) (MK k) (child k).clocking (dk k))
    (hrely : ∀ (r : List (CycleObs M.Probe)), Inv r → ∀ k c,
      (∀ c' ≤ c, C.RelyAt (r.map (CycleObs.map (M.sample d))) c') →
      (∀ j c', c' < c → (child j).GuarAt (r.map (proj j)) c') →
      (∀ j, rank j < rank k → (child j).GuarAt (r.map (proj j)) c) →
      (child k).RelyAt (r.map (proj k)) c)
    (hpar : ∀ (r : List (CycleObs M.Probe)), Inv r → ∀ c,
      (∀ c' ≤ c, C.RelyAt (r.map (CycleObs.map (M.sample d))) c') →
      (∀ k, (child k).GuarAt (r.map (proj k)) c) →
      C.GuarAt (r.map (CycleObs.map (M.sample d))) c) :
    M.Safe C.clocking d fun _ b => C.Holds b := by
  rintro ch env b hk ⟨r, hr, rfl⟩
  have hi := hinv ch env r hk hr
  refine compose_holds C child (CycleObs.map (M.sample d)) proj rank r (fun k => ?_)
    (hrely r hi) (hpar r hi)
  obtain ⟨ch', env', hk', hb'⟩ := hproj k ch env r hk hr
  exact (child k).safety_sound (hsat k) ch' env' _ hk' hb'

/-- **R-CONTRACT (safety only) for a design**, `compose_safe_inv` at `Inv := fun _ => True`.

Its rely discharge and abstract parent must hold on EVERY probe list, not only on the parent's runs,
so they cannot use the parent's own processes. For a design with glue processes this is
uninstantiable (READ: the flattened `ripple_fa` drives `c[0] = cin`, `cout = c[N]` and, per bit, the
five port connections `g_bit[i].fa.a = a[i]`, …, `c[i+1] = g_bit[i].fa.cout`, which the abstract
parent needs; `Examples/system-verilog/ripple_fa/gen.lean`, `faProcs`). Use `compose_safe_inv`
there. -/
theorem compose_safe (C : Contract) {M : ObservationModel} {d : M.Design} {K : Type}
    (child : K → Contract) (MK : K → ObservationModel) (dk : (k : K) → (MK k).Design)
    (proj : K → CycleObs M.Probe → CycleObs PortSample) (rank : K → Nat)
    (hsat : ∀ k, (child k).Sat (MK k) (dk k))
    (hproj : ∀ k, ProjectsTo M C.clocking d (proj k) (MK k) (child k).clocking (dk k))
    (hrely : ∀ (r : List (CycleObs M.Probe)) k c,
      (∀ c' ≤ c, C.RelyAt (r.map (CycleObs.map (M.sample d))) c') →
      (∀ j c', c' < c → (child j).GuarAt (r.map (proj j)) c') →
      (∀ j, rank j < rank k → (child j).GuarAt (r.map (proj j)) c) →
      (child k).RelyAt (r.map (proj k)) c)
    (hpar : ∀ (r : List (CycleObs M.Probe)) c,
      (∀ c' ≤ c, C.RelyAt (r.map (CycleObs.map (M.sample d))) c') →
      (∀ k, (child k).GuarAt (r.map (proj k)) c) →
      C.GuarAt (r.map (CycleObs.map (M.sample d))) c) :
    M.Safe C.clocking d fun _ b => C.Holds b :=
  compose_safe_inv C child MK dk proj rank (fun _ => True) (fun _ _ _ _ _ => trivial) hsat hproj
    (fun r _ => hrely r) (fun r _ => hpar r)

end Contract

#print axioms Contract.safety_sound
#print axioms Contract.safety_sound_of_included
#print axioms Contract.safety_sound_of_includedOn
#print axioms Contract.equiv_sound
#print axioms Contract.compose_holds
#print axioms Contract.compose_safe_inv
#print axioms Contract.compose_safe

end LeanModels.Sv.Observe
