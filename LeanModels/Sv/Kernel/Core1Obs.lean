import LeanModels.Sv.Kernel.Core1Edge
import LeanModels.Sv.Kernel.Core0Obs

/-!
# E-core-1 as an observation backend, and inclusion up to hidden ports (`LeanModels.Sv.Kernel`)

D-X1h, the backend for the Obs-level inclusion. **Status:** the backend and `progress_E1` are
derived from E (E-core-1's edge fragment, `Core1Edge.lean`); `Safe.of_includedOnPorts` is a
backend-generic transport lemma. Imported by no existing module.

* `E1 clk`, `Obs_E1 clk`: E-core-1 as an `ESig`. The environment is one entry per clock cycle, as
  `run2`'s. The backend drives the clock `clk` itself: slot `2c` applies entry `c` with `clk` low,
  slot `2c + 1` raises `clk` and changes nothing else. Cycle `c` is sampled at its edge slot
  `2c + 1`. Data and reset change only in clock-low slots, so the slot list satisfies
  `Core1Disc.Disciplined isPosedge` by construction (JUDGED; not proved here). It is the harness's
  `clockExpand` except that the high slot does not re-drive the entry's data, which is the same
  input values again (JUDGED). `Disciplined k` asks only that `k`'s clock be `clk`. Environments
  that change data in other slots are the general composition's (X1-NOTE §12).
* `progress_E1`: every edge-profile design (`EdgeProfile`) has a behaviour under every choice and
  every environment (R-EDGE closes every slot, whatever its ready set).
* `hidePorts`, `IncludedOnPorts`: `Included` with the behaviours compared after hiding the
  ports `xs`. `Safe.of_includedOnPorts` transports a statement that does not read them. The clock
  is the intended use (TASKV2 decision on the clock port, JUDGED): E's samples show the clock E
  drives (low before the edge, high after), `run2`'s show the stimulus's value.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv.Observe

set_option autoImplicit false

/-! ## The backend -/

/-- Slot `t`'s input events when the backend drives the clock `clk`: slot `2c` applies cycle entry
`c` with `clk` low, slot `2c + 1` raises `clk`. -/
def slotEntry1 (clk : String) (env : List SvState) (t : Nat) : SvState :=
  if t % 2 = 0 then SvState.set ((env[t / 2]?).getD []) clk (LVec.ofNat 1 0)
  else [(clk, LVec.ofNat 1 1)]

/-- Time zero: the startup store, nothing ready. -/
def Config1.init (E : Elab1) : Config1 := { store := E.base.initStore, active := [], nba := [] }

/-- **A behaviour of E-core-1**: slot `t` closes at `cfg t`, each slot opened by its input events. -/
def Behaves1 (E : Elab1) (clk : String) (env : List SvState) (ch : Choice) (cfg : Nat → Config1) :
    Prop :=
  SlotCloses1 E ch (Config1.nextSlot E (Config1.init E) (slotEntry1 clk env 0)) (cfg 0) ∧
  ∀ t, SlotCloses1 E ch (Config1.nextSlot E (cfg t) (slotEntry1 clk env (t + 1))) (cfg (t + 1))

/-- **E-core-1 as an `ESig`**, driving the clock `clk`: two slots per cycle, the edge slot odd. -/
def E1 (clk : String) : ESig where
  Elab := Elab1
  Choice := Choice
  Env := List SvState
  Config := SvState
  iface e := ⟨inputSigs e.design, outputSigs e.design⟩
  Disciplined k _ := k.clk = some clk
  read := SvState.lookup
  Behaves e env ch b := ∃ cfg, Behaves1 e clk env ch cfg ∧ ∀ t, b t = e.base.view (cfg t).store
  preponed b t := b (t - 1)
  cycles env := env.length
  edgeSlot _ c := 2 * c + 1

/-- **`Obs_E1`**: E-core-1 as an observation backend. -/
abbrev Obs_E1 (clk : String) : ObservationModel := Obs_E (E1 clk)

/-! ## Slots close, once, at typed stores -/

theorem step1_typed {E : Elab1} {ch : Choice} {c c' : Config1} (h : step1 E ch c = .next c')
    (hT : E.base.Typed c.store) : E.base.Typed c'.store := by
  unfold step1 at h
  split at h
  · split at h
    · cases h; exact hT
    · cases h
  · split at h
    · cases h
    · cases h; exact Elab1.typed_commit _ hT

theorem Steps1.typed {E : Elab1} {ch : Choice} {c c' : Config1} (h : Steps1 E ch c c')
    (hT : E.base.Typed c.store) : E.base.Typed c'.store := by
  induction h with
  | refl => exact hT
  | head hs _ ih => exact ih (step1_typed hs hT)

/-- A slot closes at one configuration (`step1` is a function). -/
theorem SlotCloses1.unique {E : Elab1} {ch : Choice} {c c₁ c₂ : Config1}
    (h₁ : SlotCloses1 E ch c c₁) (h₂ : SlotCloses1 E ch c c₂) : c₁ = c₂ := by
  obtain ⟨hs₁, hc₁⟩ := h₁
  obtain ⟨hs₂, hc₂⟩ := h₂
  revert hs₂
  induction hs₁ with
  | refl _ =>
      intro hs₂
      cases hs₂ with
      | refl => rfl
      | head h _ => rw [hc₁] at h; cases h
  | head h _ ih =>
      intro hs₂
      cases hs₂ with
      | refl => rw [hc₂] at h; cases h
      | head h' hs' => rw [h] at h'; cases h'; exact ih hc₁ hs'

/-- **Every slot of an edge-profile design closes**, at a typed store (R-EDGE, whatever the input
events fire). -/
theorem closes1 {E : Elab1} (hP : EdgeProfile E) (ch : Choice) {c : Config1}
    (hT : E.base.Typed c.store) (entry : SvState) :
    ∃ c', SlotCloses1 E ch (Config1.nextSlot E c entry) c' ∧ E.base.Typed c'.store := by
  have hT' := hT.applyInputs entry
  obtain ⟨c', hcl, -⟩ := rEdge hP ch hT'
    (act := E.triggered (E.base.view c.store) (E.base.view (E.base.applyInputs c.store entry)))
    (List.nodup_range.filter _) (fun p hp => List.mem_range.mp (List.mem_filter.mp hp).1) c.k
  exact ⟨c', hcl, hcl.1.typed hT'⟩

/-- The behaviour R-EDGE gives, one slot at a time. -/
noncomputable def chain1 {E : Elab1} (hP : EdgeProfile E) (ch : Choice) (clk : String)
    (env : List SvState) : Nat → { c : Config1 // E.base.Typed c.store }
  | 0 =>
      let h := closes1 hP ch (c := Config1.init E) E.base.typed_initStore (slotEntry1 clk env 0)
      ⟨Classical.choose h, (Classical.choose_spec h).2⟩
  | t + 1 =>
      let h := closes1 hP ch (chain1 hP ch clk env t).2 (slotEntry1 clk env (t + 1))
      ⟨Classical.choose h, (Classical.choose_spec h).2⟩

/-- **Progress over `Obs_E1`** for every edge-profile design. -/
theorem progress_E1 {E : Elab1} (hP : EdgeProfile E) (clk : String) (k : Clocking) :
    (Obs_E1 clk).Progress k E := by
  intro ch env _
  have hB : Behaves1 E clk env ch fun t => (chain1 hP ch clk env t).1 :=
    ⟨(Classical.choose_spec (closes1 hP ch (c := Config1.init E) E.base.typed_initStore
        (slotEntry1 clk env 0))).1,
      fun t => (Classical.choose_spec (closes1 hP ch (chain1 hP ch clk env t).2
        (slotEntry1 clk env (t + 1)))).1⟩
  exact ⟨_, _, ⟨_, ⟨_, hB, fun _ => rfl⟩, rfl⟩, rfl⟩

/-! ## Inclusion up to hidden ports -/

/-- A sample with the ports `xs` hidden. -/
def hidePorts (xs : List String) (s : PortSample) : PortSample :=
  ⟨s.vals.filter fun nv => !decide (nv.1 ∈ xs)⟩

/-- Behaviours with the ports `xs` hidden. -/
def hideB (xs : List String) (b : List (CycleObs PortSample)) : List (CycleObs PortSample) :=
  b.map (CycleObs.map (hidePorts xs))

/-- **Inclusion up to the hidden ports `xs`**: `Included`, with the behaviours compared after
hiding `xs`. -/
def IncludedOnPorts (M₁ M₂ : ObservationModel) (k : Clocking) (d₁ : M₁.Design) (d₂ : M₂.Design)
    (xs : List String) : Prop :=
  M₁.iface d₁ = M₂.iface d₂ ∧
    ∀ ch₁ e₁ b₁, M₁.Disciplined k e₁ → M₁.Behaves d₁ ch₁ e₁ b₁ →
      ∃ ch₂ e₂ b₂, M₂.Disciplined k e₂ ∧ M₂.Behaves d₂ ch₂ e₂ b₂ ∧ hideB xs b₁ = hideB xs b₂

/-- **A statement that does not read the hidden ports moves along `IncludedOnPorts`.** -/
theorem Safe.of_includedOnPorts {M₁ M₂ : ObservationModel} {k : Clocking} {d₁ : M₁.Design}
    {d₂ : M₂.Design} {xs : List String} {Q : Iface → List (CycleObs PortSample) → Prop}
    (hinc : IncludedOnPorts M₁ M₂ k d₁ d₂ xs)
    (hQ : ∀ I b b', hideB xs b = hideB xs b' → Q I b' → Q I b) (h : M₂.Safe k d₂ Q) :
    M₁.Safe k d₁ Q := by
  intro ch₁ e₁ b hk hb
  obtain ⟨ch₂, e₂, b₂, hk₂, hb₂, hh⟩ := hinc.2 ch₁ e₁ b hk hb
  have := h ch₂ e₂ b₂ hk₂ hb₂
  rw [← hinc.1] at this
  exact hQ _ _ _ hh this

/-- Hiding keeps every other port. -/
theorem read_hidePorts {xs : List String} {n : String} (hn : n ∉ xs) (s : PortSample) :
    (hidePorts xs s).read n = s.read n := by
  obtain ⟨vals⟩ := s
  simp only [hidePorts, PortSample.read]
  induction vals with
  | nil => rfl
  | cons nv vals ih =>
      by_cases h : nv.1 ∈ xs
      · have hne : (nv.1 == n) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hn h
        simp [h, SvState.lookup, hne, ih]
      · simp [h, SvState.lookup, ih]

/-- Two samples of the same ports agree after hiding `xs` when they read alike off `xs`. -/
theorem sample_hide_congr {M M' : ObservationModel} {d : M.Design} {d' : M'.Design}
    (hi : M.iface d = M'.iface d') {p : M.Probe} {p' : M'.Probe} {xs : List String}
    (h : ∀ n, n ∉ xs → M.read p n = M'.read p' n) :
    hidePorts xs (M.sample d p) = hidePorts xs (M'.sample d' p') := by
  simp only [ObservationModel.sample, hidePorts, hi, PortSample.mk.injEq]
  induction (M'.iface d').names with
  | nil => rfl
  | cons n ns ih =>
      by_cases hn : n ∈ xs
      · cases hm : M.read p n <;> cases hm' : M'.read p' n <;>
          simp [hm, hm', hn, ih]
      · rw [List.filterMap_cons, List.filterMap_cons, h n hn]
        cases hm' : M'.read p' n <;> simp [hn, ih]

#print axioms SlotCloses1.unique
#print axioms closes1
#print axioms progress_E1
#print axioms Safe.of_includedOnPorts
#print axioms read_hidePorts
#print axioms sample_hide_congr

end LeanModels.Sv.Kernel
