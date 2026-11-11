import LeanModels.Sv.Semantics

namespace LeanModels.Sv.Observe

open LeanModels.Sv

/-! ## 1. The interface (DRAFT of trusted text) -/

/-- A port signature: name and width in bits (svGolf's `Sig`). -/
abbrev Sig := String × Nat

/-- **The declared observable set**: a design's input and output ports, each in declaration
order. Trusted statements observe these and nothing else. -/
structure Iface where
  inputs : List Sig
  outputs : List Sig
deriving DecidableEq, Repr

/-- The names of all declared ports, inputs first. -/
def Iface.names (I : Iface) : List String :=
  I.inputs.map Prod.fst ++ I.outputs.map Prod.fst

/-- **The clock and reset ports** a statement names: `clk`, and `rst` with its asserted level. Both are
`none` for a combinational task. The clocking discipline (`ObservationModel.Disciplined`) is relative
to them. -/
structure Clocking where
  clk : Option String := none
  rst : Option (String × Bool) := none
deriving DecidableEq, Repr

/-- **A trusted observation**: the values of the declared ports at one sample point. Built only by
`ObservationModel.sample`, which keeps the ports and drops everything else. -/
structure PortSample where
  vals : List (String × LVec)
deriving BEq, Repr

/-- Read a port of a sample. First binding wins, as everywhere in ls-sv; a name that is not a
declared port reads `none` (`ObservationModel.read_sample`). -/
def PortSample.read (s : PortSample) (n : String) : Option LVec :=
  SvState.lookup s.vals n

/-- **The two samples of one cycle.** `pre`: the state the cycle's clock edge reads (Preponed of the
edge slot). `post`: the state after the cycle closes (Postponed). -/
structure CycleObs (S : Type) where
  pre : S
  post : S
deriving Repr, BEq

/-- Apply `f` to both samples. -/
def CycleObs.map {S T : Type} (f : S → T) (o : CycleObs S) : CycleObs T :=
  ⟨f o.pre, f o.post⟩

@[simp] theorem CycleObs.map_pre {S T : Type} (f : S → T) (o : CycleObs S) :
    (o.map f).pre = f o.pre := rfl

@[simp] theorem CycleObs.map_post {S T : Type} (f : S → T) (o : CycleObs S) :
    (o.map f).post = f o.post := rfl

/-- **An observation model: the backend as a parameter.**

* `Design`, `Choice`, `Env`: the backend's designs, its schedule choices (statements quantify over
  every one), and its environments (a backend detail: statements never inspect one).
* `Probe`: the backend's **proof observation** at a sample point (internal signals included). Only
  proofs read it, for cut points; trusted statements see its restriction to the ports.
* `iface`: the declared observable set; `read`: read a named signal from a proof observation.
* `Disciplined k env`: the **clocking discipline** for the clock and reset ports `k`, an environment
  rely (ARCH-NOTE §4.3). In E: data inputs and reset change only in slots with no posedge of
  `k.clk`, reset is held across an edge when synchronous reset is meant, no time-zero race. In a
  cycle-level backend whose environment is one entry per edge (`run2`): every environment.
* `Runs d ch env r`: the completed run of `d` under `ch` and `env` gives the proof observations `r`,
  one pre/post pair per clock cycle. -/
structure ObservationModel where
  Design : Type
  Choice : Type
  Env : Type
  Probe : Type
  iface : Design → Iface
  Disciplined : Clocking → Env → Prop
  read : Probe → String → Option LVec
  Runs : Design → Choice → Env → List (CycleObs Probe) → Prop

namespace ObservationModel

variable (M : ObservationModel)

/-- The trusted sample of a proof observation: the declared ports of `d`, in `Iface.names` order,
and nothing else. -/
def sample (d : M.Design) (p : M.Probe) : PortSample :=
  ⟨(M.iface d).names.filterMap fun n => (M.read p n).map fun v => (n, v)⟩

/-- **Trusted behaviours**: the observations of a completed run, restricted to the ports. The only
thing a trusted statement says about runs. -/
def Behaves (d : M.Design) (ch : M.Choice) (env : M.Env) (b : List (CycleObs PortSample)) :
    Prop :=
  ∃ r, M.Runs d ch env r ∧ b = r.map (CycleObs.map (M.sample d))

/-- **Progress**: under the clocking discipline `k`, every choice and every disciplined environment
has a completed behaviour. A safety statement is meaningful only beside it (the role `Terminates2`
plays for `⊨₂`). -/
def Progress (k : Clocking) (d : M.Design) : Prop :=
  ∀ ch env, M.Disciplined k env → ∃ b, M.Behaves d ch env b

/-- **A safety statement over trusted observations**: `Q` holds of the interface and the trusted
behaviour, for every choice, every environment disciplined for `k`, and every completed behaviour.
Every statement of this shape transfers along behaviour inclusion (`Safe.of_included`). -/
def Safe (k : Clocking) (d : M.Design) (Q : Iface → List (CycleObs PortSample) → Prop) : Prop :=
  ∀ ch env b, M.Disciplined k env → M.Behaves d ch env b → Q (M.iface d) b

end ObservationModel

/-- `SvState.lookup` over a list built by `filterMap` from a name list: a listed name reads `g`, any
other name reads `none`. -/
theorem lookup_filterMap (g : String → Option LVec) (n : String) :
    ∀ ns : List String,
      SvState.lookup (ns.filterMap fun m => (g m).map fun v => (m, v)) n =
        if n ∈ ns then g n else none
  | [] => by simp [SvState.lookup]
  | m :: ns => by
      have ih := lookup_filterMap g n ns
      cases hg : g m with
      | none =>
          simp only [List.filterMap_cons, hg, Option.map_none, ih, List.mem_cons]
          by_cases hnm : n = m
          · subst hnm; simp [hg]
          · simp [hnm]
      | some v =>
          simp only [List.filterMap_cons, hg, Option.map_some, SvState.lookup, ih, List.mem_cons]
          by_cases hnm : n = m
          · subst hnm; simp [hg]
          · have hmn : (m == n) = false := by simpa using Ne.symm hnm
            simp [hmn, hnm]

/-- **Ports only**: a trusted sample reads a declared port as the backend does, and any other name
as `none`. -/
theorem ObservationModel.read_sample (M : ObservationModel) (d : M.Design) (p : M.Probe)
    (n : String) :
    (M.sample d p).read n = if n ∈ (M.iface d).names then M.read p n else none :=
  lookup_filterMap (M.read p) n _

/-! ### Changing the backend -/

/-- **Behaviour inclusion** between two backends, under the clocking discipline `k`: the same
interface, and every trusted behaviour of `d₁` under `M₁` in a disciplined environment is a trusted
behaviour of `d₂` under `M₂`, under some choice and some disciplined environment. Inputs are part of
the samples, so no translation of environments is needed. -/
def Included (M₁ M₂ : ObservationModel) (k : Clocking) (d₁ : M₁.Design) (d₂ : M₂.Design) : Prop :=
  M₁.iface d₁ = M₂.iface d₂ ∧
    ∀ ch₁ e₁ b, M₁.Disciplined k e₁ → M₁.Behaves d₁ ch₁ e₁ b →
      ∃ ch₂ e₂, M₂.Disciplined k e₂ ∧ M₂.Behaves d₂ ch₂ e₂ b

/-- **Swapping the backend is a theorem**: a safety statement proved over `M₂` holds over `M₁`
whenever `M₁`'s behaviours are included in `M₂`'s. -/
theorem Safe.of_included {M₁ M₂ : ObservationModel} {k : Clocking} {d₁ : M₁.Design}
    {d₂ : M₂.Design} {Q : Iface → List (CycleObs PortSample) → Prop}
    (hinc : Included M₁ M₂ k d₁ d₂) (h : M₂.Safe k d₂ Q) : M₁.Safe k d₁ Q := by
  intro ch₁ e₁ b hk hb
  obtain ⟨ch₂, e₂, hk₂, hb₂⟩ := hinc.2 ch₁ e₁ b hk hb
  have := h ch₂ e₂ b hk₂ hb₂
  rw [← hinc.1] at this
  exact this

/-! ### Changing the backend on restricted environments (the general form)

Agent A found (`not_included_run2_E0`, branch `arch-x1`) that `run2` → E inclusion is false without
an environment predicate: `run2` stores an ill-typed stimulus value as given, while E converts it to
the port's width. So inclusion is stated on the environments satisfying a predicate `P`, which may
depend on the designs (`IncludedOn`, A's definition verbatim, moved here). `Included` is the case
`P = fun _ => True` (`included_iff_includedOn`). It keeps its own definition, so every statement and
proof written against it still compiles. -/

/-- **Behaviour inclusion on the environments satisfying `P`** (the general form). The same
interface, and every trusted behaviour of `d₁` under `M₁`, in an environment satisfying `P` and the
clocking discipline, is a trusted behaviour of `d₂` under `M₂` in some disciplined environment. -/
def IncludedOn (M₁ M₂ : ObservationModel) (k : Clocking) (d₁ : M₁.Design) (d₂ : M₂.Design)
    (P : M₁.Env → Prop) : Prop :=
  M₁.iface d₁ = M₂.iface d₂ ∧
    ∀ ch₁ e₁ b, P e₁ → M₁.Disciplined k e₁ → M₁.Behaves d₁ ch₁ e₁ b →
      ∃ ch₂ e₂, M₂.Disciplined k e₂ ∧ M₂.Behaves d₂ ch₂ e₂ b

/-- `Included` is `IncludedOn` with no restriction. -/
theorem included_iff_includedOn {M₁ M₂ : ObservationModel} {k : Clocking} {d₁ : M₁.Design}
    {d₂ : M₂.Design} : Included M₁ M₂ k d₁ d₂ ↔ IncludedOn M₁ M₂ k d₁ d₂ (fun _ => True) :=
  ⟨fun h => ⟨h.1, fun ch e b _ hk hb => h.2 ch e b hk hb⟩,
   fun h => ⟨h.1, fun ch e b hk hb => h.2 ch e b trivial hk hb⟩⟩

/-- Unrestricted inclusion gives inclusion on any environments. -/
theorem IncludedOn.of_included {M₁ M₂ : ObservationModel} {k : Clocking} {d₁ : M₁.Design}
    {d₂ : M₂.Design} (h : Included M₁ M₂ k d₁ d₂) (P : M₁.Env → Prop) : IncludedOn M₁ M₂ k d₁ d₂ P :=
  ⟨h.1, fun ch e b _ hk hb => h.2 ch e b hk hb⟩

/-- Narrowing the environments keeps inclusion. -/
theorem IncludedOn.mono {M₁ M₂ : ObservationModel} {k : Clocking} {d₁ : M₁.Design}
    {d₂ : M₂.Design} {P Q : M₁.Env → Prop} (hQP : ∀ e, Q e → P e) (h : IncludedOn M₁ M₂ k d₁ d₂ P) :
    IncludedOn M₁ M₂ k d₁ d₂ Q :=
  ⟨h.1, fun ch e b hq hk hb => h.2 ch e b (hQP e hq) hk hb⟩

/-- **A safety statement on the environments satisfying `P`**: `Safe` restricted to them. -/
def ObservationModel.SafeOn (M : ObservationModel) (k : Clocking) (d : M.Design)
    (P : M.Env → Prop) (Q : Iface → List (CycleObs PortSample) → Prop) : Prop :=
  ∀ ch env b, P env → M.Disciplined k env → M.Behaves d ch env b → Q (M.iface d) b

/-- `Safe` is `SafeOn` with no restriction. -/
theorem ObservationModel.safeOn_true_iff (M : ObservationModel) {k : Clocking} {d : M.Design}
    {Q : Iface → List (CycleObs PortSample) → Prop} :
    M.SafeOn k d (fun _ => True) Q ↔ M.Safe k d Q :=
  ⟨fun h ch e b hk hb => h ch e b trivial hk hb, fun h ch e b _ hk hb => h ch e b hk hb⟩

/-- **Swapping the backend on restricted environments**: a safety statement proved over `M₂` holds
over `M₁` on every environment where `M₁`'s behaviours are included in `M₂`'s. -/
theorem SafeOn.of_includedOn {M₁ M₂ : ObservationModel} {k : Clocking} {d₁ : M₁.Design}
    {d₂ : M₂.Design} {P : M₁.Env → Prop} {Q : Iface → List (CycleObs PortSample) → Prop}
    (hinc : IncludedOn M₁ M₂ k d₁ d₂ P) (h : M₂.Safe k d₂ Q) : M₁.SafeOn k d₁ P Q := by
  intro ch₁ e₁ b hp hk hb
  obtain ⟨ch₂, e₂, hk₂, hb₂⟩ := hinc.2 ch₁ e₁ b hp hk hb
  have := h ch₂ e₂ b hk₂ hb₂
  rw [← hinc.1] at this
  exact this


/-! ## 3. `Obs_E`: signature only

What the authority E (ARCH-NOTE §4.1) must supply to be an observation backend. Nothing is defined
about E; the fields name its types and functions as §4.1 does. -/

/-- **The signature of E as an observation backend.**

* `Elab`, `Choice`, `Env`, `Config`: elaborated designs, legal process-atomic choices, environments
  (event-level, with clocks as ports), configurations.
* `Disciplined k env`: the clocking discipline (§4.3), in E's own vocabulary.
* `Behaves e env ch b`: slot `t` closes at `b t` (§4.1); `preponed b t` is the configuration of slot
  `t` before anything in it runs.
* `cycles env`: the number of clock edges of a finite environment prefix; `edgeSlot env c` the slot
  of the `c`-th one.
* `read`: read a declared observable (port, or a probe for cut points) from a configuration. -/
structure ESig where
  Elab : Type
  Choice : Type
  Env : Type
  Config : Type
  iface : Elab → Iface
  Disciplined : Clocking → Env → Prop
  read : Config → String → Option LVec
  Behaves : Elab → Env → Choice → (Nat → Config) → Prop
  preponed : (Nat → Config) → Nat → Config
  cycles : Env → Nat
  edgeSlot : Env → Nat → Nat

/-- **`Obs_E`**: E as an observation backend. Cycle `c` observes the Preponed and the Postponed
samples of the slot of the `c`-th clock edge. -/
@[reducible] def Obs_E (E : ESig) : ObservationModel where
  Design := E.Elab
  Choice := E.Choice
  Env := E.Env
  Probe := E.Config
  iface := E.iface
  Disciplined := E.Disciplined
  read := E.read
  Runs e ch env r := ∃ b, E.Behaves e env ch b ∧
    r = (List.range (E.cycles env)).map fun c =>
      ⟨E.preponed b (E.edgeSlot env c), b (E.edgeSlot env c)⟩

end LeanModels.Sv.Observe
