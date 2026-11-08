import LeanModels.Sv.Spec2

/-!
# The observation interface, its `run2` backend, and the signature of its E backend

**Status labels** (EXECUTION-PLAN §1). This module is imported by nothing.

* §1, the interface (`Iface`, `Clocking`, `PortSample`, `CycleObs`, `ObservationModel`, `Behaves`,
  `Progress`, `Safe`, `Included`): **DRAFT of trusted statement surface.** It becomes trusted text only
  after Thomas reviews it; until then nothing trusted imports it. Approved by the lead at cf88008b and
  revised by the rulings of 2026-11-02 (Day 4): inputs are read from the pre sample, and the clocking
  discipline is an environment rely.
* §2, `Obs_run2` and the split of `cycleStep2` at the pre sample: **provisional over `run2`.** It is
  `run2` (Design2's cycle model), not SystemVerilog. A proof over `Obs_run2` is a statement about
  SystemVerilog only once R-DESIGN2 (`RDesign2` below) is proved.
* §3, `Obs_E`: **signature only.** Nothing about E is defined here: `ESig` lists what E must supply,
  and `Obs_E` turns any such E into an observation model. `RDesign2` states the legacy transport as
  behaviour inclusion between the two models.

## What the interface is (ARCH-NOTE §4.1 "Observation", §4.5, review verdicts 6 and 7)

A trusted statement sees a design only through:

* its **declared observable set**, the ports (`Iface`: inputs and outputs, name and width, in
  declaration order);
* the **trusted samples**, two per cycle (`CycleObs PortSample`):
  - `pre`: the state the cycle's clock edge reads. Inputs applied, comb logic settled, any
    asynchronous reset event run with its NBA committed and comb settled again, and no edge process
    run yet. This is E's Preponed sample of the clock-edge slot: what flops and SVA sample, and where
    Mealy outputs show.
  - `post`: the state after the cycle closes (E's Postponed sample; `run2`'s snapshot);
* the **clocking discipline**, an environment rely (`ObservationModel.Disciplined`, ruling (c)):
  statements quantify over the environments the backend calls disciplined for the task's clock and
  reset ports.

**Inputs are read from the pre sample** (ruling (a), Day 4). An input's value in a cycle is the value
it HOLDS at the cycle's edge, which is E's convention, and inputs are ports. So the environment is a
backend detail: no environment view appears in trusted text, and changing the backend needs no
translation of environments (`Included`). The price is non-vacuity. A design that drives its own
input ports could keep "the pre sample holds known inputs" false. Statements therefore carry a
receptiveness conjunct (`Receptive`, in the Task v2 skeleton draft): every input sequence is seen in
the pre samples of some behaviour. Day 1's convention ("the stimulus entry binds the input"), which is
`run2`'s, survives only as the separately named `_stim` variants of the svGolf drafts.

The backend is a parameter (`ObservationModel`): its design, choice (schedule), environment and
proof-observation types, how it reads a named signal, and its completed runs. Swapping the backend
is a theorem (`Safe.of_included`), not a change of definition under the statements.

**Two observation types** (review verdict 7). `PortSample` is the trusted type: the trusted sample of
a run is the restriction of the backend's proof observation to the declared ports
(`ObservationModel.sample`), so reading an internal signal from it gives `none` (`read_sample`).
`ObservationModel.Probe` is the proof type: the backend's whole state at a sample point (for
`run2`, the `SvState`), for cut-point lemmas only. Trusted statements are stated over `Behaves`
and never mention `Probe` or `Runs`.

## The pre sample over `run2` (lead's ruling, 2026-11-02: pre = st2, not st1)

`cycleStep2` (READ `Sem2.lean:695-708`) computes `st1` (inputs applied, settled), then `st2` (the
reset-event phase: `alwaysFFR` bodies whose reset made a negedge run, their NBA is committed, and comb
logic settles again), then runs the edge pass from `st2`. The pre sample is `st2`, the state the edge
pass starts from (`cyclePre2`). `st1 = st2` whenever no reset event fires (`resetPhase2_of_nil`), which
covers every design without `alwaysFFR`.

Why `st2`: under the clocking discipline (ARCH-NOTE §4.3, `Disciplined`), E has data inputs and reset
change only in slots with no `clk` posedge. A reset negedge therefore triggers the async-reset process
in an earlier slot, whose NBA region commits the reset values before that slot closes. So the
Preponed sample of the next clock-edge slot already holds the reset values, as `st2` does. With
`st1`, R-DESIGN2 would be false on every cycle with a reset event, because `st1` still holds the old
register. (The pin3 rows of `Sem2.lean` record the same fact on the simulator side: "reset values are
visible to the posedge samplers".)

## Debts recorded at promotion (ruling (e))

* `Observe.Sig` duplicates svGolf's `Sig` (both `String × Nat`); one of them goes at promotion.
* The svGolf drafts (`svgolf/design/architecture/`) place definitions in the `SvGolf.CombTask` and
  `SvGolf.Seq.SeqTask` namespaces so that dot notation works. Check those names for clashes when
  promoting them into `SvGolf/Task.lean`.

## What is proved here

* `cycleStep2_eq_pre_post`: `cycleStep2 = cyclePre2 >>= cyclePost2` (decomposition at the pre sample).
* `pre_sample_spec`: what the pre sample is, in source terms (the five clauses above), and
  `resetPhase2_of_nil`: pre = st1 when no reset event fires.
* `run2_eq_runObs2`: the new run function `runObs2` (pre and post samples per cycle) agrees with `run2`
  on the post samples, failures included (`run2` itself is unchanged), for a design with no
  qualified `case` (`hnq`; see `Obs_run2`).
* `Obs_run2.runs2_of_runs`, `Obs_run2.runs_of_runs2`, `Obs_run2.progress_iff` (`Progress ↔
  Terminates2`, under `hnq`), `Obs_run2.progress_of_terminates`: the bridges a statement restated over
  `Obs_run2` uses to move existing records.
-/

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

/-! ## 2. The `run2` backend (provisional over `run2`) -/

/-! ### `cycleStep2` split at the pre sample

`cyclePre2` and `cyclePost2` are `cycleStep2`'s code, cut where the edge pass starts. `run2` is not
changed; `cycleStep2_eq_pre_post` proves the cut is exact. -/

/-- The reset-event phase of `cycleStep2`: the `alwaysFFR` processes whose reset made a negedge
between `prev` (the previous snapshot) and `st1` run once in σ order, their NBA is committed, and comb
logic settles again. With no reset event, nothing happens (`resetPhase2_of_nil`). -/
def resetPhase2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (prev st1 : SvState) (k1 : Nat) :
    Res (SvState × Nat) :=
  let rdy := d.resetIndices prev st1
  match rdy with
  | [] => pure (st1, k1)
  | _ => do
      let (str, nbar) ← resetPass2 d fuel st1 [] (σ.choose k1 rdy)
      combSettle2 d σ fuel (commitNba2 str nbar) (k1 + 1)

/-- **The part of a cycle before the edge processes**, whose result is the pre sample: apply the
inputs, settle (`st1`), then the reset-event phase (`st2`). -/
def cyclePre2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (inputs st : SvState) (k : Nat) :
    Res (SvState × Nat) := do
  let (st1, k1) ← combSettle2 d σ fuel (applyInputs2 d inputs st) k
  resetPhase2 d σ fuel st st1 k1

/-- **The edge part of a cycle**, from the pre sample: every edge process once in σ order, NBA
commit, settle. Its result is the post sample (`run2`'s snapshot). -/
def cyclePost2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (pre : SvState) (k2 : Nat) :
    Res (SvState × Nat) := do
  let (st3, nba) ← edgePass2 d fuel pre [] (σ.choose k2 d.edgeIndices)
  combSettle2 d σ fuel (commitNba2 st3 nba) (k2 + 1)

/-- **The decomposition**: one `cycleStep2` is `cyclePre2` followed by `cyclePost2` from the pre
sample. -/
theorem cycleStep2_eq_pre_post (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (inputs st : SvState) (k : Nat) :
    cycleStep2 d σ fuel inputs st k =
      (cyclePre2 d σ fuel inputs st k >>= fun p => cyclePost2 d σ fuel p.1 p.2) := by
  dsimp only [cycleStep2, cyclePre2, resetPhase2, cyclePost2]
  generalize combSettle2 d σ fuel (applyInputs2 d inputs st) k = r1
  cases r1 with
  | timeout => rfl
  | unsupported _ => rfl
  | ok p =>
      obtain ⟨st1, k1⟩ := p
      dsimp only [Res.ok_bind]
      generalize d.resetIndices st st1 = rdy
      cases rdy with
      | nil => rfl
      | cons i is =>
          dsimp only
          generalize resetPass2 d fuel st1 [] (σ.choose k1 (i :: is)) = r2
          cases r2 with
          | timeout => rfl
          | unsupported _ => rfl
          | ok q =>
              obtain ⟨str, nbar⟩ := q
              dsimp only [Res.ok_bind]

/-- With no reset event, the reset-event phase changes nothing: the pre sample is `st1`. -/
theorem resetPhase2_of_nil {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {prev st1 : SvState}
    {k1 : Nat} (h : d.resetIndices prev st1 = []) :
    resetPhase2 d σ fuel prev st1 k1 = .ok (st1, k1) := by
  unfold resetPhase2
  simp only [h]
  rfl

/-- With a reset event, the reset-event phase runs the ready `alwaysFFR` bodies, commits their NBA
and settles. -/
theorem resetPhase2_of_ne_nil {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {prev st1 : SvState}
    {k1 : Nat} (h : d.resetIndices prev st1 ≠ []) :
    resetPhase2 d σ fuel prev st1 k1 =
      (resetPass2 d fuel st1 [] (σ.choose k1 (d.resetIndices prev st1)) >>= fun q =>
        combSettle2 d σ fuel (commitNba2 q.1 q.2) (k1 + 1)) := by
  unfold resetPhase2
  generalize hr : d.resetIndices prev st1 = rdy at h
  cases rdy with
  | nil => exact absurd rfl h
  | cons i is => simp only

/-- **Settled**: the state a successful `combSettle2` returns is a fixpoint of one σ-ordered pass of
the comb processes. -/
theorem combSettle2_settled {d : Design2} {σ : ScheduleOracle} :
    ∀ {fuel : Nat} {s : SvState} {k : Nat} {s' : SvState} {k' : Nat},
      combSettle2 d σ fuel s k = .ok (s', k') →
        ∃ f j, combPass2 d f s' (σ.choose j d.combIndices) = .ok s'
  | 0, _, _, _, _, h => by simp [combSettle2] at h
  | fuel + 1, s, k, s', k', h => by
      unfold combSettle2 at h
      cases hp : combPass2 d fuel s (σ.choose k d.combIndices) with
      | timeout => rw [hp] at h; cases h
      | unsupported _ => rw [hp] at h; cases h
      | ok t =>
          rw [hp] at h
          simp only [Res.ok_bind] at h
          by_cases heq : (t == s) = true
          · rw [if_pos heq] at h
            simp only [Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            have hts : t = s := by simpa using heq
            subst hts
            exact ⟨fuel, k, hp⟩
          · rw [if_neg heq] at h
            exact combSettle2_settled h

/-! ### One cycle and one run with pre and post samples -/

/-- One cycle with both samples: the pre sample (`cyclePre2`) and the post sample (`cyclePost2`
from it). -/
def cycleObs2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (inputs st : SvState) (k : Nat) :
    Res (CycleObs SvState × Nat) := do
  let (pre, k2) ← cyclePre2 d σ fuel inputs st k
  let (post, k') ← cyclePost2 d σ fuel pre k2
  pure (⟨pre, post⟩, k')

/-- `cycleStep2` is `cycleObs2` with the pre sample dropped. -/
theorem cycleStep2_eq_cycleObs2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (inputs st : SvState) (k : Nat) :
    cycleStep2 d σ fuel inputs st k =
      (cycleObs2 d σ fuel inputs st k >>= fun p => pure (p.1.post, p.2)) := by
  rw [cycleStep2_eq_pre_post]
  unfold cycleObs2
  cases cyclePre2 d σ fuel inputs st k with
  | timeout => rfl
  | unsupported _ => rfl
  | ok p =>
      obtain ⟨pre, k2⟩ := p
      simp only [Res.ok_bind]
      cases cyclePost2 d σ fuel pre k2 with
      | timeout => rfl
      | unsupported _ => rfl
      | ok q => rfl

/-- **What the pre sample is** (the lead's wording): the state after the inputs are applied, comb
logic has settled, and any asynchronous reset event has run with its NBA committed and comb logic
settled again, before the edge processes run. Clause by clause, for a successful cycle observation
`o` from snapshot `st` under stimulus entry `inputs`:

1. the inputs are applied and comb logic settles, to `st1`;
2. with no reset event (`d.resetIndices st st1 = []`), the pre sample is `st1`;
3. with a reset event, the ready `alwaysFFR` bodies run from `st1`, their NBA is committed, and comb
   logic settles to the pre sample;
4. the pre sample is settled: one σ-ordered comb pass leaves it unchanged;
5. the post sample is the edge part (`cyclePost2`: edge processes, NBA, settle) run from the pre
   sample, so no edge process has run in the pre sample. -/
theorem pre_sample_spec {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {inputs st : SvState}
    {k : Nat} {o : CycleObs SvState} {k' : Nat}
    (h : cycleObs2 d σ fuel inputs st k = .ok (o, k')) :
    ∃ st1 k1 k2,
      combSettle2 d σ fuel (applyInputs2 d inputs st) k = .ok (st1, k1) ∧
      (d.resetIndices st st1 = [] → o.pre = st1 ∧ k2 = k1) ∧
      (d.resetIndices st st1 ≠ [] → ∃ str nbar,
        resetPass2 d fuel st1 [] (σ.choose k1 (d.resetIndices st st1)) = .ok (str, nbar) ∧
        combSettle2 d σ fuel (commitNba2 str nbar) (k1 + 1) = .ok (o.pre, k2)) ∧
      (∃ f j, combPass2 d f o.pre (σ.choose j d.combIndices) = .ok o.pre) ∧
      cyclePost2 d σ fuel o.pre k2 = .ok (o.post, k') := by
  unfold cycleObs2 cyclePre2 at h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨⟨pre, k2⟩, ⟨⟨st1, k1⟩, h1, h2⟩, ⟨post, k3⟩, h3, h4⟩ := h
  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h4
  obtain ⟨rfl, rfl⟩ := h4
  refine ⟨st1, k1, k2, h1, ?_, ?_, ?_, h3⟩
  · intro hn
    rw [resetPhase2_of_nil hn] at h2
    simp only [Res.ok.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1.symm, h2.2.symm⟩
  · intro hn
    rw [resetPhase2_of_ne_nil hn, Res.bind_eq_ok] at h2
    obtain ⟨⟨str, nbar⟩, hr, hs⟩ := h2
    exact ⟨str, nbar, hr, hs⟩
  · by_cases hn : d.resetIndices st st1 = []
    · rw [resetPhase2_of_nil hn] at h2
      simp only [Res.ok.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      exact combSettle2_settled h1
    · rw [resetPhase2_of_ne_nil hn, Res.bind_eq_ok] at h2
      obtain ⟨_, _, hs⟩ := h2
      exact combSettle2_settled hs

/-- A run with both samples per cycle: `runFrom2`'s recursion over `cycleObs2`. -/
def runFromObs2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) :
    SvState → Nat → List SvState → Res (List (CycleObs SvState))
  | _, _, [] => .ok []
  | st, k, inputs :: rest => do
      let (o, k') ← cycleObs2 d σ fuel inputs st k
      let os ← runFromObs2 d σ fuel o.post k' rest
      pure (o :: os)

/-- `run2` with both samples per cycle (same start: `initState2`, counter `0`). -/
def runObs2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    Res (List (CycleObs SvState)) :=
  do
    run2ClockGuard d
    runFromObs2 d σ fuel (initState2 d) 0 stim

/-- **Agreement with `runFrom2` on the post samples**, failures included. -/
theorem runFrom2_eq_runFromObs2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) :
    ∀ (stim : List SvState) (st : SvState) (k : Nat),
      runFrom2 d σ fuel st k stim =
        (runFromObs2 d σ fuel st k stim >>= fun os => pure (os.map CycleObs.post))
  | [], st, k => rfl
  | inputs :: rest, st, k => by
      have ih := runFrom2_eq_runFromObs2 d σ fuel rest
      simp only [runFrom2, runFromObs2, cycleStep2_eq_cycleObs2]
      cases cycleObs2 d σ fuel inputs st k with
      | timeout => rfl
      | unsupported _ => rfl
      | ok p =>
          obtain ⟨o, k'⟩ := p
          simp only [Res.ok_bind, Res.pure_eq, ih]
          cases runFromObs2 d σ fuel o.post k' rest <;> rfl

/-! `runObs2` omits `run2`'s qualified-case trace check (master `2218821b`: `run2` runs
`validateTraceChecks2` after `runFrom2` when a process has a `unique`/`unique0`/`priority` case). For
such a design `runObs2` is NOT `run2`: it completes on runs whose claim is violated, where `run2`
refuses loudly. `hnq` (no qualified case) is exactly the condition under which the two agree; the
lemmas below that need it take it, the others hold for every design. -/

/-- **`runObs2` agrees with `run2` on the post samples**, failures included, for a design with no
qualified `case`. -/
theorem run2_eq_runObs2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState)
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false) :
    run2 d σ fuel stim = (runObs2 d σ fuel stim >>= fun os => pure (os.map CycleObs.post)) := by
  unfold run2 runObs2
  cases hg : run2ClockGuard d with
  | timeout => rfl
  | unsupported msg => rfl
  | ok u =>
      simp only [hg, Res.ok_bind, Res.pure_eq, hnq, if_false]
      rw [runFrom2_eq_runFromObs2]
      cases runFromObs2 d σ fuel (initState2 d) 0 stim <;> rfl

/-- A completed `run2` is the post samples of a completed `runObs2` (every design). -/
theorem runObs2_of_run2_ok {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {stim tr : List SvState}
    (h : run2 d σ fuel stim = .ok tr) :
    ∃ os, runObs2 d σ fuel stim = .ok os ∧ tr = os.map CycleObs.post := by
  have hg : run2ClockGuard d = .ok () := by
    cases hq : run2ClockGuard d with
    | ok u => simpa using hq
    | timeout => simp [run2, hq] at h
    | unsupported msg => simp [run2, hq] at h
  have h1 := run2_from_ok h
  rw [runFrom2_eq_runFromObs2, Res.bind_eq_ok] at h1
  obtain ⟨os, h2, h3⟩ := h1
  exact ⟨os, by simpa [runObs2, hg] using h2, (Res.ok.inj h3).symm⟩

/-- `.ok` form of `run2_eq_runObs2` (no qualified `case`). -/
theorem run2_ok_iff {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {stim tr : List SvState}
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false) :
    run2 d σ fuel stim = .ok tr ↔
      ∃ os, runObs2 d σ fuel stim = .ok os ∧ tr = os.map CycleObs.post := by
  rw [run2_eq_runObs2 d σ fuel stim hnq, Res.bind_eq_ok]
  constructor
  · rintro ⟨os, h1, h2⟩
    exact ⟨os, h1, (Res.ok.inj h2).symm⟩
  · rintro ⟨os, h1, rfl⟩
    exact ⟨os, h1, rfl⟩

/-- A successful `runObs2` has one cycle observation per stimulus entry. -/
theorem runObs2_length {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {stim : List SvState}
    {os : List (CycleObs SvState)} (h : runObs2 d σ fuel stim = .ok os) :
    os.length = stim.length := by
  have hg : run2ClockGuard d = .ok () := by
    cases hq : run2ClockGuard d with
    | ok u => simpa using hq
    | timeout => simp [runObs2, hq] at h
    | unsupported msg => simp [runObs2, hq] at h
  have h2 : runFrom2 d σ fuel (initState2 d) 0 stim = .ok (os.map CycleObs.post) := by
    rw [runFrom2_eq_runFromObs2, show runFromObs2 d σ fuel (initState2 d) 0 stim = .ok os by simpa [runObs2, hg] using h]
    rfl
  simpa using runFrom2_length h2

/-- **Snapshot decomposition with the pre sample**: cycle `c` of a successful `runObs2` is a
successful `cycleObs2` from the previous post sample (or `initState2 d` at cycle 0), at stimulus
entry `c`. The cycle-level facts (`pre_sample_spec`) then apply to every cycle of a run. -/
theorem runFromObs2_cycle {d : Design2} {σ : ScheduleOracle} {fuel : Nat} :
    ∀ {stim : List SvState} {st : SvState} {k : Nat} {os : List (CycleObs SvState)},
      runFromObs2 d σ fuel st k stim = .ok os →
      ∀ {c : Nat} {o : CycleObs SvState}, os[c]? = some o →
        ∃ inputs prev kc kc', stim[c]? = some inputs ∧
          (st :: os.map CycleObs.post)[c]? = some prev ∧
          cycleObs2 d σ fuel inputs prev kc = .ok (o, kc')
  | [], st, k, os, h, c, o, hc => by
      simp only [runFromObs2, Res.ok.injEq] at h
      subst h; simp at hc
  | inputs :: rest, st, k, os, h, c, o, hc => by
      simp only [runFromObs2, Res.bind_eq_ok] at h
      obtain ⟨⟨o0, k'⟩, h1, os', h2, h3⟩ := h
      simp only [Res.pure_eq, Res.ok.injEq] at h3
      subst h3
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc
          exact ⟨inputs, st, k, k', rfl, rfl, h1⟩
      | succ c =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨inp, prev, kc, kc', hi, hp, hs⟩ := runFromObs2_cycle h2 hc
          exact ⟨inp, prev, kc, kc', by simpa using hi, by simpa using hp, hs⟩

/-! ### The `run2` observation model -/

/-- The input ports of a `Design2` (svGolf's `inputPorts`, the same definition). -/
def inputSigs (d : Design2) : List Sig :=
  d.decls.toList.filterMap fun dc => if dc.isInput then some (dc.name, dc.width) else none

/-- The output ports of a `Design2` (svGolf's `outputPorts`, the same definition). -/
def outputSigs (d : Design2) : List Sig :=
  d.decls.toList.filterMap fun dc => if dc.isOutput then some (dc.name, dc.width) else none

/-- `run2`'s own input convention (a backend detail, used only by the `_stim` variants that restate
v1 verbatim): the value stimulus entry `c` binds on input `n`, if it binds one. `applyInputs2` reads
the entry with `SvState.lookup`; an unbound input holds its previous value, which this reports as
`none`. -/
def stimDrive (stim : List SvState) (c : Nat) (n : String) : Option LVec :=
  (stim[c]?).bind fun e => SvState.lookup e n

/-- **`Obs_run2`, the `run2` backend** (*provisional over `run2`*). It omits `run2`'s qualified-case
trace check (master `2218821b`), so for a design with a `unique`/`unique0`/`priority` case it is NOT
`run2`: its behaviours include runs whose claim is violated, where `run2` refuses loudly. `hnq` (no
qualified `case`) is exactly the condition under which the two agree. Pre sample: the state the edge
pass starts from (`cyclePre2`); post sample: `run2`'s snapshot (`run2_eq_runObs2`). Proof
observation: the whole `SvState`. Every stimulus is disciplined: an entry is one clock edge by
construction (the harness's `clockExpand`; the design side is the admission predicate `ClockedBy`). Reducible, so that a `Design2` is an `Obs_run2.Design` at every
transparency (rewriting under `Obs_run2.sample d` needs it). -/
@[reducible] def Obs_run2 : ObservationModel where
  Design := Design2
  Choice := ScheduleOracle
  Env := List SvState
  Probe := SvState
  iface d := ⟨inputSigs d, outputSigs d⟩
  Disciplined _ _ := True
  read := SvState.lookup
  Runs d σ stim r := ∃ fuel, runObs2 d σ fuel stim = .ok r

/-- The trusted sample of a `run2` state reads a declared port as `SvState.lookup` does. -/
theorem Obs_run2.read_sample {d : Design2} {st : SvState} {n : String}
    (hn : n ∈ (Obs_run2.iface d).names) :
    (Obs_run2.sample d st).read n = SvState.lookup st n := by
  have h := ObservationModel.read_sample Obs_run2 d st n
  rw [if_pos hn] at h
  exact h

/-! The bridges to `Runs2`. `Obs_run2` omits `run2`'s qualified-case trace check (master
`2218821b`): for a design with a `unique`/`unique0`/`priority` case, `Obs_run2` is NOT `run2` (its
behaviours include runs whose claim is violated, where `run2` refuses loudly). `hnq` (no qualified
`case`) is exactly the condition under which the two agree; `CombDesign.noQualified` gives it for the
comb profile. -/

/-- **The bridge to `Runs2`** (no qualified `case`): a trusted `Obs_run2` behaviour is the port
restriction of a completed `runObs2` run, whose post samples are a completed `run2` trace. -/
theorem Obs_run2.runs2_of_runs {d : Design2} {σ : ScheduleOracle} {stim : List SvState}
    {r : List (CycleObs SvState)}
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (h : Obs_run2.Runs d σ stim r) :
    Runs2 d σ stim (r.map CycleObs.post) := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, (run2_ok_iff hnq).mpr ⟨r, h, rfl⟩⟩

/-- The other direction: every completed `run2` trace is the post samples of an `Obs_run2` run. -/
theorem Obs_run2.runs_of_runs2 {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) :
    ∃ r, Obs_run2.Runs d σ stim r ∧ tr = r.map CycleObs.post := by
  obtain ⟨fuel, h⟩ := h
  obtain ⟨os, h1, rfl⟩ := runObs2_of_run2_ok h
  exact ⟨os, ⟨fuel, h1⟩, rfl⟩

/-- `Terminates2` gives `Progress` over `Obs_run2`, whatever the clocking (every design). -/
theorem Obs_run2.progress_of_terminates (k : Clocking) (d : Design2) (h : Terminates2 d) :
    Obs_run2.Progress k d := by
  intro σ stim _
  obtain ⟨tr, htr⟩ := h σ stim
  obtain ⟨r, hr, -⟩ := Obs_run2.runs_of_runs2 htr
  exact ⟨_, r, hr, rfl⟩

/-- **Non-vacuity agrees** (no qualified `case`): `Progress` over `Obs_run2` is exactly
`Terminates2`, whatever the clocking. -/
theorem Obs_run2.progress_iff (k : Clocking) (d : Design2)
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false) :
    Obs_run2.Progress k d ↔ Terminates2 d := by
  constructor
  · intro h σ stim
    obtain ⟨b, r, hr, -⟩ := h σ stim trivial
    exact ⟨_, Obs_run2.runs2_of_runs hnq hr⟩
  · exact Obs_run2.progress_of_terminates k d

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
def Obs_E (E : ESig) : ObservationModel where
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

/-- **R-DESIGN2, stated** (signature only; ARCH-NOTE §4.3): on admitted designs, the `run2` backend
and E have the same trusted behaviours, each included in the other, with `toE` the elaboration of a
`Design2` into E, for every clocking. With the first half, every safety statement proved over E
holds over `run2`; with the second, every one proved over `run2` holds over E (`Safe.of_included`).
JUDGED: the second half is where the discipline is used (a disciplined event-level environment is
sampled into one stimulus entry per edge, its held input values). -/
def RDesign2 (E : ESig) (Admitted : Design2 → Prop) (toE : Design2 → E.Elab) : Prop :=
  ∀ k d, Admitted d →
    Included Obs_run2 (Obs_E E) k d (toE d) ∧ Included (Obs_E E) Obs_run2 k (toE d) d

/-- **R-DESIGN2 on typed stimuli** (signature only). Agent A proved the `run2` → E half of `RDesign2`
false for every assign-only design with an input (`not_included_run2_E0`, branch `arch-x1`): `run2`
stores an ill-typed stimulus value as given, while E converts it to the port's width. So that half
is stated on the stimuli `Typed d` admits (`IncludedOn`); the E → `run2` half stays unrestricted. -/
def RDesign2On (E : ESig) (Admitted : Design2 → Prop) (toE : Design2 → E.Elab)
    (Typed : Design2 → List SvState → Prop) : Prop :=
  ∀ k d, Admitted d →
    IncludedOn Obs_run2 (Obs_E E) k d (toE d) (Typed d) ∧ Included (Obs_E E) Obs_run2 k (toE d) d

/-! ## Axiom pins -/

#print axioms cycleStep2_eq_pre_post
#print axioms resetPhase2_of_nil
#print axioms resetPhase2_of_ne_nil
#print axioms combSettle2_settled
#print axioms cycleStep2_eq_cycleObs2
#print axioms pre_sample_spec
#print axioms runFrom2_eq_runFromObs2
#print axioms run2_eq_runObs2
#print axioms runObs2_of_run2_ok
#print axioms run2_ok_iff
#print axioms runObs2_length
#print axioms runFromObs2_cycle
#print axioms ObservationModel.read_sample
#print axioms Safe.of_included
#print axioms Obs_run2.read_sample
#print axioms Obs_run2.runs2_of_runs
#print axioms Obs_run2.runs_of_runs2
#print axioms Obs_run2.progress_of_terminates
#print axioms Obs_run2.progress_iff
#print axioms included_iff_includedOn
#print axioms IncludedOn.of_included
#print axioms IncludedOn.mono
#print axioms ObservationModel.safeOn_true_iff
#print axioms SafeOn.of_includedOn

end LeanModels.Sv.Observe
