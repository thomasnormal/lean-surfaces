import LeanModels.Sv.Sem2
import LeanModels.Sv.Obs

/-!
# The Design2 spec judgment (`LeanModels.Sv` — `⊨₂`)

The semantic tier (`Sem2.lean`) has an interpreter, `run2`, but until this
file no judgment a theorem could state about it. This is the Design2 twin of
M0's `Surface.lean` judgment layer, and it obeys the same laws:

* **Fuel never reaches a statement.** `Runs2 d σ stim tr` (`∃ fuel, run2 …
  = .ok tr`) is the one fuel boundary. Every public judgment — `Models2`
  (`d ⊨₂ P`), `spec2`, `Terminates2` — is built on it, so a spec mentions
  neither fuel nor the AST. Fuel appears in this file only inside
  `Runs2`'s definition, in the STRUCTURAL lemmas that open a run
  (`runFrom2_*`, `Runs2.snapshot`, `Runs2.snapshot_step` — existentially) or
  build one (`Runs2.intro`, `runFrom2_ok_of_invariant`,
  `run2_ok_of_invariant`, `Runs2.of_invariant`, `Terminates2.of_invariant` —
  as the invariant's step fuel), and in the bridges between a concrete
  interpreter run and the judgments: `Models2.of_run` (introduction from a
  fact about every fuel), `Models2.run` (elimination against one fuel), and
  the step hypothesis of `Runs2.forall_of_step` / `forall_mem_of_step` (a
  property preserved by every `.ok` `cycleStep2`, at any fuel).
* **`⊨₂` is all-schedule, all-stimulus, completed-run.** `d ⊨₂ P` says: for
  every legal schedule σ, every stimulus, and every trace that SOME fuel
  completes, `P d stim tr`. It does not say a run completes — a design that
  never settles satisfies every `⊨₂` vacuously. `Terminates2 d` is the
  non-vacuity half, and a `⊨₂` theorem is only meaningful beside it
  (`Models2.exists_of_terminates` packages the pair: a trace exists AND it
  satisfies `P`).
* **No fuel monotonicity in this file.** It neither needs nor imports it:
  `Models2` quantifies over every completing fuel, and the snapshot
  decomposition reads one run. That `Runs2` is functional across fuels (one
  trace per schedule and stimulus) is `Runs2.functional` in `Mono2.lean`,
  which also proves `run2_det` and `Terminates2.existsUnique`.
* **`P` sees the design** (`TraceProp2 = Design2 → stim → trace → Prop`), so
  property builders may mention `initState2 d`; design-agnostic properties
  are lifted with `spec2`.

## Stimulus conventions

A stimulus is a list of `SvState`s, one entry per cycle, and `cycleStep2`
applies entry `c` with `applyInputs2` before cycle `c` settles. A `⊨₂`
statement over stimuli should be written with these rules in mind, because
`applyInputs2` never fails:

* **Entries are applied verbatim.** The value bound to an input is stored
  as given, AT ITS OWN WIDTH; it is not resized to the port's declared width
  (SV port assignment would zero-extend). On the 4-bit `ripple_add` with
  `b = 0001` and `cin = 0`, the entry `a := LVec.ofNat 2 3` makes `a` the
  2-bit `11`, so the out-of-range reads `a[2]`, `a[3]` are `x` and `s`
  comes out `xx00`, where SV would give `0100` (pinned, with the two
  ignored-key cases below, by `#guard` rows in
  `Examples/system-verilog/ripple_add/spec.lean`).
  The one exception is a 2-STATE input declaration (`Decl.twoState`, the
  symbolic `bit`/`bit [W-1:0]` ports): `applyInputs2` maps its x/z bits to 0
  at the boundary (§6.3.1). The comb proof layer (`CombDesign.inFourState`)
  covers 4-state input ports only, where "verbatim" is exact.
* **Only declared inputs are read.** `applyInputs2` walks the input
  declarations (`d.inputNames`); a key that names no input — a misspelling such as `"A"`,
  or an output or internal net such as `"s"` — is silently ignored. If an
  entry binds a name twice, the first binding wins (`SvState.lookup`).
* **Unbound inputs hold.** An input the entry does not bind keeps its value
  from the previous snapshot; before any entry binds it, that is its
  `initState2` value (its initializer, else all-`x`).

A statement whose stimulus hypothesis is built at the wrong width or under a
misspelled name therefore does not say what it appears to: depending on its
form it holds vacuously (no run meets the hypothesis) or is false (the design
sees `x` or a narrower port). Challenge statements should quantify over
known values at the DECLARED width —
`SvState.lookup inputs "a" = some (LVec.ofBitVec x)` with
`x : BitVec <declared width>` (the shape of `ripple_correct_stim` in
`Examples/system-verilog/ripple_add/spec.lean`) — so that the hypothesis
fixes the width and names the port.

What the later proof layers consume:

* `Runs2.snapshot` / `Runs2.snapshot_step` — every snapshot is an `.ok`
  `cycleStep2` from the previous snapshot (or `initState2 d` at cycle 0),
  at the cycle's stimulus entry. The combinational settle theorem
  (`Comb2.lean`) lifts its per-settle equations to every snapshot through
  this, by induction on the cycle index (`snapshot_step` hands the previous
  snapshot back as a `tr[c]? = some prev` fact, the shape that induction
  needs).
* `run2_ok_of_invariant` / `Terminates2.of_invariant` — the introduction
  side: an invariant that holds initially and that every `cycleStep2` (at
  one fuel `F`, any inputs, any schedule counter) succeeds from and
  preserves yields a completed run, hence `Terminates2`.

The `#guard`/`example` section at the end runs a hand-built one-gate design
through `run2` and exercises both directions of `⊨₂` on it, and proves
`Terminates2` of a process-free design through the invariant helper.

This file imports `Obs.lean` (besides `Sem2.lean`) only for the `Res`
do-notation simp set (`Res.bind_eq_ok`, `Res.ok_bind`, …), the
`LawfulBEq LVec` instance, and `ScheduleOracle.choose_nil` (used by the
`Terminates2` example); it re-declares none of them, so it composes with
any file that imports both.

**Naming trap for later `Models2.*` declarations.** Lean opens the
`Models2` namespace while elaborating a declaration named `Models2.foo`, so
inside it `Models2.and` (the `⊨₂` conjunction rule) hides the root `and`
(Bool).
In `Models2.*` declarations, write `&&` / `Bool.and` and `Bool.true`
explicitly. No other declaration here shadows a root name. The trivial-spec
lemma is called `Models2.spec2_true`, not `Models2.true` or
`Models2.trivial`, because those names would hide `true` and `trivial`.
-/

namespace LeanModels.Sv

/-! ## The judgments -/

/-- A cycle-level trace property of a semantic-tier design: sees the design
(so property builders can mention `initState2 d`), the stimulus, and the
trace (one snapshot per stimulus entry). Design-agnostic properties are
lifted with `spec2`. -/
abbrev TraceProp2 := Design2 → List SvState → List SvState → Prop

/-- The fuel-abstracted Design2 run judgment: *some* fuel completes the run
of `d` under schedule `σ` and stimulus `stim` with trace `tr`. The only place
fuel appears in a Design2 spec. -/
def Runs2 (d : Design2) (σ : ScheduleOracle) (stim tr : List SvState) : Prop :=
  ∃ fuel, run2 d σ fuel stim = .ok tr

/-- `d ⊨₂ P` — for **every** legal schedule, every stimulus, and every
completed run (`Runs2`), the trace satisfies `P`. Introduce from a raw
∀-fuel fact with `Models2.of_run`; eliminate against a concrete run with
`Models2.run` / `Models2.runs`. Says nothing about whether runs complete —
pair it with `Terminates2`. -/
def Models2 (d : Design2) (P : TraceProp2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim tr : List SvState), Runs2 d σ stim tr → P d stim tr

@[inherit_doc] scoped infix:50 " ⊨₂ " => Models2

/-- Lift a design-agnostic stimulus/trace predicate into `⊨₂`
(`d ⊨₂ spec2 fun stim tr => …`). -/
def spec2 (P : List SvState → List SvState → Prop) : TraceProp2 := fun _ stim tr => P stim tr

/-- Non-vacuity: every schedule and every stimulus completes. A `⊨₂` theorem
is only meaningful together with this (a design that never settles satisfies
every `⊨₂`). -/
def Terminates2 (d : Design2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim : List SvState), ∃ tr, Runs2 d σ stim tr

/-! ## `Runs2` basics -/

/-- Introduce `Runs2` from one concrete completing fuel. -/
theorem Runs2.intro {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (fuel : Nat) (h : run2 d σ fuel stim = .ok tr) : Runs2 d σ stim tr :=
  ⟨fuel, h⟩

/-! ### Structural `runFrom2` lemmas (fuel-explicit; the `Runs2` lemmas below
hide the fuel again) -/

/-- The empty stimulus completes immediately with the empty trace (any fuel). -/
@[simp] theorem runFrom2_nil (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (st : SvState) (k : Nat) : runFrom2 d σ fuel st k [] = .ok [] := by
  simp [runFrom2]

/-- One cycle of `runFrom2`, inverted: a completed run of `inputs :: rest`
is an `.ok` `cycleStep2` followed by a completed run of `rest` from its
result. -/
theorem runFrom2_cons_eq_ok {d : Design2} {σ : ScheduleOracle} {fuel : Nat}
    {st : SvState} {k : Nat} {inputs : SvState} {rest tr : List SvState} :
    runFrom2 d σ fuel st k (inputs :: rest) = .ok tr ↔
      ∃ st' k' tr', cycleStep2 d σ fuel inputs st k = .ok (st', k') ∧
        runFrom2 d σ fuel st' k' rest = .ok tr' ∧ tr = st' :: tr' := by
  simp only [runFrom2, Res.bind_eq_ok]
  constructor
  · rintro ⟨⟨st', k'⟩, h1, tr', h2, h3⟩
    exact ⟨st', k', tr', h1, h2, by simpa [eq_comm] using h3⟩
  · rintro ⟨st', k', tr', h1, h2, rfl⟩
    exact ⟨(st', k'), h1, tr', h2, rfl⟩

/-- A completed `runFrom2` emits one snapshot per stimulus entry. -/
theorem runFrom2_length {d : Design2} {σ : ScheduleOracle} {fuel : Nat} :
    ∀ {stim : List SvState} {st : SvState} {k : Nat} {tr : List SvState},
      runFrom2 d σ fuel st k stim = .ok tr → tr.length = stim.length
  | [], st, k, tr, h => by
      simp only [runFrom2_nil, Res.ok.injEq] at h
      subst h; rfl
  | inputs :: rest, st, k, tr, h => by
      obtain ⟨st', k', tr', _, h2, rfl⟩ := runFrom2_cons_eq_ok.mp h
      simp [runFrom2_length h2]

/-- Snapshot decomposition of a completed `runFrom2`: snapshot `c` is an
`.ok` `cycleStep2` (at the run's fuel) from the previous snapshot — or the
start state `st` at `c = 0` — at stimulus entry `c`. -/
theorem runFrom2_snapshot {d : Design2} {σ : ScheduleOracle} {fuel : Nat} :
    ∀ {stim : List SvState} {st : SvState} {k : Nat} {tr : List SvState},
      runFrom2 d σ fuel st k stim = .ok tr →
      ∀ {c : Nat} {s : SvState}, tr[c]? = some s →
        ∃ inputs prev kc kc', stim[c]? = some inputs ∧ (st :: tr)[c]? = some prev ∧
          cycleStep2 d σ fuel inputs prev kc = .ok (s, kc')
  | [], st, k, tr, h, c, s, hc => by
      simp only [runFrom2_nil, Res.ok.injEq] at h
      subst h; simp at hc
  | inputs :: rest, st, k, tr, h, c, s, hc => by
      obtain ⟨st', k', tr', h1, h2, rfl⟩ := runFrom2_cons_eq_ok.mp h
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc
          exact ⟨inputs, st, k, k', rfl, rfl, h1⟩
      | succ c =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨inp, prev, kc, kc', hi, hp, hs⟩ := runFrom2_snapshot h2 hc
          exact ⟨inp, prev, kc, kc', by simpa using hi, by simpa using hp, hs⟩

/-! ### The `Runs2` structure lemmas -/

/-- A completed run has exactly one snapshot per stimulus entry. -/
theorem Runs2.length {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) : tr.length = stim.length := by
  obtain ⟨fuel, hrun⟩ := h
  exact runFrom2_length hrun

/-- Every stimulus cycle of a completed run has a snapshot. -/
theorem Runs2.exists_snapshot {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) {c : Nat} (hc : c < stim.length) : ∃ st, tr[c]? = some st :=
  ⟨tr[c]'(h.length ▸ hc), List.getElem?_eq_getElem _⟩

/-- The empty stimulus completes with the empty trace, and only with it. -/
theorem Runs2.nil_iff {d : Design2} {σ : ScheduleOracle} {tr : List SvState} :
    Runs2 d σ [] tr ↔ tr = [] := by
  constructor
  · intro h; simpa using h.length
  · rintro rfl; exact ⟨0, by simp [run2]⟩

/-- **Snapshot decomposition, step form**: snapshot `c` of a completed run
is an `.ok` `cycleStep2` from the previous snapshot — read off the shifted
trace `initState2 d :: tr`, so cycle 0 starts from `initState2 d` and cycle
`c + 1` from `tr[c]` — at the stimulus entry of cycle `c`. Fuel and the
schedule counters stay existential. This is the induction-friendly form:
at `c + 1` the previous snapshot comes back as `tr[c]? = some prev`. -/
theorem Runs2.snapshot_step {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) {c : Nat} {st : SvState} (hc : tr[c]? = some st) :
    ∃ fuel inputs prev k k', stim[c]? = some inputs ∧
      (initState2 d :: tr)[c]? = some prev ∧
      cycleStep2 d σ fuel inputs prev k = .ok (st, k') := by
  obtain ⟨fuel, hrun⟩ := h
  obtain ⟨inputs, prev, k, k', hi, hp, hs⟩ := runFrom2_snapshot hrun hc
  exact ⟨fuel, inputs, prev, k, k', hi, hp, hs⟩

/-- **Snapshot decomposition** (the closed form): every snapshot is a
successful `cycleStep2` from the previous snapshot (or `initState2 d` at
cycle 0), at the cycle's stimulus entry. `Runs2.snapshot_step` is the same
fact with the previous snapshot as a `getElem?` equation. -/
theorem Runs2.snapshot {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) {c : Nat} {st : SvState} (hc : tr[c]? = some st) :
    ∃ fuel inputs prev k k', stim[c]? = some inputs ∧
      (prev = if c = 0 then initState2 d else (tr[c-1]?.getD [])) ∧
      cycleStep2 d σ fuel inputs prev k = .ok (st, k') := by
  obtain ⟨fuel, inputs, prev, k, k', hi, hp, hs⟩ := h.snapshot_step hc
  refine ⟨fuel, inputs, prev, k, k', hi, ?_, hs⟩
  cases c with
  | zero => simpa [eq_comm] using hp
  | succ c => simp only [List.getElem?_cons_succ] at hp; simp [hp]

/-! ## Building runs from a cycle invariant -/

/-- **Run construction**: if, at fuel `F`, every `cycleStep2` from a state
satisfying `I` (any inputs, any schedule counter) succeeds and lands in `I`,
then `runFrom2` from any `I`-state completes on every stimulus, and every
snapshot satisfies `I`. -/
theorem runFrom2_ok_of_invariant {d : Design2} {σ : ScheduleOracle} {F : Nat}
    (I : SvState → Prop)
    (hstep : ∀ (inputs st : SvState) (k : Nat), I st →
      ∃ st' k', cycleStep2 d σ F inputs st k = .ok (st', k') ∧ I st') :
    ∀ (stim : List SvState) (st : SvState) (k : Nat), I st →
      ∃ tr, runFrom2 d σ F st k stim = .ok tr ∧ ∀ s ∈ tr, I s
  | [], st, k, _ => ⟨[], by simp⟩
  | inputs :: rest, st, k, hI => by
      obtain ⟨st', k', h1, hI'⟩ := hstep inputs st k hI
      obtain ⟨tr', h2, hall⟩ := runFrom2_ok_of_invariant I hstep rest st' k' hI'
      refine ⟨st' :: tr', runFrom2_cons_eq_ok.mpr ⟨st', k', tr', h1, h2, rfl⟩, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hI'
      · exact hall s hs

/-- `run2` form of `runFrom2_ok_of_invariant`: an invariant that holds at
`initState2 d` and that every `cycleStep2` at fuel `F` succeeds from and
preserves makes `run2 d σ F` complete on every stimulus. -/
theorem run2_ok_of_invariant {d : Design2} {σ : ScheduleOracle} {F : Nat}
    (I : SvState → Prop) (hinit : I (initState2 d))
    (hstep : ∀ (inputs st : SvState) (k : Nat), I st →
      ∃ st' k', cycleStep2 d σ F inputs st k = .ok (st', k') ∧ I st')
    (stim : List SvState) :
    ∃ tr, run2 d σ F stim = .ok tr ∧ ∀ s ∈ tr, I s :=
  runFrom2_ok_of_invariant I hstep stim (initState2 d) 0 hinit

/-- `Runs2` form of `run2_ok_of_invariant` (fuel hidden again). -/
theorem Runs2.of_invariant {d : Design2} {σ : ScheduleOracle} {F : Nat}
    (I : SvState → Prop) (hinit : I (initState2 d))
    (hstep : ∀ (inputs st : SvState) (k : Nat), I st →
      ∃ st' k', cycleStep2 d σ F inputs st k = .ok (st', k') ∧ I st')
    (stim : List SvState) :
    ∃ tr, Runs2 d σ stim tr ∧ ∀ s ∈ tr, I s := by
  obtain ⟨tr, h, hall⟩ := run2_ok_of_invariant I hinit hstep stim
  exact ⟨tr, ⟨F, h⟩, hall⟩

/-- **Snapshot invariant (elimination side)**: if `I` holds at `initState2 d`
and every `.ok` `cycleStep2` (any fuel, inputs, schedule counter) from an
`I`-state lands in `I`, then every snapshot of a completed run satisfies `I`.
This packages the cycle induction over `Runs2.snapshot_step`, so consumers
do not have to repeat it. -/
theorem Runs2.forall_of_step {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    {I : SvState → Prop} (hinit : I (initState2 d))
    (hstep : ∀ (fuel : Nat) (inputs prev : SvState) (k : Nat) (st : SvState) (k' : Nat),
      I prev → cycleStep2 d σ fuel inputs prev k = .ok (st, k') → I st)
    (h : Runs2 d σ stim tr) : ∀ (c : Nat) (st : SvState), tr[c]? = some st → I st := by
  intro c
  induction c with
  | zero =>
      intro st hc
      obtain ⟨fuel, inputs, prev, k, k', _, hp, hs⟩ := h.snapshot_step hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact hstep fuel inputs _ k st k' hinit hs
  | succ c ih =>
      intro st hc
      obtain ⟨fuel, inputs, prev, k, k', _, hp, hs⟩ := h.snapshot_step hc
      simp only [List.getElem?_cons_succ] at hp
      exact hstep fuel inputs prev k st k' (ih prev hp) hs

/-- Membership form of `Runs2.forall_of_step`: every state in the trace of a
completed run satisfies the step invariant. -/
theorem Runs2.forall_mem_of_step {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    {I : SvState → Prop} (hinit : I (initState2 d))
    (hstep : ∀ (fuel : Nat) (inputs prev : SvState) (k : Nat) (st : SvState) (k' : Nat),
      I prev → cycleStep2 d σ fuel inputs prev k = .ok (st, k') → I st)
    (h : Runs2 d σ stim tr) : ∀ st ∈ tr, I st := by
  intro st hst
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hst
  exact h.forall_of_step hinit hstep c _ (List.getElem?_eq_getElem hc)

/-- **`Terminates2` from a cycle invariant**: if `I (initState2 d)` and, for
each schedule, some fuel makes every `cycleStep2` from an `I`-state succeed
into `I`, the design terminates on every schedule and stimulus. -/
theorem Terminates2.of_invariant {d : Design2} (I : SvState → Prop)
    (hinit : I (initState2 d))
    (hstep : ∀ σ : ScheduleOracle, ∃ F, ∀ (inputs st : SvState) (k : Nat), I st →
      ∃ st' k', cycleStep2 d σ F inputs st k = .ok (st', k') ∧ I st') :
    Terminates2 d := by
  intro σ stim
  obtain ⟨F, hF⟩ := hstep σ
  obtain ⟨tr, h, _⟩ := Runs2.of_invariant (F := F) I hinit hF stim
  exact ⟨tr, h⟩

/-! ## `⊨₂` introduction and elimination -/

/-- Introduction rule — the raw hypothesis-form shape
(`run2 d σ fuel stim = .ok tr → …`, for every fuel), lifted in one step. -/
theorem Models2.of_run {d : Design2} {P : TraceProp2}
    (h : ∀ (σ : ScheduleOracle) (fuel : Nat) (stim tr : List SvState),
      run2 d σ fuel stim = .ok tr → P d stim tr) : d ⊨₂ P :=
  fun σ stim tr hr => hr.elim fun fuel hrun => h σ fuel stim tr hrun

/-- Introduction from the fuel-free run judgment (definitional; for
readability at use sites). -/
theorem Models2.of_runs {d : Design2} {P : TraceProp2}
    (h : ∀ (σ : ScheduleOracle) (stim tr : List SvState), Runs2 d σ stim tr → P d stim tr) :
    d ⊨₂ P :=
  h

/-- Elimination against a concrete interpreter run (any fuel). -/
theorem Models2.run {d : Design2} {P : TraceProp2} (h : d ⊨₂ P)
    {σ : ScheduleOracle} {fuel : Nat} {stim tr : List SvState}
    (hrun : run2 d σ fuel stim = .ok tr) : P d stim tr :=
  h σ stim tr ⟨fuel, hrun⟩

/-- Elimination against the fuel-free run judgment. -/
theorem Models2.runs {d : Design2} {P : TraceProp2} (h : d ⊨₂ P)
    {σ : ScheduleOracle} {stim tr : List SvState} (hr : Runs2 d σ stim tr) : P d stim tr :=
  h σ stim tr hr

/-- Monotonicity: weaken the property pointwise. -/
theorem Models2.imp {d : Design2} {P Q : TraceProp2}
    (hPQ : ∀ stim tr, P d stim tr → Q d stim tr) (h : d ⊨₂ P) : d ⊨₂ Q :=
  fun σ stim tr hr => hPQ stim tr (h σ stim tr hr)

/-- Conjunction: two `⊨₂` facts about one design combine pointwise.
(Its name hides the root `and` inside later `Models2.*` declarations. There,
write `&&` / `Bool.and`; see the module docstring.) -/
theorem Models2.and {d : Design2} {P Q : TraceProp2} (hP : d ⊨₂ P) (hQ : d ⊨₂ Q) :
    d ⊨₂ fun d stim tr => P d stim tr ∧ Q d stim tr :=
  fun σ stim tr hr => ⟨hP σ stim tr hr, hQ σ stim tr hr⟩

/-- `Models2.and` for `spec2`-lifted properties (stays in `spec2` form). -/
theorem Models2.and_spec2 {d : Design2} {P Q : List SvState → List SvState → Prop}
    (hP : d ⊨₂ spec2 P) (hQ : d ⊨₂ spec2 Q) :
    d ⊨₂ spec2 fun stim tr => P stim tr ∧ Q stim tr :=
  Models2.and hP hQ

/-- Every design satisfies the trivially true property. (Not named
`Models2.true`/`Models2.trivial`: those would hide the root `true`/`trivial`
inside every later `Models2.*` declaration.) -/
theorem Models2.spec2_true (d : Design2) : d ⊨₂ spec2 fun _ _ => True :=
  fun _ _ _ _ => trivial

/-- Every design satisfies the length law: one snapshot per stimulus entry. -/
theorem Models2.length (d : Design2) : d ⊨₂ spec2 fun stim tr => tr.length = stim.length :=
  fun _ _ _ hr => hr.length

/-- **Non-vacuity, packaged**: with `Terminates2`, a `⊨₂` property is
witnessed by an actual completed run on every schedule and stimulus. -/
theorem Models2.exists_of_terminates {d : Design2} {P : TraceProp2}
    (ht : Terminates2 d) (h : d ⊨₂ P) (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 d σ stim tr ∧ P d stim tr := by
  obtain ⟨tr, hr⟩ := ht σ stim
  exact ⟨tr, hr, h.runs hr⟩

/-! ## Examples: a one-gate design

`y = a & b` over 1-bit inputs. The `#guard` rows pin concrete `run2`
traces (the `x` startup values of undriven inputs flow through the gate,
held inputs keep their last driven value); the `example`s use the judgment
layer on it. -/

/-- `assign y = a & b;` with 1-bit ports. -/
private def and1D : Design2 :=
  { name := "and1"
    decls := #[
      { name := "a", width := 1, isInput := true },
      { name := "b", width := 1, isInput := true },
      { name := "y", width := 1, isOutput := true }]
    processes := #[.assign (.ident "y") (.binary .and (.ident "a") (.ident "b"))] }

private def and1Stim : List SvState := [
  [("a", LVec.lit "1"), ("b", LVec.lit "1")],
  [("b", LVec.lit "0")],
  [("b", LVec.lit "1")],
  [("a", LVec.lit "0")],
  []]

#guard (Res.toOption (run2 and1D σ_src 64 and1Stim)).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["1", "0", "1", "0", "0"]

-- Same rows under the reversed schedule (one comb process: σ is irrelevant).
#guard (Res.toOption (run2 and1D σ_rev 64 and1Stim)).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["1", "0", "1", "0", "0"]

-- An undriven input reads x at startup; `0 & x = 0`, `1 & x = x`.
#guard (Res.toOption (run2 and1D σ_src 64 [[("a", LVec.lit "0")], [("a", LVec.lit "1")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["0", "x"]

-- `⊨₂` from `Runs2.length`: the trace has one snapshot per stimulus entry.
example : and1D ⊨₂ spec2 fun stim tr => tr.length = stim.length :=
  Models2.of_run fun _ _ _ _ hrun => Runs2.length ⟨_, hrun⟩

-- A concrete completed run as a fuel-free `Runs2` fact (kernel-checked).
example : Runs2 and1D σ_src [[("a", LVec.lit "1"), ("b", LVec.lit "1")]]
    [[("a", LVec.lit "1"), ("b", LVec.lit "1"), ("y", LVec.lit "1")]] :=
  ⟨8, by decide +kernel⟩

-- Elimination: ANY `⊨₂` property of `and1D` holds of that concrete run.
example (P : TraceProp2) (h : and1D ⊨₂ P) :
    P and1D [[("a", LVec.lit "1"), ("b", LVec.lit "1")]]
      [[("a", LVec.lit "1"), ("b", LVec.lit "1"), ("y", LVec.lit "1")]] :=
  h.runs (σ := σ_src) ⟨8, by decide +kernel⟩

-- The snapshot-invariant eliminator, at its smallest instance (`I := True`):
-- the shape `Comb2.lean` instantiates with `StateShape` (`Runs2.comb_shape`).
example (σ : ScheduleOracle) (stim tr : List SvState) (h : Runs2 and1D σ stim tr) :
    ∀ st ∈ tr, True :=
  h.forall_mem_of_step (I := fun _ => True) trivial (fun _ _ _ _ _ _ _ _ => trivial)

-- Conjunction of two generic facts, staying in `spec2` form.
example : and1D ⊨₂ spec2 fun stim tr => tr.length = stim.length ∧ True :=
  Models2.and_spec2 (Models2.length _) (Models2.spec2_true _)

-- `Terminates2` through the invariant helper, on a process-free design (the
-- trivial invariant `True`; every settle is one no-op pass whose `==`
-- fixpoint check closes by `LawfulBEq`).
private def holdD : Design2 :=
  { name := "hold"
    decls := #[{ name := "a", width := 4, isInput := true }]
    processes := #[] }

private theorem holdD_terminates : Terminates2 holdD :=
  Terminates2.of_invariant (fun _ => True) trivial fun σ =>
    ⟨1, fun inputs st k _ => ⟨applyInputs2 holdD inputs st, k + 3, by
      simp [cycleStep2, combSettle2, combPass2, Design2.combIndices, Design2.resetIndices,
        Design2.edgeIndices, holdD, σ.choose_nil, edgePass2, commitNba2], trivial⟩⟩

-- Non-vacuity, packaged: with `Terminates2`, a `⊨₂` fact is witnessed by an
-- actual run on every schedule and stimulus.
example (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 holdD σ stim tr ∧ tr.length = stim.length :=
  Models2.exists_of_terminates holdD_terminates (Models2.length holdD) σ stim

end LeanModels.Sv
