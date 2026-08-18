import LeanModels.Python.VC2

/-!
# The generator tier (`py_vcgen` layer 2G)

Landing **L2** of [docs/generator-tier-architecture.md](../../docs/generator-tier-architecture.md).
Layers 1 and 2 (VC.lean, VC2.lean) specify STATEMENTS — what a `for`/`while`
body does to a frame state. This file specifies SUSPENDED MACHINES: what a
generator's frame stack (`GenCont`, Runtime.lean) still has to yield.

Before it there were exactly two facts about the generator tier in the repo
(`stepIter_mono`/`execGen_mono` in Obs.lean, plus clock erasure) and no way
to say what a generator *computes*. `Examples/python/gen_lab` carried 73
differential rows and no `proof.lean`.

## The objects

* **`drainGen`/`stepGenN`** — the two spec-side drivers. `drainGen` runs a
  frame stack to exhaustion collecting the yields; `stepGenN` takes exactly
  `n` steps and hands back the machine. Neither is in the interpreter's
  mutual block (nothing in the interpreter calls them), so they cost no
  `fuelMono`/`worldInv`/`clockErase` conjunct — their monotonicity is proved
  here, off `execGen_mono`.

* **`GenYields m st k vs st'`** — from `st` with frame stack `k` the machine
  yields exactly `vs` and then FINISHES, landing in `st'`. The
  fuel-threshold idiom of the rest of the repo (`∃ t, ∀ F ≥ t`), so timeout
  is excluded rather than tolerated.

* **`GenYieldsPrefix m st k vs st' k'`** — the LAZY half: the first `vs`
  values, machine left suspended at `k'`. Two objects rather than one
  deliberately: laziness is semantically load-bearing (an unconsumed yield
  must not run its TT-writing search), so a consumer that ABANDONS the
  generator takes on no total obligation. `itertools.count` has no
  `GenYields` at all — only a prefix.

## The calculus

Composition is list concatenation, and the shape that makes it so is
**`GenEmits`**: `GenEmits m st pre ws st₁` says the frame PREFIX `pre`
emits `ws` and falls through to `st₁` — *for every continuation below it*.
Frame-stack polymorphism is the whole trick: the interpreter only ever
scrutinizes the head frames, so every structural rule is stated over
`pre ++ k` with `k` universally quantified, and `GenEmits.trans` is literal
`List.append` on both the frames and the output.

Two primitives underneath, both in threshold form:

* `GenSteps m st k r st'` — one decided resumption step (`execGen`).
* `GenSilent m st k st₁ k₁` — `⟨st, k⟩` resumes exactly as `⟨st₁, k₁⟩`
  does: the interpreter rearranged the frame stack without yielding. This
  is the arm every non-yielding frame transition takes, and it composes
  transitively because the fuel offset is existentially quantified.

## What is here and what is not

Every frame kind of `GenFrame` has its transition rule, the yield-free
statements delegate to the layer-1/2 statement triples (`genPlan .delegate`
calls `execStmt`, so their semantics keeps exactly one definition), and
`GenEmits.forSeq` is the sequence rule with a remainder-indexed invariant —
`execFor_of_invariant`'s proof with the output list threaded.

DELIBERATELY not here (L3's content, docs/generator-tier-architecture.md §2):
the walker case, `EvalsTo.genCall`, and any `py_vcgen` automation. Also not
here: a LOOP-level invariant rule over the live-cursor frames (`forList`,
`enumList`, `forGen`). Their single-step transitions are below and carry an
explicit heap-read hypothesis at the state the step is taken from; an
invariant rule over them would need a heap-stability side condition that
says the body does not mutate the object under the cursor, and inventing
one before a consumer needs it would be claiming a snapshot semantics the
interpreter does not have (the `IterVals` exclusion note in VC2.lean, one
level up).
-/

namespace LeanModels.Python

open scoped Run

/-- Destructure a nonzero-threshold bound (private twin of VC.lean's and
VC2.lean's helper — both are `private`). -/
private theorem succ_le_dest {t F : Nat} (h : t + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ t ≤ F' := ⟨F - 1, by omega, by omega⟩

/-- A decided outcome is its own upper bound in `⊑ʳ`. -/
private theorem le_of_pin {σ α : Type} {x y : Run σ α}
    (h : x ≠ .timeout → y = x) : x ⊑ʳ y := by
  by_cases hx : x = .timeout
  · exact Or.inl hx
  · exact Or.inr (h hx).symm

/-! ## The spec-side drivers -/

/-- Run a frame stack to EXHAUSTION, collecting the yields in order — the
spec-side twin of `drainIter` (which does the same thing to a heap
generator OBJECT, writing the suspension back each step). One `execGen` per
yield; fuel bounds the drain, so an infinite generator is a loud timeout
and `GenYields` simply has no witness for it.

Outside the interpreter's mutual block on purpose: nothing in the
interpreter calls it, so it adds no `fuelMono`/`worldInv`/`clockErase`
conjunct and unfolds freely. -/
def drainGen (m : Module) (fuel : Nat) (st : FrameState) (k : GenCont) :
    Run FrameState (List RVal) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    execGen m fuel st k ⤳ fun st r =>
      match r with
      | Option.none => .ok st []
      | some (v, k') => drainGen m fuel st k' ⤳ fun st vs => .ok st (v :: vs)
  termination_by structural fuel

/-- Take exactly `n` resumption steps and hand the machine back — the LAZY
driver, for a consumer that stops early (`bound`'s beta cutoff). Running
out of yields before `n` answers the short list with the EXHAUSTED stack
`[]`, which is the same thing the interpreter means by an empty
continuation, so a short answer can never be read as a full one: at
`n = vs.length` the equation in `GenYieldsPrefix` pins the length too. -/
def stepGenN (m : Module) (fuel : Nat) (st : FrameState) (k : GenCont)
    (n : Nat) : Run FrameState (List RVal × GenCont) :=
  match n with
  | 0 => .ok st ([], k)
  | n + 1 =>
    execGen m fuel st k ⤳ fun st r =>
      match r with
      | Option.none => .ok st ([], [])
      | some (v, k') =>
        stepGenN m fuel st k' n ⤳ fun st p => .ok st (v :: p.1, p.2)
  termination_by structural n

/-- `drainGen`'s continuation, named so the fuel-shift lemmas can speak
about it. -/
private def drainCont (m : Module) (F : Nat) (st : FrameState)
    (r : Option (RVal × GenCont)) : Run FrameState (List RVal) :=
  match r with
  | Option.none => .ok st []
  | some (v, k') => drainGen m F st k' ⤳ fun st vs => .ok st (v :: vs)

/-- `stepGenN`'s continuation, likewise. -/
private def stepCont (m : Module) (F n : Nat) (st : FrameState)
    (r : Option (RVal × GenCont)) : Run FrameState (List RVal × GenCont) :=
  match r with
  | Option.none => .ok st ([], [])
  | some (v, k') =>
    stepGenN m F st k' n ⤳ fun st p => .ok st (v :: p.1, p.2)

/-- One-step unfold of the drain (`drainGen` is not a frozen recursion
point — it is outside the mutual block — but naming the step keeps the
proofs below readable). -/
theorem drainGen_succ (m : Module) (F : Nat) (st : FrameState) (k : GenCont) :
    drainGen m (F + 1) st k = execGen m F st k ⤳ drainCont m F := by
  rw [drainGen]
  rfl

theorem drainGen_zero (m : Module) (st : FrameState) (k : GenCont) :
    drainGen m 0 st k = .timeout := by rw [drainGen]

theorem stepGenN_zero (m : Module) (F : Nat) (st : FrameState) (k : GenCont) :
    stepGenN m F st k 0 = .ok st ([], k) := by rw [stepGenN]

theorem stepGenN_succ (m : Module) (F : Nat) (st : FrameState) (k : GenCont)
    (n : Nat) :
    stepGenN m F st k (n + 1) = execGen m F st k ⤳ stepCont m F n := by
  rw [stepGenN]
  rfl

/-- Fuel monotonicity of the drain: a decided drain keeps its exact outcome
at any higher fuel. Ordinary induction on fuel off `execGen_mono` — the
`fuelMono` block never has to hear about `drainGen`. -/
theorem drainGen_le (m : Module) : ∀ (fuel : Nat) (st : FrameState)
    (k : GenCont) (fuel' : Nat), fuel ≤ fuel' →
      drainGen m fuel st k ⊑ʳ drainGen m fuel' st k := by
  intro fuel
  induction fuel with
  | zero => intro st k fuel' _; rw [drainGen_zero]; exact Run.timeout_le _
  | succ f ih =>
    intro st k fuel' hf
    obtain ⟨f', rfl, hf'⟩ := succ_le_dest hf
    rw [drainGen_succ, drainGen_succ]
    refine Run.le_bind (le_of_pin fun hx => execGen_mono rfl hx f' hf') ?_
    intro s r
    match r with
    | Option.none => exact Run.le_refl _
    | some (v, k') =>
      exact Run.le_bind (ih s k' f' hf') fun _ _ => Run.le_refl _

@[inherit_doc drainGen_le]
theorem drainGen_mono {m : Module} {fuel : Nat} {st : FrameState} {k : GenCont}
    {r : Run FrameState (List RVal)} (h : drainGen m fuel st k = r)
    (hr : r ≠ .timeout) (fuel' : Nat) (hf : fuel ≤ fuel') :
    drainGen m fuel' st k = r := by
  subst h
  exact (Run.le_eq (drainGen_le m fuel st k fuel' hf) hr).symm

/-- Fuel monotonicity of the bounded stepper (induction on the STEP count;
the fuel rides along and `execGen_mono` does the work at each step). -/
theorem stepGenN_le (m : Module) : ∀ (n : Nat) (st : FrameState) (k : GenCont)
    (fuel fuel' : Nat), fuel ≤ fuel' →
      stepGenN m fuel st k n ⊑ʳ stepGenN m fuel' st k n := by
  intro n
  induction n with
  | zero => intro st k fuel fuel' _; rw [stepGenN_zero, stepGenN_zero]; exact Run.le_refl _
  | succ n ih =>
    intro st k fuel fuel' hf
    rw [stepGenN_succ, stepGenN_succ]
    refine Run.le_bind (le_of_pin fun hx => execGen_mono rfl hx fuel' hf) ?_
    intro s r
    match r with
    | Option.none => simp only [stepCont]; exact Run.le_refl _
    | some (v, k') =>
      simp only [stepCont]
      exact Run.le_bind (ih s k' fuel fuel' hf) fun _ _ => Run.le_refl _

@[inherit_doc stepGenN_le]
theorem stepGenN_mono {m : Module} {fuel : Nat} {st : FrameState} {k : GenCont}
    {n : Nat} {r : Run FrameState (List RVal × GenCont)}
    (h : stepGenN m fuel st k n = r) (hr : r ≠ .timeout) (fuel' : Nat)
    (hf : fuel ≤ fuel') : stepGenN m fuel' st k n = r := by
  subst h
  exact (Run.le_eq (stepGenN_le m n st k fuel fuel' hf) hr).symm

/-- The drain's continuation is fuel-insensitive once the drain has
DECIDED — the one lemma the fuel-offset bookkeeping of `GenSilent` needs. -/
private theorem drainCont_pin {m : Module} {F F' : Nat} (hF : F ≤ F')
    {x : Run FrameState (Option (RVal × GenCont))} {st' : FrameState}
    {vs : List RVal} (h : x ⤳ drainCont m F = .ok st' vs) :
    x ⤳ drainCont m F' = .ok st' vs := by
  match x with
  | .ok s Option.none => simpa [drainCont] using h
  | .ok s (some (v, k')) =>
    simp only [Run.ok_bind, drainCont] at h ⊢
    match hd : drainGen m F s k' with
    | .ok s₂ ws =>
      rw [drainGen_mono hd (by simp) F' hF]
      rw [hd] at h; exact h
    | .exn s₂ e => rw [hd] at h; simp at h
    | .timeout => rw [hd] at h; simp at h
    | .unsupported msg => rw [hd] at h; simp at h
  | .exn s e => simp at h
  | .timeout => simp at h
  | .unsupported msg => simp at h

/-- The bounded stepper's continuation is fuel-insensitive once decided —
`drainCont_pin`'s twin. -/
private theorem stepCont_pin {m : Module} {F F' n : Nat} (hF : F ≤ F')
    {x : Run FrameState (Option (RVal × GenCont))} {st' : FrameState}
    {p : List RVal × GenCont} (h : x ⤳ stepCont m F n = .ok st' p) :
    x ⤳ stepCont m F' n = .ok st' p := by
  match x with
  | .ok s Option.none => simpa [stepCont] using h
  | .ok s (some (v, k')) =>
    simp only [Run.ok_bind, stepCont] at h ⊢
    match hd : stepGenN m F s k' n with
    | .ok s₂ q =>
      rw [stepGenN_mono hd (by simp) F' hF]
      rw [hd] at h; exact h
    | .exn s₂ e => rw [hd] at h; simp at h
    | .timeout => rw [hd] at h; simp at h
    | .unsupported msg => rw [hd] at h; simp at h
  | .exn s e => simp at h
  | .timeout => simp at h
  | .unsupported msg => simp at h

/-! ## The spec objects -/

/-- **From `st` with frame stack `k` the generator yields exactly `vs` and
then finishes, landing in `st'`.** Total: `timeout` is excluded by the
threshold, `unsupported` by there being no arm for it.

The fuel-threshold shape (`∃ t, ∀ F ≥ t`) is the total-correctness idiom of
every other judgment in the repo (`CallsTo`, `PyStmtTriple`, `EvalsTo`), and
it is what lets a generator fact splice into a surrounding run at whatever
fuel that run happens to be using. -/
def GenYields (m : Module) (st : FrameState) (k : GenCont)
    (vs : List RVal) (st' : FrameState) : Prop :=
  ∃ t, ∀ F ≥ t, drainGen m F st k = .ok st' vs

/-- **The lazy half**: the first `vs` values, with the machine left
SUSPENDED at `k'` — what a consumer that abandons the generator needs
(`gen_lab.two_phase`, and `bound`'s beta cutoff). An infinite generator has
no `GenYields` and every `GenYieldsPrefix`. -/
def GenYieldsPrefix (m : Module) (st : FrameState) (k : GenCont)
    (vs : List RVal) (st' : FrameState) (k' : GenCont) : Prop :=
  ∃ t, ∀ F ≥ t, stepGenN m F st k vs.length = .ok st' (vs, k')

/-- One DECIDED resumption step of a suspended machine, threshold form:
`execGen`'s answer, pinned at every large enough fuel. Either a yield
(`some (v, k')`, carrying its own resumption) or exhaustion (`none`). -/
def GenSteps (m : Module) (st : FrameState) (k : GenCont)
    (r : Option (RVal × GenCont)) (st' : FrameState) : Prop :=
  ∃ t, ∀ F ≥ t, execGen m F st k = .ok st' r

/-- `⟨st, k⟩` resumes exactly as `⟨st₁, k₁⟩` does — a **silent** transition:
the interpreter rearranged the frame stack (pushed a loop frame, popped an
exhausted one, ran a yield-free statement) without producing a value. The
fuel offset `d` is existential, which is what makes silent transitions
compose transitively. -/
def GenSilent (m : Module) (st : FrameState) (k : GenCont)
    (st₁ : FrameState) (k₁ : GenCont) : Prop :=
  ∃ d t, ∀ F ≥ t, execGen m (F + d) st k = execGen m F st₁ k₁

/-- **The compositional object**: the frame PREFIX `pre` emits `ws` and
falls through, leaving the machine at `st₁` with whatever was below it —
*for every* continuation `k`. The interpreter only scrutinizes head frames,
so this is exactly as strong as the per-frame behaviour, and composition is
`List.append` on both the frames and the output (`GenEmits.trans`). -/
def GenEmits (m : Module) (st : FrameState) (pre : GenCont)
    (ws : List RVal) (st₁ : FrameState) : Prop :=
  ∀ k vs st', GenYields m st₁ k vs st' → GenYields m st (pre ++ k) (ws ++ vs) st'

/-! ## Introduction, and the two primitives -/

namespace GenYields

/-- Introduce a `GenYields` from ONE concrete drain (any fuel) —
monotonicity is `drainGen_mono`'s job, not the introduction's. -/
theorem of_drain {m : Module} {fuel : Nat} {st st' : FrameState} {k : GenCont}
    {vs : List RVal} (h : drainGen m fuel st k = .ok st' vs) :
    GenYields m st k vs st' :=
  ⟨fuel, fun F hF => drainGen_mono h (by simp) F hF⟩

/-- The machine is already finished: an EXHAUSTED step yields nothing. -/
theorem done {m : Module} {st st' : FrameState} {k : GenCont}
    (h : GenSteps m st k Option.none st') : GenYields m st k [] st' := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  rw [drainGen_succ, ht F' hF']
  rfl

/-- One YIELD, then the rest — the induction step of every drain. -/
theorem cons {m : Module} {st st₁ st' : FrameState} {k k' : GenCont}
    {v : RVal} {vs : List RVal} (hstep : GenSteps m st k (some (v, k')) st₁)
    (hrest : GenYields m st₁ k' vs st') : GenYields m st k (v :: vs) st' := by
  obtain ⟨t₁, ht₁⟩ := hstep
  obtain ⟨t₂, ht₂⟩ := hrest
  refine ⟨t₁ + t₂ + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  rw [drainGen_succ, ht₁ F' (by omega)]
  simp only [Run.ok_bind, drainCont]
  rw [ht₂ F' (by omega)]
  rfl

/-- A silent transition transports the whole remaining output. -/
theorem silent {m : Module} {st st₁ st' : FrameState} {k k₁ : GenCont}
    {vs : List RVal} (hs : GenSilent m st k st₁ k₁)
    (h : GenYields m st₁ k₁ vs st') : GenYields m st k vs st' := by
  obtain ⟨d, t₁, ht₁⟩ := hs
  obtain ⟨t₂, ht₂⟩ := h
  refine ⟨t₁ + t₂ + d + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  obtain ⟨G, rfl⟩ : ∃ G, F' = G + d := ⟨F' - d, by omega⟩
  rw [drainGen_succ, ht₁ G (by omega)]
  have hd := ht₂ (G + 1) (by omega)
  rw [drainGen_succ] at hd
  exact drainCont_pin (by omega) hd

end GenYields

namespace GenSteps

/-- A silent transition transports a step fact. -/
theorem silent {m : Module} {st st₁ st' : FrameState} {k k₁ : GenCont}
    {r : Option (RVal × GenCont)} (hs : GenSilent m st k st₁ k₁)
    (h : GenSteps m st₁ k₁ r st') : GenSteps m st k r st' := by
  obtain ⟨d, t₁, ht₁⟩ := hs
  obtain ⟨t₂, ht₂⟩ := h
  refine ⟨t₁ + t₂ + d, fun F hF => ?_⟩
  obtain ⟨G, rfl⟩ : ∃ G, F = G + d := ⟨F - d, by omega⟩
  rw [ht₁ G (by omega)]
  exact ht₂ G (by omega)

end GenSteps

namespace GenSilent

theorem refl {m : Module} {st : FrameState} {k : GenCont} :
    GenSilent m st k st k := ⟨0, 0, fun _ _ => rfl⟩

theorem trans {m : Module} {st st₁ st₂ : FrameState} {k k₁ k₂ : GenCont}
    (h₁ : GenSilent m st k st₁ k₁) (h₂ : GenSilent m st₁ k₁ st₂ k₂) :
    GenSilent m st k st₂ k₂ := by
  obtain ⟨d₁, t₁, ht₁⟩ := h₁
  obtain ⟨d₂, t₂, ht₂⟩ := h₂
  refine ⟨d₁ + d₂, t₁ + t₂, fun F hF => ?_⟩
  rw [show F + (d₁ + d₂) = (F + d₂) + d₁ from by omega, ht₁ (F + d₂) (by omega),
    ht₂ F (by omega)]

/-- Introduce a silent transition from one concrete pair of unfolds — the
shape every frame rule below closes with. -/
theorem of_step {m : Module} {st st₁ : FrameState} {k k₁ : GenCont}
    (h : ∀ F, execGen m (F + 1) st k = execGen m F st₁ k₁) :
    GenSilent m st k st₁ k₁ := ⟨1, 0, fun F _ => h F⟩

end GenSilent

/-! ## `GenEmits`: the frame-stack-polymorphic calculus -/

namespace GenEmits

/-- The empty prefix emits nothing. -/
theorem nil {m : Module} {st : FrameState} : GenEmits m st [] [] st :=
  fun _ _ _ h => h

/-- **Composition is `List.append`** — on the frames and on the output at
once. This is the property the whole design is arranged around. -/
theorem trans {m : Module} {st st₁ st₂ : FrameState} {p₁ p₂ : GenCont}
    {w₁ w₂ : List RVal} (h₁ : GenEmits m st p₁ w₁ st₁)
    (h₂ : GenEmits m st₁ p₂ w₂ st₂) : GenEmits m st (p₁ ++ p₂) (w₁ ++ w₂) st₂ := by
  intro k vs st' hk
  have := h₁ (p₂ ++ k) (w₂ ++ vs) st' (h₂ k vs st' hk)
  rwa [← List.append_assoc, ← List.append_assoc] at this

/-- Close an emission into a total `GenYields` (the prefix IS the whole
stack). -/
theorem toYields {m : Module} {st st₁ : FrameState} {pre : GenCont}
    {ws : List RVal} (h : GenEmits m st pre ws st₁) :
    GenYields m st pre ws st₁ := by
  have := h [] [] st₁ (GenYields.done ⟨1, fun F hF => by
    obtain ⟨F', rfl, _⟩ := succ_le_dest hF
    rw [execGen]⟩)
  simpa using this

/-- One SILENT step, frame-stack-polymorphic. -/
theorem silent {m : Module} {st st₁ st₂ : FrameState} {pre pre₁ : GenCont}
    {ws : List RVal} (hsil : ∀ k, GenSilent m st (pre ++ k) st₁ (pre₁ ++ k))
    (hrest : GenEmits m st₁ pre₁ ws st₂) : GenEmits m st pre ws st₂ :=
  fun k vs st' hk => GenYields.silent (hsil k) (hrest k vs st' hk)

/-- One YIELD, frame-stack-polymorphic. -/
theorem cons {m : Module} {st st₁ st₂ : FrameState} {pre pre₁ : GenCont}
    {v : RVal} {ws : List RVal}
    (hstep : ∀ k, GenSteps m st (pre ++ k) (some (v, pre₁ ++ k)) st₁)
    (hrest : GenEmits m st₁ pre₁ ws st₂) : GenEmits m st pre (v :: ws) st₂ :=
  fun k vs st' hk => GenYields.cons (hstep k) (hrest k vs st' hk)

end GenEmits

/-! ## The frame rules, one per `GenFrame` kind

Each is a `GenSilent` or `GenSteps` fact about `f :: … ++ k` with `k` free,
which is exactly the strength `GenEmits.silent`/`GenEmits.cons` consume.
They are transcriptions of `execGen`'s arms and nothing more; the content
is that they hold at EVERY continuation. -/

/-- The exhausted stack: nothing left to run. -/
theorem genSteps_nil {m : Module} {st : FrameState} :
    GenSteps m st [] Option.none st :=
  ⟨1, fun F hF => by obtain ⟨F', rfl, _⟩ := succ_le_dest hF; rw [execGen]⟩

/-- The exhausted stack yields nothing (the `yields_nil` of the memo). -/
theorem genYields_nil {m : Module} {st : FrameState} :
    GenYields m st [] [] st := GenYields.done genSteps_nil

/-- A finished `block` frame pops. -/
theorem genSilent_blockNil {m : Module} {st : FrameState} {k : GenCont} :
    GenSilent m st (.block [] :: k) st k :=
  GenSilent.of_step fun _ => by rw [execGen]

/-- **The yield rule**: `yield e` in statement position emits `e`'s value
and leaves the rest of the block as the resumption. -/
theorem genSteps_yieldHere {m : Module} {st : FrameState} {s : Stmt}
    {e : Expr} {ss : List Stmt} {k : GenCont} {v : RVal}
    (hplan : genPlan s = .yieldHere e) (hv : EvalsTo m st e v) :
    GenSteps m st (.block (s :: ss) :: k) (some (v, .block ss :: k)) st := by
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  rw [execGen]
  simp only [hplan, ht F' hF', Run.ok_bind]

/-- **The branch rule**: `if` with a `yield` somewhere inside pushes the
taken arm as a block frame. -/
theorem genSilent_branch {m : Module} {st : FrameState} {s : Stmt}
    {test : Expr} {body orelse ss : List Stmt} {k : GenCont} {tv : RVal}
    {b : Bool} (hplan : genPlan s = .branch test body orelse)
    (hv : EvalsTo m st test tv) (hb : truthyH st.world.heap tv = .ok b) :
    GenSilent m st (.block (s :: ss) :: k) st
      ((if b then GenFrame.block body else GenFrame.block orelse)
        :: .block ss :: k) := by
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [hplan, ht F hF, Run.ok_bind, hb, Run.liftRes]

/-- **The while rule (push)**: a `while` with a `yield` inside becomes a
`whileLoop` frame; re-entering the frame re-tests. -/
theorem genSilent_whileHere {m : Module} {st : FrameState} {s : Stmt}
    {test : Expr} {body orelse ss : List Stmt} {k : GenCont}
    (hplan : genPlan s = .whileHere test body orelse) :
    GenSilent m st (.block (s :: ss) :: k) st
      (.whileLoop test body orelse :: .block ss :: k) :=
  GenSilent.of_step fun _ => by rw [execGen]; simp only [hplan]

/-- **The while rule (re-entry, test true)**. -/
theorem genSilent_whileTrue {m : Module} {st : FrameState} {test : Expr}
    {body orelse : List Stmt} {k : GenCont} {tv : RVal}
    (hv : EvalsTo m st test tv) (hb : truthyH st.world.heap tv = .ok true) :
    GenSilent m st (.whileLoop test body orelse :: k) st
      (.block body :: .whileLoop test body orelse :: k) := by
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [ht F hF, Run.ok_bind, hb, Run.liftRes, if_pos]

/-- **The while rule (re-entry, test false)**: the loop exits into its
`orelse` (pushed on normal exit, skipped by `break` — Runtime.lean). -/
theorem genSilent_whileFalse {m : Module} {st : FrameState} {test : Expr}
    {body orelse : List Stmt} {k : GenCont} {tv : RVal}
    (hv : EvalsTo m st test tv) (hb : truthyH st.world.heap tv = .ok false) :
    GenSilent m st (.whileLoop test body orelse :: k) st (.block orelse :: k) := by
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [ht F hF, Run.ok_bind, hb, Run.liftRes, if_neg, Bool.false_eq_true,
    not_false_eq_true]

/-- **The for rule (push, value sequence)**: `for x in <immutable>` inside
a generator pushes a `forSeq` frame over exactly the elements `IterVals`
names. The same `IterVals` the statement-level for rule uses (VC2.lean) —
a snapshot IS the live semantics for each of those sources, which is what
makes a remainder-indexed invariant faithful. -/
theorem genSilent_forHere {m : Module} {st : FrameState} {s : Stmt}
    {target iter : Expr} {body ss : List Stmt} {k : GenCont} {v : RVal}
    {xs : List RVal} (hplan : genPlan s = .forHere target iter body)
    (hv : EvalsTo m st iter v) (hxs : IterVals v xs) :
    GenSilent m st (.block (s :: ss) :: k) st
      (.forSeq target xs body :: .block ss :: k) := by
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  cases hxs <;> simp only [hplan, ht F hF, Run.ok_bind]

/-- The exhausted value sequence pops. -/
theorem genSilent_forSeqNil {m : Module} {st : FrameState} {target : Expr}
    {body : List Stmt} {k : GenCont} :
    GenSilent m st (.forSeq target [] body :: k) st k :=
  GenSilent.of_step fun _ => by rw [execGen]

/-- One element of a value sequence: bind the target, push the body. -/
theorem genSilent_forSeqCons {m : Module} {st : FrameState} {target : Expr}
    {x : RVal} {rest : List RVal} {body : List Stmt} {k : GenCont} {env₁ : REnv}
    (hasg : assignToH st.world.heap st.locals target x = .ok env₁) :
    GenSilent m st (.forSeq target (x :: rest) body :: k)
      { st with locals := env₁ } (.block body :: .forSeq target rest body :: k) :=
  GenSilent.of_step fun _ => by rw [execGen]; simp only [hasg, Run.liftRes, Run.ok_bind]

/-- The exhausted `enumerate` snapshot pops. -/
theorem genSilent_enumSeqNil {m : Module} {st : FrameState} {i : Int}
    {k : GenCont} : GenSilent m st (.enumSeq i [] :: k) st k :=
  GenSilent.of_step fun _ => by rw [execGen]

/-- **The `enumerate` rule**: one `(index, element)` tuple per step, the
index advancing — `enumerate` is a generator FRAME, not a second object
kind, so it needs no separate machinery. -/
theorem genSteps_enumSeqCons {m : Module} {st : FrameState} {i : Int}
    {x : RVal} {rest : List RVal} {k : GenCont} :
    GenSteps m st (.enumSeq i (x :: rest) :: k)
      (some (.tuple #[.int i, x], .enumSeq (i + 1) rest :: k)) st :=
  ⟨1, fun F hF => by obtain ⟨F', rfl, _⟩ := succ_le_dest hF; rw [execGen]⟩

/-- **The ray rule**: `itertools.count` never exhausts, so its only spec is
a PREFIX one — every step yields, and a consumer's `break` is what ends it
(sunfish's `for j in count(i + d, d)`). There is deliberately no
`GenYields` for a `countFrom` frame: it has none. -/
theorem genSteps_countFrom {m : Module} {st : FrameState} {cur step : Int}
    {k : GenCont} :
    GenSteps m st (.countFrom cur step :: k)
      (some (.int cur, .countFrom (cur + step) step :: k)) st :=
  ⟨1, fun F hF => by obtain ⟨F', rfl, _⟩ := succ_le_dest hF; rw [execGen]⟩

/-! ### The live-cursor frames

These re-read the heap object every step (CPython's list iterator is an
index cursor against the LIVE object), so their transitions carry the heap
read AT THE STATE THE STEP IS TAKEN FROM as a hypothesis rather than a
snapshot. That is all a single step needs; a loop-level invariant rule over
them would need a stability side condition and is deliberately not here
(the file header says why). -/

/-- One element of a live heap-list cursor. -/
theorem genSilent_forListCons {m : Module} {st : FrameState} {target : Expr}
    {ad : Addr} {i : Nat} {body : List Stmt} {k : GenCont} {xs : Array RVal}
    {env₁ : REnv} (hobj : Heap.get? st.world.heap ad = some (.list xs))
    (hi : i < xs.size)
    (hasg : assignToH st.world.heap st.locals target (xs.getD i .none) = .ok env₁) :
    GenSilent m st (.forList target ad i body :: k)
      { st with locals := env₁ }
      (.block body :: .forList target ad (i + 1) body :: k) :=
  GenSilent.of_step fun _ => by
    rw [execGen]
    simp only [hobj, hi, if_pos, hasg, Run.liftRes, Run.ok_bind]

/-- The live heap-list cursor ran off the end (the object may have SHRUNK
under it — that is the faithful behaviour, and it is why the bound is read
here rather than fixed at entry). -/
theorem genSilent_forListDone {m : Module} {st : FrameState} {target : Expr}
    {ad : Addr} {i : Nat} {body : List Stmt} {k : GenCont} {xs : Array RVal}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : ¬ i < xs.size) :
    GenSilent m st (.forList target ad i body :: k) st k :=
  GenSilent.of_step fun _ => by rw [execGen]; simp only [hobj, hi, if_neg, not_false_eq_true]

/-- One element of a live `enumerate` cursor over a heap list. -/
theorem genSteps_enumListCons {m : Module} {st : FrameState} {i : Int}
    {ad : Addr} {cur : Nat} {k : GenCont} {xs : Array RVal}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : cur < xs.size) :
    GenSteps m st (.enumList i ad cur :: k)
      (some (.tuple #[.int i, xs.getD cur .none], .enumList (i + 1) ad (cur + 1) :: k))
      st :=
  ⟨1, fun F hF => by
    obtain ⟨F', rfl, _⟩ := succ_le_dest hF
    rw [execGen]
    simp only [hobj, hi, if_pos]⟩

/-- The live `enumerate` cursor ran off the end. -/
theorem genSilent_enumListDone {m : Module} {st : FrameState} {i : Int}
    {ad : Addr} {cur : Nat} {k : GenCont} {xs : Array RVal}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : ¬ cur < xs.size) :
    GenSilent m st (.enumList i ad cur :: k) st k :=
  GenSilent.of_step fun _ => by rw [execGen]; simp only [hobj, hi, if_neg, not_false_eq_true]

/-- One element of a generator consuming a generator: the inner `stepIter`
yielded, so the outer binds the target and pushes the body. -/
theorem genSilent_forGenCons {m : Module} {st : FrameState} {target : Expr}
    {ad : Addr} {body : List Stmt} {k : GenCont} {w₁ : World} {v : RVal}
    {env₁ : REnv} (hstep : ∃ t, ∀ F ≥ t, stepIter m F st.world ad = .ok w₁ (some v))
    (hasg : assignToH w₁.heap st.locals target v = .ok env₁) :
    GenSilent m st (.forGen target ad body :: k) ⟨w₁, env₁⟩
      (.block body :: .forGen target ad body :: k) := by
  obtain ⟨t, ht⟩ := hstep
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [ht F hF, Run.withLocals, Run.ok_bind, hasg, Run.liftRes]

/-- The inner generator is exhausted: the `forGen` frame pops. -/
theorem genSilent_forGenDone {m : Module} {st : FrameState} {target : Expr}
    {ad : Addr} {body : List Stmt} {k : GenCont} {w₁ : World}
    (hstep : ∃ t, ∀ F ≥ t, stepIter m F st.world ad = .ok w₁ Option.none) :
    GenSilent m st (.forGen target ad body :: k) ⟨w₁, st.locals⟩ k := by
  obtain ⟨t, ht⟩ := hstep
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [ht F hF, Run.withLocals, Run.ok_bind]

/-! ## The heap-object bridge

Everything above speaks about a frame stack and a frame state. The
interpreter's consumers (`next`, `for … in gen`, `sorted`/`max`/`min` via
`drainIter`) speak about a generator OBJECT at a heap address: `stepIter`
flips its status to `.running`, runs `execGen`, and writes the resumption
back. These two theorems are that wrapper, per step — a `GenSteps` fact
about the stored continuation IS the object's step, with the write-back
made explicit rather than assumed.

What is NOT here, and is the recorded remainder of this landing: the
`drainIter` bridge over a WHOLE drain. It needs a heap-stability side
condition (the generator body must not itself write slot `a` — the
write-back would otherwise clobber, and `drainGen`, which threads no
object, cannot see it). Stating that condition before a consumer needs it
would be guessing at its shape; the per-step bridges below are what L3's
walker case consumes, and they are unconditional. -/

/-- **One step of a suspended generator OBJECT** that yields: the stored
continuation's `GenSteps` fact, plus the two heap writes `stepIter`
performs (`.running` on entry, the new continuation `.suspended` on exit).
Both writes are hypotheses rather than side conditions, so nothing here
assumes the address is live — a dangling one simply has no proof. -/
theorem stepIter_of_genSteps {m : Module} {w : World} {a : Addr}
    {qname : String} {locals : REnv} {cont cont' : GenCont}
    {status : GenStatus} {h₁ h₂ : Heap} {st₁ : FrameState} {v : RVal}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont status))
    (hstatus : status = .created ∨ status = .suspended)
    (hrun : Heap.update w.heap a (.generator qname locals cont .running) = some h₁)
    (hstep : GenSteps m ⟨{ w with heap := h₁ }, locals⟩ cont (some (v, cont')) st₁)
    (hback : Heap.update st₁.world.heap a
        (.generator qname st₁.locals cont' .suspended) = some h₂) :
    ∃ t, ∀ F ≥ t, stepIter m F w a
      = .ok { st₁.world with heap := h₂ } (some v) := by
  obtain ⟨t, ht⟩ := hstep
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  rw [stepIter]
  rcases hstatus with rfl | rfl <;>
    simp only [hobj, hrun, ht F' hF', Run.ok_bindE, hback, Run.toWorld]

/-- **One step of a suspended generator OBJECT** that is EXHAUSTED: the
object is closed and its continuation dropped, which is what makes every
later `next` a `StopIteration` rather than a resume. -/
theorem stepIter_of_genDone {m : Module} {w : World} {a : Addr}
    {qname : String} {locals : REnv} {cont : GenCont} {status : GenStatus}
    {h₁ h₂ : Heap} {st₁ : FrameState}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont status))
    (hstatus : status = .created ∨ status = .suspended)
    (hrun : Heap.update w.heap a (.generator qname locals cont .running) = some h₁)
    (hstep : GenSteps m ⟨{ w with heap := h₁ }, locals⟩ cont Option.none st₁)
    (hback : Heap.update st₁.world.heap a
        (.generator qname st₁.locals [] .closed) = some h₂) :
    ∃ t, ∀ F ≥ t, stepIter m F w a
      = .ok { st₁.world with heap := h₂ } Option.none := by
  obtain ⟨t, ht⟩ := hstep
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  rw [stepIter]
  rcases hstatus with rfl | rfl <;>
    simp only [hobj, hrun, ht F' hF', Run.ok_bindE, hback, Run.toWorld]

/-! ## Delegation: the yield-free statements

`genPlan` classifies every statement into `.delegate` (no `yield` in it) or
one of five suspendable shapes, and the `.delegate` arm calls **`execStmt`**
— the ordinary statement executor. So the generator tier does not
re-implement statement reasoning: a yield-free statement inside a generator
body is discharged by the layer-1/2 triples that already exist. -/

/-- **The delegate rule as a SILENT transition**: a yield-free statement
that falls through moves the machine and emits nothing. This is the form
the other rules compose with; `GenEmits.blockDelegate` below is the form a
user writes (it consumes a statement triple instead of a pinned run). -/
theorem genSilent_delegate {m : Module} {s : Stmt} {ss : List Stmt}
    {k : GenCont} {st st₁ : FrameState} (hplan : genPlan s = .delegate)
    (hrun : ∃ t, ∀ F ≥ t, execStmt m F st s = .ok st₁ .next) :
    GenSilent m st (.block (s :: ss) :: k) st₁ (.block ss :: k) := by
  obtain ⟨t, ht⟩ := hrun
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [hplan, ht F hF, Run.ok_bind]

/-- **The delegate rule**: a yield-free statement that FALLS THROUGH runs
as an ordinary statement triple, and the generator continues with the rest
of the block.

The postcondition's other arms are `False` by `PyPost.ofNext`: `break` and
`continue` unwind the frame stack (`genBreak`/`genContinue`), which reaches
BELOW the polymorphic prefix and therefore cannot be stated at this
altitude — put the enclosing loop frame inside `pre` and use the loop rules
instead. `return` is `genYields_blockReturn`. -/
theorem GenEmits.blockDelegate {m : Module} {P : FrameState → Prop} {s : Stmt}
    {ss : List Stmt} {st st₂ : FrameState} {ws : List RVal}
    (hplan : genPlan s = .delegate)
    (htriple : PyStmtTriple m P s
      (PyPost.ofNext (fun st₁ => GenEmits m st₁ [.block ss] ws st₂)))
    (hP : P st) : GenEmits m st [.block (s :: ss)] ws st₂ := by
  obtain ⟨r, t, hr, hrun⟩ := htriple.exec hP
  match r, hr with
  | .ok st₁ .next, hr =>
    refine GenEmits.silent (pre₁ := [.block ss]) (fun k => ?_) hr
    simpa using genSilent_delegate (k := k) hplan ⟨t, hrun⟩

/-- A `return` (valueless — `return <value>` inside a generator is the
`StopIteration.value` channel and refuses loudly) ENDS the generator: the
remaining output is empty whatever the frames below say. Not
frame-polymorphic in the `GenEmits` sense — it discards the continuation,
which is exactly what makes it a `GenYields` rule. -/
theorem genYields_blockReturn {m : Module} {P : FrameState → Prop} {s : Stmt}
    {ss : List Stmt} {k : GenCont} {st st₁ : FrameState}
    (hplan : genPlan s = .delegate)
    (htriple : PyStmtTriple m P s
      { next := fun _ => False, ret := fun v st' => v = .none ∧ st' = st₁ })
    (hP : P st) : GenYields m st (.block (s :: ss) :: k) [] st₁ := by
  obtain ⟨r, t, hr, hrun⟩ := htriple.exec hP
  match r, hr with
  | .ok st' (.ret v), hr =>
    obtain ⟨rfl, rfl⟩ := hr
    refine GenYields.done ⟨t + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    rw [execGen]
    simp only [hplan, hrun F' hF', Run.ok_bind]

/-! ## The sequence rule -/

/-- **The sequence rule** — the point of the whole file: iterating an
immutable value sequence inside a generator is the invariant a user already
writes for a `for` loop, plus an output accumulator. `execFor_of_invariant`
(VC2.lean) with the output list threaded: structural induction on the
remaining elements, no measure.

The elements are spec-side (`α`) behind a marshalling `elt`, exactly as
`PyStmtTriple.forLoop` does it, and `out` is the per-element output. The
loop's whole contribution is `(as.map out).flatten` — outputs concatenated
per element, which is `GenEmits.trans` iterated. -/
theorem GenEmits.forSeq {m : Module} {α : Type} {target : Expr}
    {body : List Stmt} (elt : α → RVal) (Inv : List α → FrameState → Prop)
    (out : α → List RVal)
    (hstep : ∀ a rest st, Inv (a :: rest) st →
      ∃ env₁ st₂, assignToH st.world.heap st.locals target (elt a) = .ok env₁ ∧
        Inv rest st₂ ∧
        GenEmits m { st with locals := env₁ } [.block body] (out a) st₂) :
    ∀ as st, Inv as st →
      ∃ st₂, Inv [] st₂ ∧
        GenEmits m st [.forSeq target (as.map elt) body] ((as.map out).flatten) st₂ := by
  intro as
  induction as with
  | nil =>
    intro st hI
    refine ⟨st, hI, ?_⟩
    simpa using
      GenEmits.silent (pre₁ := ([] : GenCont))
        (fun k => by simpa using genSilent_forSeqNil) GenEmits.nil
  | cons a rest ih =>
    intro st hI
    obtain ⟨env₁, st₂, hasg, hI₂, hbody⟩ := hstep a rest st hI
    obtain ⟨st₃, hI₃, hloop⟩ := ih st₂ hI₂
    refine ⟨st₃, hI₃, ?_⟩
    have hcomp :
        GenEmits m { st with locals := env₁ }
          ([.block body] ++ [.forSeq target (rest.map elt) body])
          (out a ++ (rest.map out).flatten) st₃ := GenEmits.trans hbody hloop
    have := GenEmits.silent
      (pre := [GenFrame.forSeq target ((a :: rest).map elt) body])
      (pre₁ := [GenFrame.block body, GenFrame.forSeq target (rest.map elt) body])
      (fun k => by simpa using genSilent_forSeqCons (k := k) hasg) hcomp
    simpa using this

/-! ## The lazy half: prefixes

`GenYieldsPrefix` is what a consumer that BREAKS needs. Its rules are the
same primitives read one step at a time — and the ray (`countFrom`) has
nothing else, since it never exhausts. -/


namespace GenYieldsPrefix

/-- Introduce a prefix from ONE concrete bounded run. -/
theorem of_step {m : Module} {fuel : Nat} {st st' : FrameState}
    {k k' : GenCont} {vs : List RVal}
    (h : stepGenN m fuel st k vs.length = .ok st' (vs, k')) :
    GenYieldsPrefix m st k vs st' k' :=
  ⟨fuel, fun F hF => stepGenN_mono h (by simp) F hF⟩

/-- The empty prefix: zero steps, machine untouched. -/
theorem nil {m : Module} {st : FrameState} {k : GenCont} :
    GenYieldsPrefix m st k [] st k :=
  ⟨0, fun F _ => by rw [show ([] : List RVal).length = 0 from rfl, stepGenN_zero]⟩

/-- One more value on the front of a prefix. -/
theorem cons {m : Module} {st st₁ st' : FrameState} {k k₁ k' : GenCont}
    {v : RVal} {vs : List RVal} (hstep : GenSteps m st k (some (v, k₁)) st₁)
    (hrest : GenYieldsPrefix m st₁ k₁ vs st' k') :
    GenYieldsPrefix m st k (v :: vs) st' k' := by
  obtain ⟨t₁, ht₁⟩ := hstep
  obtain ⟨t₂, ht₂⟩ := hrest
  refine ⟨t₁ + t₂, fun F hF => ?_⟩
  rw [show (v :: vs).length = vs.length + 1 from rfl, stepGenN_succ,
    ht₁ F (by omega)]
  simp only [Run.ok_bind, stepCont, ht₂ F (by omega)]

/-- A silent transition transports a NONEMPTY prefix. The empty prefix is
deliberately excluded: `GenYieldsPrefix … [] st' k'` pins `k'` to the stack
it was asked about — zero steps observe nothing, so there is nothing for a
silent transition to carry across. -/
theorem silent {m : Module} {st st₁ st' : FrameState} {k k₁ k' : GenCont}
    {v : RVal} {vs : List RVal} (hs : GenSilent m st k st₁ k₁)
    (h : GenYieldsPrefix m st₁ k₁ (v :: vs) st' k') :
    GenYieldsPrefix m st k (v :: vs) st' k' := by
  obtain ⟨d, t₁, ht₁⟩ := hs
  obtain ⟨t₂, ht₂⟩ := h
  refine ⟨t₁ + t₂ + d, fun F hF => ?_⟩
  obtain ⟨G, rfl⟩ : ∃ G, F = G + d := ⟨F - d, by omega⟩
  rw [show (v :: vs).length = vs.length + 1 from rfl, stepGenN_succ,
    ht₁ G (by omega)]
  have hG := ht₂ G (by omega)
  rw [show (v :: vs).length = vs.length + 1 from rfl, stepGenN_succ] at hG
  exact stepCont_pin (by omega) hG

end GenYieldsPrefix

/-- The values an infinite `count(cur, step)` frame hands over in `n`
steps. Recursive rather than a closed form on purpose: the Python lane is
core-only (no `ring`), and the ray rule should cost no arithmetic. -/
def rayVals (cur step : Int) : Nat → List RVal
  | 0 => []
  | n + 1 => .int cur :: rayVals (cur + step) step n

/-- Where an infinite `count(cur, step)` frame is left after `n` steps. -/
def rayFrom (cur step : Int) : Nat → Int
  | 0 => cur
  | n + 1 => rayFrom (cur + step) step n

/-- **The ray rule**: `count(cur, step)` hands over as many values as
anyone asks and is still suspended afterwards — the only spec an infinite
frame has, and the one sunfish's `for j in count(i + d, d)` needs. Note
what is NOT provable here and is not claimed: there is no `GenYields` for a
`countFrom` frame, because it never finishes. -/
theorem genYieldsPrefix_countFrom {m : Module} {st : FrameState} {k : GenCont} :
    ∀ (n : Nat) (cur step : Int),
      GenYieldsPrefix m st (.countFrom cur step :: k) (rayVals cur step n) st
        (.countFrom (rayFrom cur step n) step :: k) := by
  intro n
  induction n with
  | zero => intro cur step; exact GenYieldsPrefix.nil
  | succ n ih =>
    intro cur step
    exact GenYieldsPrefix.cons genSteps_countFrom (ih (cur + step) step)

/-! ## L3: the consumer side — a generator OBJECT in a `for` statement

Landing **L3** of docs/generator-tier-architecture.md §2. Everything above
specifies a suspended MACHINE (a frame stack and a frame state). A consumer
never sees one: it calls a generator function, gets a heap OBJECT back, and
steps it with a `for`. Three facts are new here, and nothing else is.

* **`EvalsIn`** — evaluating `upto(n)` ALLOCATES, so its value fact cannot
  be an `EvalsTo`: that judgment is pinned-state by construction. `EvalsIn`
  is its stateful twin, exactly as `CallsIn` is `CallsTo`'s.
  `EvalsIn.genCall` is the memo's `EvalsTo.genCall` under the name its own
  state change forces: a generator call is a `.ref` at the heap's end whose
  object carries the frame stack `GenYields` talks about — **a value with a
  specification**, which is the sentence L3 exists to make true.

* **`PyStmtTriple.assignNameIn`** — `g = upto(n)`. The pure assignment rule
  pins the out-state's world to the in-state's, so no instance of it can
  bind an allocation; this one stores into the world the CALL produced. It
  is what lets a generator be NAMED rather than only consumed in place,
  which is what a second consumer of the same object needs.

* **`PyStmtTriple.forGen`** — `for x in <generator>`, with the same
  remainder-indexed invariant the value-sequence `for` rule uses.
  `execForGen_of_invariant` underneath is `execFor_of_invariant` with one
  `stepIter` in front of each round.

**Where the heap-stability side condition went.** L2 recorded that a
whole-drain bridge needs one (the body must not write the iterator slot).
The loop rule does not: it asks for a FRESH `IterSteps` fact at the state
each round actually begins in, and the INVARIANT is what carries the object
across the body. A body that clobbers slot `a` cannot re-establish the
invariant; a body that leaves it alone re-establishes it for free. So no
`WritesAvoid`-style frame predicate is introduced — at this altitude it
would be a special case dressed as a rule. (The `drainIter` bridge still
wants one and is still recorded as L2's remainder: a drain has no body in
which to re-establish anything.)

**And the lazy half needs no second rule.** The memo expected
`GenYieldsPrefix` at the consumer level for the `break` case. It is not
needed, and the reason is worth stating: **`Inv []` may be `False`.** A
consumer that always escapes — `first_over_inf`'s `return`, `bound`'s beta
`break` — writes an invariant that is unsatisfiable at the empty remainder;
that discharges the exhaustion obligation vacuously and never asks the
generator to finish. An INFINITE generator is consumed by this rule, and it
is the same rule. `gen_lab.two_phase` is where that half is EXERCISED: both
its loops carry an invariant whose empty-remainder case is `False`, and the
second one resumes the object the first abandoned. -/

/-! ### Heap bookkeeping for a suspended object

Three small `Array` facts, stated here because the generator tier is where
they are load-bearing: a call allocates at the END of the heap, and
`stepIter` writes that one slot twice per step. -/

/-- **The freshly allocated object is readable at the address the call
answered** — the heap fact `PyStmtTriple.forGen`'s `hiter` obligation needs
the moment `EvalsIn.genCall` has fired. -/
theorem Heap.get?_push_size (h : Heap) (o : Obj) :
    Heap.get? (h.push o) h.size = some o := by
  simp [Heap.get?, Array.size_push]

/-- **Two writes to the same slot are the second write** — what makes
`stepIter`'s enter-`.running`/exit-`.suspended` pair one observable change
of the object rather than two. -/
theorem Heap.update_update {h h₁ : Heap} {a : Addr} {o o' : Obj}
    (hu : Heap.update h a o = some h₁) :
    Heap.update h₁ a o' = Heap.update h a o' := by
  unfold Heap.update at *
  split at hu
  · next hlt =>
      injection hu with hu
      subst hu
      rw [dif_pos (by simpa using hlt : a < (h.set a o hlt).size), dif_pos hlt]
      exact congrArg some (Array.ext' (by simp [Array.toList_set]))
  · next => exact absurd hu (by simp)

/-- **Writing the last-allocated slot rebuilds the same push.** Small, and
load-bearing: it is what keeps the worlds a generator loop passes through
UNIFORM (`h.push objₖ` at every round) instead of a growing tower of
`Array.set`s, and `stepIter` writes that slot twice per step. -/
theorem Heap.update_push_size (h : Heap) (o o' : Obj) :
    Heap.update (h.push o) h.size o' = some (h.push o') := by
  have hlt : h.size < (h.push o).size := by simp [Array.size_push]
  simp only [Heap.update, hlt, dif_pos]
  refine congrArg some (Array.ext' ?_)
  simp [Array.toList_set, Array.toList_push]

/-- **One decided step of the generator OBJECT at `a`** — the world-level
twin of `GenSteps`, in the same threshold form: from world `w`, stepping
the object either yields (`some v`) or reports exhaustion (`none`), leaving
`w'`. This is what every consumer of a generator consumes, one at a time
(`execForGen`, `drainIter`, `anyAllIter`, `next`), and the two heap-object
bridges above are its introduction rules. -/
def IterSteps (m : Module) (w : World) (a : Addr) (r : Option RVal)
    (w' : World) : Prop :=
  ∃ t, ∀ F ≥ t, stepIter m F w a = .ok w' r

namespace IterSteps

/-- Introduce an object step from one concrete run (any fuel). -/
theorem of_step {m : Module} {fuel : Nat} {w w' : World} {a : Addr}
    {r : Option RVal} (h : stepIter m fuel w a = .ok w' r) :
    IterSteps m w a r w' :=
  ⟨fuel, fun F hF => stepIter_mono h (by simp) F hF⟩

/-- **A yield of the object**, from a `GenSteps` fact about its stored
continuation: `stepIter_of_genSteps` read as this judgment (its conclusion
IS this judgment, unfolded). -/
theorem of_genSteps {m : Module} {w : World} {a : Addr} {qname : String}
    {locals : REnv} {cont cont' : GenCont} {status : GenStatus}
    {h₁ h₂ : Heap} {st₁ : FrameState} {v : RVal}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont status))
    (hstatus : status = .created ∨ status = .suspended)
    (hrun : Heap.update w.heap a (.generator qname locals cont .running) = some h₁)
    (hstep : GenSteps m ⟨{ w with heap := h₁ }, locals⟩ cont (some (v, cont')) st₁)
    (hback : Heap.update st₁.world.heap a
        (.generator qname st₁.locals cont' .suspended) = some h₂) :
    IterSteps m w a (some v) { st₁.world with heap := h₂ } :=
  stepIter_of_genSteps hobj hstatus hrun hstep hback

/-- **Exhaustion of the object**, likewise from `stepIter_of_genDone`. -/
theorem of_genDone {m : Module} {w : World} {a : Addr} {qname : String}
    {locals : REnv} {cont : GenCont} {status : GenStatus} {h₁ h₂ : Heap}
    {st₁ : FrameState}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont status))
    (hstatus : status = .created ∨ status = .suspended)
    (hrun : Heap.update w.heap a (.generator qname locals cont .running) = some h₁)
    (hstep : GenSteps m ⟨{ w with heap := h₁ }, locals⟩ cont Option.none st₁)
    (hback : Heap.update st₁.world.heap a
        (.generator qname st₁.locals [] .closed) = some h₂) :
    IterSteps m w a Option.none { st₁.world with heap := h₂ } :=
  stepIter_of_genDone hobj hstatus hrun hstep hback

/-- **One step of a generator object whose own resumption is heap-pure** —
the common case, and the one every consumer of `EvalsIn.genCall` meets: a
generator whose body touches only its own frame. Then `stepIter`'s two
writes (`.running` on entry, the resumption on exit) land on the same slot
and collapse (`Heap.update_update`), so the whole step is ONE observable
change of the object and the caller never has to name the intermediate
heap twice. `of_genSteps` is the general form, for a resumption that moves
the world. -/
theorem pureStep {m : Module} {w : World} {a : Addr} {qname : String}
    {locals locals' : REnv} {cont cont' : GenCont} {status : GenStatus}
    {h₁ h₂ : Heap} {v : RVal}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont status))
    (hstatus : status = .created ∨ status = .suspended)
    (hrun : Heap.update w.heap a (.generator qname locals cont .running) = some h₁)
    (hstep : GenSteps m ⟨{ w with heap := h₁ }, locals⟩ cont (some (v, cont'))
      ⟨{ w with heap := h₁ }, locals'⟩)
    (hback : Heap.update w.heap a
      (.generator qname locals' cont' .suspended) = some h₂) :
    IterSteps m w a (some v) { w with heap := h₂ } :=
  IterSteps.of_genSteps hobj hstatus hrun hstep (by
    show Heap.update h₁ a (.generator qname locals' cont' .suspended) = some h₂
    rw [Heap.update_update hrun]
    exact hback)

/-- `pureStep`'s exhaustion twin. -/
theorem pureDone {m : Module} {w : World} {a : Addr} {qname : String}
    {locals locals' : REnv} {cont : GenCont} {status : GenStatus} {h₁ h₂ : Heap}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont status))
    (hstatus : status = .created ∨ status = .suspended)
    (hrun : Heap.update w.heap a (.generator qname locals cont .running) = some h₁)
    (hstep : GenSteps m ⟨{ w with heap := h₁ }, locals⟩ cont Option.none
      ⟨{ w with heap := h₁ }, locals'⟩)
    (hback : Heap.update w.heap a (.generator qname locals' [] .closed) = some h₂) :
    IterSteps m w a Option.none { w with heap := h₂ } :=
  IterSteps.of_genDone hobj hstatus hrun hstep (by
    show Heap.update h₁ a (.generator qname locals' [] .closed) = some h₂
    rw [Heap.update_update hrun]
    exact hback)

/-- A CLOSED object answers exhaustion forever without running anything —
what makes a second `for` over a drained generator run zero times
(`gen_lab.drain_then_more`). -/
theorem closed {m : Module} {w : World} {a : Addr} {qname : String}
    {locals : REnv} {cont : GenCont}
    (hobj : Heap.get? w.heap a = some (.generator qname locals cont .closed)) :
    IterSteps m w a Option.none w :=
  ⟨1, fun F hF => by
    obtain ⟨F', rfl, _⟩ := succ_le_dest hF
    rw [stepIter]
    simp only [hobj]⟩

end IterSteps

/-- **Terminating EFFECTFUL expression evaluation**: `e` evaluates to `v`
and moves the state to `st'`. The stateful twin of `EvalsTo` (VC.lean),
which pins the out-state to the in-state, exactly as `CallsIn` is the
stateful twin of `CallsTo`.

Stated here rather than in VC.lean because a generator call is the first
expression in the tier whose evaluation is *not* pinned-state — it
allocates — and this file is where its consumer lives. -/
def EvalsIn (m : Module) (st : FrameState) (e : Expr) (v : RVal)
    (st' : FrameState) : Prop :=
  ∃ t, ∀ F ≥ t, evalExpr m F st e = .ok st' v

namespace EvalsIn

/-- Introduce from one concrete evaluation (any fuel). -/
theorem of_eval {m : Module} {fuel : Nat} {st st' : FrameState} {e : Expr}
    {v : RVal} (h : evalExpr m fuel st e = .ok st' v) : EvalsIn m st e v st' :=
  ⟨fuel, fun F hF => evalExpr_mono h (by simp) F hF⟩

/-- A pure evaluation is an effectful one that moved nothing. -/
theorem of_evalsTo {m : Module} {st : FrameState} {e : Expr} {v : RVal}
    (h : EvalsTo m st e v) : EvalsIn m st e v st := h.at_least

end EvalsIn

/-- **The heap object a generator CALL allocates** — `callIn`'s H4 creation
arm as a name, so the rules below can say it once: the arguments bound by
`mkCallEnv`, the whole body as the initial continuation, status `.created`.

That middle field is the hinge of this landing. `[.block f.body.toList]` is
literally the frame stack every `GenYields` theorem in this file is stated
over, so a spec for the BODY and a spec for the CALL compose with no glue. -/
def genObj (fname : String) (f : FunctionDefn) (args : Array RVal) : Obj :=
  .generator fname (mkCallEnv f.params args) [.block f.body.toList] .created

/-- **Calling a generator function runs no code**: it appends the suspended
frame to the heap and answers its address. `callIn`'s creation arm in
equational form (the guards are the interpreter's own, in its own order). -/
theorem callIn_genCall {m : Module} {fuel : Nat} {w : World} {fname : String}
    {f : FunctionDefn} {args : Array RVal}
    (hf : findFunction m fname = some f) (hargsOk : f.argsOk = true)
    (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params args.size = true) (hgen : f.isGenerator = true) :
    callIn m (fuel + 1) w fname args
      = .ok { w with heap := w.heap.push (genObj fname f args) } (.ref w.heap.size) := by
  rw [callIn]
  simp [hf, hargsOk, hlocalsOk, harity, hgen, genObj]

/-- **A generator call is a value with a specification** (the memo's
`EvalsTo.genCall`, §2.1). The call expression `f(e₁, …, eₖ)` evaluates to a
`.ref` at the heap's END, and the object there is `genObj` — whose stored
continuation is exactly what a `GenYields` fact about the body speaks
about, so the generator arrives as a heap value whose remaining output is
already known.

The guards are `evalExpr`'s own name-resolution order, hypothesis by
hypothesis; at a literal module every one of them closes by `rfl`. Note
there is no `heapFree` hypothesis and there could not be: a module with a
generator def is not heap-free, which is exactly why `EvalsTo.call` cannot
serve here. -/
theorem EvalsIn.genCall {m : Module} {st : FrameState} {fname : String}
    {f : FunctionDefn} {argEs : Array Expr} {vs : List RVal} {sp sp' : Span}
    (hlocal : Env.lookup st.locals fname = Option.none)
    (hglob : lookupG (moduleGlobals m).1 fname = Option.none)
    (hcls : findClass m fname = Option.none)
    (hnt : findNamedTuple m fname = Option.none)
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params vs.length = true) (hgen : f.isGenerator = true)
    (hargs : EvalsToList m st argEs.toList vs) :
    EvalsIn m st (.call (.name fname sp) argEs #[] Option.none sp')
      (.ref st.world.heap.size)
      ⟨{ st.world with heap := st.world.heap.push (genObj fname f vs.toArray) },
        st.locals⟩ := by
  obtain ⟨ta, ha⟩ := hargs.at_least
  refine ⟨ta + 2, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
  have hcall := callIn_genCall (m := m) (fuel := F'') (w := st.world) (fname := fname)
    (args := vs.toArray) hf hargsOk hlocalsOk (by simpa using harity) hgen
  rw [evalExpr]
  simp only [Array.isEmpty, Array.size_empty, hlocal, hglob, hcls, hnt, hf,
    ha (F'' + 1) (by omega), Run.ok_bind, Option.isSome_some, if_pos,
    Option.isSome_none, Bool.false_or, Bool.false_eq_true, if_neg,
    not_false_eq_true, hcall, Run.withLocals]
  rfl

/-! ### Binding the object to a name -/

/-- **`x = e` where evaluating `e` MOVES the state** —
`PyStmtTriple.assignName`'s stateful twin, over `EvalsIn` instead of
`EvalsTo`. It is what binds a generator to a name (`g = upto(n)`), the
statement `EvalsIn.genCall` cannot reach on its own: the pure rule stores
into `st.locals` at `st.world`, and an allocating RHS has already left that
world behind. Here the store lands in the world the CALL produced, which is
the only place the fresh object exists.

Not a special case of `PyStmtTriple.assign`: that rule's conclusion pins the
out-state's world to the in-state's, so no instance of it can bind an
allocation. The two rules stay side by side — the pure one is what every
heap-free assignment should keep using. -/
theorem PyStmtTriple.assignNameIn {m : Module} {P : FrameState → Prop}
    {Q : PyPost} {x : String} {e : Expr} {sp sp' : Span}
    (h : ∀ st, P st → ∃ v st₁, EvalsIn m st e v st₁ ∧
        Q.next ⟨st₁.world, Env.set st₁.locals x v⟩) :
    PyStmtTriple m P (.assign #[.name x sp] e sp') Q := by
  intro st hP
  obtain ⟨v, st₁, hv, hQ⟩ := h st hP
  obtain ⟨t, ht⟩ := hv
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt, ht F' hF', assignToH, assignTo] using hQ

/-- List-level singleton form of the effectful name-assignment rule. -/
theorem PyTriple.assignNameIn {m : Module} {P : FrameState → Prop}
    {Q : PyPost} {x : String} {e : Expr} {sp sp' : Span}
    (h : ∀ st, P st → ∃ v st₁, EvalsIn m st e v st₁ ∧
        Q.next ⟨st₁.world, Env.set st₁.locals x v⟩) :
    PyTriple m P [.assign #[.name x sp] e sp'] Q :=
  PyTriple.single (PyStmtTriple.assignNameIn h)

/-! ### The loop engine and the statement rule -/

/-- **The generator `for`'s engine**, at the `execForGen` level:
`execFor_of_invariant` (VC2.lean) with one `stepIter` in front of each
round. The invariant is indexed by the REMAINING elements exactly as there,
and the two obligations are the interpreter's two arms:

* `hexit` — at the empty remainder the object must report EXHAUSTION (the
  loop still takes a step to learn that), landing in `Q.next`;
* `hstep` — at `x :: rest` the object must yield `elt x` from the state
  this round begins in, and the body must re-establish `Inv rest`.

The per-round `IterSteps` obligation is deliberate: it is what makes the
rule sound without a heap-stability side condition, since the body's effect
on the object is re-observed rather than assumed away. `Inv [] = False` is
allowed and is how an infinite generator is consumed (file section header). -/
theorem execForGen_of_invariant {m : Module} {α : Type} {target : Expr}
    {body : List Stmt} {Q : PyPost} {a : Addr} (elt : α → RVal)
    (Inv : List α → FrameState → Prop)
    (hexit : ∀ st, Inv [] st →
      ∃ w', IterSteps m st.world a Option.none w' ∧ Q.next ⟨w', st.locals⟩)
    (hstep : ∀ x rest st, Inv (x :: rest) st →
      ∃ w' env₁, IterSteps m st.world a (some (elt x)) w' ∧
        assignToH w'.heap st.locals target (elt x) = .ok env₁ ∧
        PyTriple m (fun st' => st' = (⟨w', env₁⟩ : FrameState)) body
          { next := Inv rest
            ret := Q.ret
            brk := Q.next
            cont := Inv rest
            err := Q.err }) :
    ∀ as st, Inv as st →
      ∃ t, ∀ F ≥ t, Q.holds (execForGen m F st target a body) := by
  intro as
  induction as with
  | nil =>
    intro st hI
    obtain ⟨w', hit, hQ⟩ := hexit st hI
    obtain ⟨ts, hts⟩ := hit
    refine ⟨ts + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    rw [execForGen, hts F' hF']
    simp only [Run.withLocals, Run.ok_bind]
    exact hQ
  | cons x rest ih =>
    intro st hI
    obtain ⟨w', env₁, hit, hasg, hb⟩ := hstep x rest st hI
    obtain ⟨ts, hts⟩ := hit
    obtain ⟨r, tb, hr, hrun⟩ := hb.exec (st := (⟨w', env₁⟩ : FrameState)) rfl
    cases r with
    | ok st' flow =>
      cases flow with
      | next =>
        obtain ⟨tf, hf⟩ := ih st' hr
        have h0 := hf tf (Nat.le_refl tf)
        have hpin := execForGen_mono rfl (PyPost.holds_ne_timeout h0)
        refine ⟨ts + tb + tf + 1, fun F hF => ?_⟩
        obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
        rw [execForGen, hts F' (by omega)]
        simp only [Run.withLocals, Run.ok_bind, hasg, Run.liftRes]
        rw [hrun F' (by omega)]
        simp only [Run.ok_bind]
        rw [hpin F' (by omega)]
        exact h0
      | cont =>
        obtain ⟨tf, hf⟩ := ih st' hr
        have h0 := hf tf (Nat.le_refl tf)
        have hpin := execForGen_mono rfl (PyPost.holds_ne_timeout h0)
        refine ⟨ts + tb + tf + 1, fun F hF => ?_⟩
        obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
        rw [execForGen, hts F' (by omega)]
        simp only [Run.withLocals, Run.ok_bind, hasg, Run.liftRes]
        rw [hrun F' (by omega)]
        simp only [Run.ok_bind]
        rw [hpin F' (by omega)]
        exact h0
      | brk =>
        refine ⟨ts + tb + 1, fun F hF => ?_⟩
        obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
        rw [execForGen, hts F' (by omega)]
        simp only [Run.withLocals, Run.ok_bind, hasg, Run.liftRes]
        rw [hrun F' (by omega)]
        simpa using hr
      | ret v =>
        refine ⟨ts + tb + 1, fun F hF => ?_⟩
        obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
        rw [execForGen, hts F' (by omega)]
        simp only [Run.withLocals, Run.ok_bind, hasg, Run.liftRes]
        rw [hrun F' (by omega)]
        simpa using hr
    | exn st' e =>
      refine ⟨ts + tb + 1, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      rw [execForGen, hts F' (by omega)]
      simp only [Run.withLocals, Run.ok_bind, hasg, Run.liftRes]
      rw [hrun F' (by omega)]
      simpa using hr
    | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
    | unsupported msg => exact hr.elim

/-- **The generator `for` rule** in the triple vocabulary
(docs/generator-tier-architecture.md §2.2). Deliberately NOT an `IterVals`
constructor: nothing here claims a snapshot — the elements arrive one
`stepIter` at a time and the invariant re-observes the object every round —
so the exclusion note in VC2.lean's for-rule section stands untouched.

`hiter` is the effectful evaluation of the iterable (`EvalsIn`, since
`gen()` allocates) plus the fact that what it names is a generator object.
`hgenfree` is the interpreter's own guard: a generator object in a module
with no generator defs is a heap well-formedness violation and
`execForList` says so loudly rather than stepping, so the rule must know
the module has generator defs. It closes by `rfl` at a literal module. -/
theorem PyStmtTriple.forGen {m : Module} {α : Type} {target iter : Expr}
    {body : Array Stmt} {sp : Span} {P : FrameState → Prop} {Q : PyPost}
    {a : Addr} (elt : α → RVal) (Inv : List α → FrameState → Prop)
    (as : List α) (hgenfree : moduleGenFree m = false)
    (hiter : ∀ st, P st → ∃ st₁ qname locals cont status,
      EvalsIn m st iter (.ref a) st₁ ∧
        Heap.get? st₁.world.heap a = some (.generator qname locals cont status) ∧
        Inv as st₁)
    (hexit : ∀ st, Inv [] st →
      ∃ w', IterSteps m st.world a Option.none w' ∧ Q.next ⟨w', st.locals⟩)
    (hstep : ∀ x rest st, Inv (x :: rest) st →
      ∃ w' env₁, IterSteps m st.world a (some (elt x)) w' ∧
        assignToH w'.heap st.locals target (elt x) = .ok env₁ ∧
        PyTriple m (fun st' => st' = (⟨w', env₁⟩ : FrameState)) body.toList
          { next := Inv rest
            ret := Q.ret
            brk := Q.next
            cont := Inv rest
            err := Q.err }) :
    PyStmtTriple m P (.forStmt target iter body #[] sp) Q := by
  intro st hP
  obtain ⟨st₁, qname, locals, cont, status, hev, hobj, hI⟩ := hiter st hP
  obtain ⟨ti, hi⟩ := hev
  obtain ⟨t, ht⟩ := execForGen_of_invariant elt Inv hexit hstep as st₁ hI
  refine ⟨ti + t + 2, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
  rw [execStmt]
  simp only [hi (F'' + 1) (by omega), Run.ok_bind]
  rw [execForList]
  simp only [hobj, hgenfree, Bool.false_eq_true, if_neg, not_false_eq_true]
  exact ht F'' (by omega)

/-- List-level singleton form of the generator `for` rule; for a loop in
mid-list position feed `PyStmtTriple.forGen` to `PyTriple.seq` instead. -/
theorem PyTriple.forGen {m : Module} {α : Type} {target iter : Expr}
    {body : Array Stmt} {sp : Span} {P : FrameState → Prop} {Q : PyPost}
    {a : Addr} (elt : α → RVal) (Inv : List α → FrameState → Prop)
    (as : List α) (hgenfree : moduleGenFree m = false)
    (hiter : ∀ st, P st → ∃ st₁ qname locals cont status,
      EvalsIn m st iter (.ref a) st₁ ∧
        Heap.get? st₁.world.heap a = some (.generator qname locals cont status) ∧
        Inv as st₁)
    (hexit : ∀ st, Inv [] st →
      ∃ w', IterSteps m st.world a Option.none w' ∧ Q.next ⟨w', st.locals⟩)
    (hstep : ∀ x rest st, Inv (x :: rest) st →
      ∃ w' env₁, IterSteps m st.world a (some (elt x)) w' ∧
        assignToH w'.heap st.locals target (elt x) = .ok env₁ ∧
        PyTriple m (fun st' => st' = (⟨w', env₁⟩ : FrameState)) body.toList
          { next := Inv rest
            ret := Q.ret
            brk := Q.next
            cont := Inv rest
            err := Q.err }) :
    PyTriple m P [.forStmt target iter body #[] sp] Q :=
  PyTriple.single (PyStmtTriple.forGen elt Inv as hgenfree hiter hexit hstep)

/-! ## Smoke tests

Two ends of the calculus on hand-built frame stacks over an EMPTY module
(the rules never consult `m` unless a statement runs), so they exercise the
composition and nothing else. The real acceptance is
`Examples/python/gen_lab/proof.lean` — the first generator theorem in the
repo, over the ingested lab module. -/

namespace GenSmokeTest

private def m0 : Module := ⟨#[], #[], #[], #[]⟩
private def st0 : FrameState := ⟨⟨#[], [], [], []⟩, []⟩

/-- An `enumerate` over a two-element snapshot yields both pairs and stops
— `GenSteps` twice, then the exhausted stack. -/
example : GenYields m0 st0 [.enumSeq 0 [.int 7, .int 8]]
    [.tuple #[.int 0, .int 7], .tuple #[.int 1, .int 8]] st0 :=
  GenYields.cons genSteps_enumSeqCons
    (GenYields.cons genSteps_enumSeqCons
      (GenYields.silent genSilent_enumSeqNil genYields_nil))

/-- The same two values through the frame-POLYMORPHIC layer, spliced above
a second `enumerate` frame: `GenEmits.trans` is `List.append` on the frames
and on the output at once. -/
example : GenYields m0 st0
    [.enumSeq 0 [.int 7], .enumSeq 5 [.int 9]]
    [.tuple #[.int 0, .int 7], .tuple #[.int 5, .int 9]] st0 := by
  have one : ∀ (i : Int) (x : RVal),
      GenEmits m0 st0 [.enumSeq i [x]] [.tuple #[.int i, x]] st0 := by
    intro i x
    refine GenEmits.cons (pre₁ := [GenFrame.enumSeq (i + 1) []])
      (fun k => by simpa using genSteps_enumSeqCons) ?_
    exact GenEmits.silent (pre₁ := ([] : GenCont))
      (fun k => by simpa using genSilent_enumSeqNil) GenEmits.nil
  simpa using GenEmits.toYields (GenEmits.trans (one 0 (.int 7)) (one 5 (.int 9)))

/-- `count(5, 3)` hands over four values and is still suspended at 17. -/
example : GenYieldsPrefix m0 st0 [.countFrom 5 3]
    [.int 5, .int 8, .int 11, .int 14] st0 [.countFrom 17 3] :=
  genYieldsPrefix_countFrom 4 5 3

end GenSmokeTest

end LeanModels.Python
