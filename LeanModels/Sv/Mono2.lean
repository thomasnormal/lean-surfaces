import LeanModels.Sv.Spec2
import LeanModels.Sv.Pure2

/-!
# Fuel monotonicity and determinism of the Design2 interpreter (`LeanModels.Sv`)

The semantic tier's twin of `Obs.lean`'s fuel layer. `Sem2.lean`'s
interpreter threads ONE fuel parameter through expression evaluation,
statement execution, and the comb-settle pass counter; this file proves that
the parameter is a pure implementation detail of the executable semantics:

* **Adding fuel never changes a decided result.** Every interpreter function
  `F` is monotone in the flat approximation order `⊑` (`Res.le`, reused from
  `Obs.lean`): `F fuel ⊑ F fuel'` for `fuel ≤ fuel'`, i.e. the smaller run
  timed out or the two runs agree exactly (`.unsupported` messages
  included).
* **At fixed schedule σ a run is a function of the stimulus.** Two completed
  runs at any two fuels yield the same trace (`run2_det`), so the
  fuel-abstracted `Runs2` judgment (`Spec2.lean`) is functional
  (`Runs2.functional`), and `Deterministic2 d` — every legal schedule yields
  the same trace — is a meaningful property of a design.

## Design laws

* **One induction, one conjunction.** `fuelMono2` is a single induction on
  fuel over the whole of `Sem2`'s mutual block, in its declaration order:
  `evalExpr2`, `evalExprs2`, `resolveLhs2`, `resolveConcatLhs2`,
  `execStmt2`, `execCase2`, `execStmts2` (`writeConcatLhs2` is fuel-free and
  needs no conjunct). The glue is exactly `Obs.lean`'s: `Res.le_bind` /
  `Res.le_ite` congruences, `Res.le_refl` for fuel-free continuations, plus
  `Res.le_foldlM` for the `List.foldlM` walk of a concatenated target.
* **Same-fuel delegation is not induction.** `resolveLhs2` and
  `resolveConcatLhs2` do not match on fuel: they call `evalExpr2` at the SAME
  fuel (and the latter recurses structurally on the target). Their conjuncts
  are therefore derived at every level from the `evalExpr2` conjunct at that
  level (`resolveLhs2_le_of`, `resolveConcatLhs2_le_of` — the latter by
  well-founded recursion on the target's size), including fuel `0`, where
  `resolveLhs2 0 _ (.slice …)` is NOT a timeout.
* **The scheduler lifts compositionally.** `runCombProcess2`, `combPass2`,
  `runResetProcess2`, `resetPass2`, `runEdgeProcess2`, `edgePass2`,
  `cycleStep2`, `runFrom2`, `run2` consume fuel only through the mutual
  block, so their `_le` lemmas are congruence chains; `combSettle2` (the
  settle fixpoint loop, the scheduler-level fuel consumer) is its own small
  fuel induction, as in M0.
* **Fuel-free endpoint.** `evalExpr2_le_evalPure2`: every fueled evaluation
  approximates the fuel-free evaluator of `Pure2.lean` — the fuel-indexed
  chain converges to `evalPure2`, `.unsupported` outcomes included (this
  strengthens `evalPure2_of_evalExpr2_ok`, which covers `.ok` only).
* **Consumption forms.** Per-function `_mono` corollaries in implication form
  (`F fuel = r → r ≠ .timeout → ∀ fuel' ≥ fuel, F fuel' = r`), `_at_least`
  threshold forms (`∃ f₀, ∀ F, f₀ ≤ F → … = .ok p`, the shape spliced by
  `simp (disch := omega) only [h]`), and cross-fuel determinism `_det`
  lemmas for `combSettle2`, `cycleStep2`, and `run2`.

## What later layers consume

* `Runs2.functional` / `Deterministic2` — trace uniqueness at fixed σ and
  across schedules; `Terminates2.existsUnique` packages `Terminates2` with
  functionality (exactly one trace per schedule and stimulus).
* `cycleStep2_det` / `combSettle2_det` — two snapshot decompositions of the
  same cycle (e.g. two `Runs2.snapshot` witnesses with different fuels and
  the same counters) agree.
* `Runs2.at_least` — a completed run completes at every larger fuel, the
  fuel-uniformisation step when several runs must be read at one fuel.

The file ends with the two poles of `Deterministic2`:
`Deterministic2.of_processes_empty` (a process-free design's trace is
`holdTrace2`, whatever the schedule) and a two-process blocking race (the
Design2 twin of M0's `race_blk`) whose two schedules provably disagree, with
`#guard` rows pinning cross-fuel agreement and the timeout below it.
-/

namespace LeanModels.Sv

/-! ## Glue: `⊑` under `List.foldlM` -/

/-- Congruence of `⊑` under `List.foldlM`: if every step is `⊑`-related
pointwise (on list members), so is the whole fold. Used for the `foldlM`
walk of a concatenated assignment target (`resolveConcatLhs2`). -/
theorem Res.le_foldlM {α β : Type} {f g : β → α → Res β} :
    ∀ (l : List α) (init : β), (∀ b a, a ∈ l → f b a ⊑ g b a) →
      l.foldlM f init ⊑ l.foldlM g init
  | [], _, _ => Res.le_refl _
  | a :: as, init, h => by
      simp only [List.foldlM]
      exact Res.le_bind (h init a (List.mem_cons_self ..)) fun b =>
        Res.le_foldlM as b fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha')

/-! ## Same-fuel delegation: target resolution -/

/-- `resolveLhs2` at fuel `fuel` is `⊑` its run at `fuel'` whenever
`evalExpr2` is (it evaluates only a dynamic index, at the SAME fuel). -/
theorem resolveLhs2_le_of {fuel fuel' : Nat} {st : SvState}
    (hE : ∀ e, evalExpr2 fuel st e ⊑ evalExpr2 fuel' st e) (t : Lhs2) :
    resolveLhs2 fuel st t ⊑ resolveLhs2 fuel' st t := by
  cases t with
  | ident n => exact Res.le_refl _
  | slice n lo w => exact Res.le_refl _
  | index n idx elemW =>
    simp only [resolveLhs2]
    exact Res.le_bind (hE idx) fun _ => Res.le_refl _
  | concat parts => exact Res.le_refl _

/-- `resolveConcatLhs2` at fuel `fuel` is `⊑` its run at `fuel'` whenever
`resolveLhs2` is (it resolves each leaf through `resolveLhs2` at the SAME
fuel, recursing structurally through nested concatenations). -/
theorem resolveConcatLhs2_le_of {fuel fuel' : Nat} {st : SvState}
    (hR : ∀ t, resolveLhs2 fuel st t ⊑ resolveLhs2 fuel' st t) :
    ∀ t : Lhs2, resolveConcatLhs2 fuel st t ⊑ resolveConcatLhs2 fuel' st t
  | .concat parts => by
      rw [resolveConcatLhs2.eq_1, resolveConcatLhs2.eq_1]
      exact Res.le_foldlM parts [] fun acc part hmem =>
        Res.le_bind (resolveConcatLhs2_le_of hR part) fun _ => Res.le_refl _
  | .ident n => by
      simp only [resolveConcatLhs2]
      exact Res.le_bind (hR _) fun _ => Res.le_refl _
  | .slice n lo w => by
      simp only [resolveConcatLhs2]
      exact Res.le_bind (hR _) fun _ => Res.le_refl _
  | .index n idx elemW => by
      simp only [resolveConcatLhs2]
      exact Res.le_bind (hR _) fun _ => Res.le_refl _
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem hmem
  simp_wf
  omega

/-! ## Fuel monotonicity of the mutual block -/

/-- **Fuel monotonicity** of `Sem2`'s mutual block, one conjunction proved by
a single induction on fuel: for every interpreter function `F` and
`fuel ≤ fuel'`, `F fuel ⊑ F fuel'` — a run that decided keeps its exact
result at any higher fuel. Conjunct order is the mutual block's
declaration order: `evalExpr2`, `evalExprs2`, `resolveLhs2`,
`resolveConcatLhs2`, `execStmt2`, `execCase2`, `execStmts2`. Consume it
through the per-function `_le`/`_mono` corollaries below. -/
theorem fuelMono2 (fuel : Nat) :
    (∀ (st : SvState) (e : Expr2) (fuel' : Nat), fuel ≤ fuel' →
      evalExpr2 fuel st e ⊑ evalExpr2 fuel' st e) ∧
    (∀ (st : SvState) (es : List Expr2) (fuel' : Nat), fuel ≤ fuel' →
      evalExprs2 fuel st es ⊑ evalExprs2 fuel' st es) ∧
    (∀ (st : SvState) (t : Lhs2) (fuel' : Nat), fuel ≤ fuel' →
      resolveLhs2 fuel st t ⊑ resolveLhs2 fuel' st t) ∧
    (∀ (st : SvState) (t : Lhs2) (fuel' : Nat), fuel ≤ fuel' →
      resolveConcatLhs2 fuel st t ⊑ resolveConcatLhs2 fuel' st t) ∧
    (∀ (st : SvState) (nba : NbaQueue2) (s : Stmt2) (fuel' : Nat), fuel ≤ fuel' →
      execStmt2 fuel st nba s ⊑ execStmt2 fuel' st nba s) ∧
    (∀ (st : SvState) (nba : NbaQueue2) (subj : LVec) (items : List CaseItem2)
        (default? : Option Stmt2) (inside : Bool) (fuel' : Nat), fuel ≤ fuel' →
      execCase2 fuel st nba subj items default? inside ⊑
        execCase2 fuel' st nba subj items default? inside) ∧
    (∀ (st : SvState) (nba : NbaQueue2) (ss : List Stmt2) (fuel' : Nat), fuel ≤ fuel' →
      execStmts2 fuel st nba ss ⊑ execStmts2 fuel' st nba ss) := by
  induction fuel with
  | zero =>
    -- Fuel 0 is `.timeout` for every fuel-matching function (the bottom of
    -- `⊑`); the two same-fuel resolvers are derived from `evalExpr2`.
    have hE : ∀ (st : SvState) (e : Expr2) (fuel' : Nat), 0 ≤ fuel' →
        evalExpr2 0 st e ⊑ evalExpr2 fuel' st e :=
      fun st e fuel' _ => Or.inl (by simp [evalExpr2])
    have hR : ∀ (st : SvState) (t : Lhs2) (fuel' : Nat), 0 ≤ fuel' →
        resolveLhs2 0 st t ⊑ resolveLhs2 fuel' st t :=
      fun st t fuel' h => resolveLhs2_le_of (fun e => hE st e fuel' h) t
    refine ⟨hE, ?_, hR, ?_, ?_, ?_, ?_⟩
    · exact fun st es fuel' _ => Or.inl (by simp [evalExprs2])
    · exact fun st t fuel' h => resolveConcatLhs2_le_of (fun t => hR st t fuel' h) t
    · exact fun st nba s fuel' _ => Or.inl (by simp [execStmt2])
    · intro st nba subj items dflt inside fuel' _
      cases items with
      | nil => exact Or.inl (by simp [execCase2])
      | cons it rest => cases it; exact Or.inl (by simp [execCase2])
    · exact fun st nba ss fuel' _ => Or.inl (by simp [execStmts2])
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihR, ihCR, ihS, ihC, ihSs⟩ := ih
    -- evalExpr2: every child is evaluated at the decremented fuel, every
    -- continuation after the binds is fuel-free.
    have hE : ∀ (st : SvState) (e : Expr2) (fuel' : Nat), fuel + 1 ≤ fuel' →
        evalExpr2 (fuel + 1) st e ⊑ evalExpr2 fuel' st e := by
      intro st e fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases e <;> simp only [evalExpr2] <;>
          repeat (first
            | exact Res.le_refl _
            | refine Res.le_bind (ihE st _ k hk) fun _ => ?_
            | refine Res.le_bind (ihEs st _ k hk) fun _ => ?_)
    have hR : ∀ (st : SvState) (t : Lhs2) (fuel' : Nat), fuel + 1 ≤ fuel' →
        resolveLhs2 (fuel + 1) st t ⊑ resolveLhs2 fuel' st t :=
      fun st t fuel' h => resolveLhs2_le_of (fun e => hE st e fuel' h) t
    refine ⟨hE, ?_, hR, ?_, ?_, ?_, ?_⟩
    -- evalExprs2
    · intro st es fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases es with
        | nil => simp only [evalExprs2]; exact Res.le_refl _
        | cons e rest =>
          simp only [evalExprs2]
          exact Res.le_bind (ihE st e k hk) fun v =>
            Res.le_bind (ihEs st rest k hk) fun vs => Res.le_refl _
    -- resolveConcatLhs2
    · exact fun st t fuel' h => resolveConcatLhs2_le_of (fun t => hR st t fuel' h) t
    -- execStmt2
    · intro st nba s fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases s with
        | blockingAssign target value =>
          simp only [execStmt2]
          refine Res.le_bind (ihE st value k hk) fun v => ?_
          cases target with
          | concat parts =>
            exact Res.le_bind (ihCR st _ k hk) fun _ => Res.le_refl _
          | ident n => exact Res.le_bind (ihR st _ k hk) fun _ => Res.le_refl _
          | slice n lo w => exact Res.le_bind (ihR st _ k hk) fun _ => Res.le_refl _
          | index n idx elemW => exact Res.le_bind (ihR st _ k hk) fun _ => Res.le_refl _
        | nbaAssign target value =>
          simp only [execStmt2]
          exact Res.le_bind (ihE st value k hk) fun v =>
            Res.le_bind (ihR st target k hk) fun _ => Res.le_refl _
        | ifStmt cond thenB elseB =>
          simp only [execStmt2]
          refine Res.le_bind (ihE st cond k hk) fun c => ?_
          refine Res.le_ite (ihS st nba thenB k hk) ?_
          cases elseB with
          | some s => exact ihS st nba s k hk
          | none => exact Res.le_refl _
        | caseStmt subject items dflt inside check =>
          simp only [execStmt2]
          exact Res.le_bind (ihE st subject k hk) fun sv =>
            ihC st nba sv items.toList dflt inside k hk
        | block body =>
          simp only [execStmt2]
          exact ihSs st nba body.toList k hk
        | unsupported svKind text => simp only [execStmt2]; exact Res.le_refl _
    -- execCase2
    · intro st nba subj items dflt inside fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases items with
        | nil =>
          cases dflt with
          | some s => simp only [execCase2]; exact ihS st nba s k hk
          | none => simp only [execCase2]; exact Res.le_refl _
        | cons it rest =>
          obtain ⟨pats, body⟩ := it
          simp only [execCase2]
          exact Res.le_bind (ihEs st pats.toList k hk) fun pvs =>
            Res.le_ite (ihS st nba body k hk) (ihC st nba subj rest dflt inside k hk)
    -- execStmts2
    · intro st nba ss fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases ss with
        | nil => simp only [execStmts2]; exact Res.le_refl _
        | cons s rest =>
          simp only [execStmts2]
          refine Res.le_bind (ihS st nba s k hk) fun p => ?_
          obtain ⟨st', nba'⟩ := p
          exact ihSs st' nba' rest k hk

/-! ## Per-function `⊑` projections

`fuelMono2`'s conjuncts, one per function of the mutual block, in the
building-block form `F fuel ⊑ F fuel'` for `fuel ≤ fuel'`. The scheduler
chain below is assembled from them; the implication-form `_mono` and the
threshold-form `_at_least` corollaries further down are what proofs
consume. -/

/-- `⊑`-monotonicity of `evalExpr2` in the fuel (`fuelMono2`, conjunct 1). -/
theorem evalExpr2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState) (e : Expr2) :
    evalExpr2 fuel st e ⊑ evalExpr2 fuel' st e :=
  (fuelMono2 fuel).1 st e fuel' h

/-- `⊑`-monotonicity of `evalExprs2` in the fuel (conjunct 2). -/
theorem evalExprs2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (es : List Expr2) : evalExprs2 fuel st es ⊑ evalExprs2 fuel' st es :=
  (fuelMono2 fuel).2.1 st es fuel' h

/-- `⊑`-monotonicity of `resolveLhs2` in the fuel (conjunct 3). -/
theorem resolveLhs2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState) (t : Lhs2) :
    resolveLhs2 fuel st t ⊑ resolveLhs2 fuel' st t :=
  (fuelMono2 fuel).2.2.1 st t fuel' h

/-- `⊑`-monotonicity of `resolveConcatLhs2` in the fuel (conjunct 4). -/
theorem resolveConcatLhs2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (t : Lhs2) : resolveConcatLhs2 fuel st t ⊑ resolveConcatLhs2 fuel' st t :=
  (fuelMono2 fuel).2.2.2.1 st t fuel' h

/-- `⊑`-monotonicity of `execStmt2` in the fuel (conjunct 5). -/
theorem execStmt2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue2) (s : Stmt2) : execStmt2 fuel st nba s ⊑ execStmt2 fuel' st nba s :=
  (fuelMono2 fuel).2.2.2.2.1 st nba s fuel' h

/-- `⊑`-monotonicity of `execCase2` in the fuel (conjunct 6). -/
theorem execCase2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue2) (subj : LVec) (items : List CaseItem2) (default? : Option Stmt2)
    (inside : Bool) :
    execCase2 fuel st nba subj items default? inside ⊑
      execCase2 fuel' st nba subj items default? inside :=
  (fuelMono2 fuel).2.2.2.2.2.1 st nba subj items default? inside fuel' h

/-- `⊑`-monotonicity of `execStmts2` in the fuel (conjunct 7). -/
theorem execStmts2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue2) (ss : List Stmt2) :
    execStmts2 fuel st nba ss ⊑ execStmts2 fuel' st nba ss :=
  (fuelMono2 fuel).2.2.2.2.2.2 st nba ss fuel' h

/-! ## The fuel-free endpoint (`Pure2.lean`) -/

/-- Every fueled evaluation approximates the fuel-free evaluator: it timed
out, or it IS `evalPure2 st e` — `.ok` and `.unsupported` outcomes alike.
(The `.ok` half is `evalPure2_of_evalExpr2_ok`; this adds the loud half.) -/
theorem evalExpr2_le_evalPure2 (fuel : Nat) (st : SvState) (e : Expr2) :
    evalExpr2 fuel st e ⊑ evalPure2 st e := by
  have h := evalExpr2_le (Nat.le_add_right fuel (e.size + 1)) st e
  rwa [evalExpr2_eq_evalPure2 (fuel := fuel + (e.size + 1)) (by omega)] at h

/-- List twin of `evalExpr2_le_evalPure2` (the `concat` part walk). -/
theorem evalExprs2_le_evalPures2 (fuel : Nat) (st : SvState) (es : List Expr2) :
    evalExprs2 fuel st es ⊑ evalPures2 st es := by
  have h := evalExprs2_le (Nat.le_add_right fuel (Expr2.listSize es + 1)) st es
  rwa [evalExprs2_eq_evalPures2 (fuel := fuel + (Expr2.listSize es + 1)) (by omega)] at h

/-! ## The `⊑`-chain through the scheduler

The scheduler consumes fuel only through the mutual block and
`combSettle2`'s pass counter, so `⊑`-monotonicity lifts compositionally;
`combSettle2_le` is its own small fuel induction. -/

/-- `⊑`-monotonicity of one comb process run (assign or `always_comb`). -/
theorem runCombProcess2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (p : Process2) : runCombProcess2 fuel st p ⊑ runCombProcess2 fuel' st p := by
  cases p with
  | assign target value =>
    simp only [runCombProcess2]
    refine Res.le_bind (evalExpr2_le h st value) fun v => ?_
    cases target with
    | concat parts =>
      exact Res.le_bind (resolveConcatLhs2_le h st _) fun _ => Res.le_refl _
    | ident n => exact Res.le_bind (resolveLhs2_le h st _) fun _ => Res.le_refl _
    | slice n lo w => exact Res.le_bind (resolveLhs2_le h st _) fun _ => Res.le_refl _
    | index n idx elemW => exact Res.le_bind (resolveLhs2_le h st _) fun _ => Res.le_refl _
  | alwaysComb body =>
    simp only [runCombProcess2]
    exact Res.le_bind (execStmt2_le h st [] body) fun _ => Res.le_refl _
  | alwaysFF clock body => exact Res.le_refl _
  | alwaysPlain clock body => exact Res.le_refl _
  | alwaysFFR clock rstn body => exact Res.le_refl _
  | unsupported svKind text => exact Res.le_refl _

/-- `⊑`-monotonicity of one comb pass, by induction on the index list. -/
theorem combPass2_le (d : Design2) {fuel fuel' : Nat} (h : fuel ≤ fuel') :
    ∀ (is : List Nat) (st : SvState), combPass2 d fuel st is ⊑ combPass2 d fuel' st is := by
  intro is
  induction is with
  | nil => intro st; exact Res.le_refl _
  | cons i rest ih =>
    intro st
    simp only [combPass2]
    cases d.processes[i]? with
    | some p => exact Res.le_bind (runCombProcess2_le h st p) fun st' => ih st'
    | none => exact Res.le_bind (Res.le_refl _) fun st' => ih st'

/-- `combSettle2` is the scheduler-level fuel consumer (fuel bounds the pass
count), so its monotonicity is its own small induction on fuel. -/
theorem combSettle2_le (d : Design2) (σ : ScheduleOracle) :
    ∀ {fuel fuel' : Nat}, fuel ≤ fuel' → ∀ (st : SvState) (k : Nat),
      combSettle2 d σ fuel st k ⊑ combSettle2 d σ fuel' st k := by
  intro fuel
  induction fuel with
  | zero => intro fuel' h st k; exact Or.inl (by simp [combSettle2])
  | succ f ih =>
    intro fuel' h st k
    cases fuel' with
    | zero => exact absurd h (Nat.not_succ_le_zero f)
    | succ f' =>
      have hf : f ≤ f' := Nat.le_of_succ_le_succ h
      simp only [combSettle2]
      refine Res.le_bind (combPass2_le d hf _ st) fun st' => ?_
      exact Res.le_ite (Res.le_refl _) (ih hf st' (k + 1))

/-- `⊑`-monotonicity of one async-reset process run. -/
theorem runResetProcess2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue2) (p : Process2) :
    runResetProcess2 fuel st nba p ⊑ runResetProcess2 fuel' st nba p := by
  cases p with
  | alwaysFFR clock rstn body => exact execStmt2_le h st nba body
  | alwaysFF clock body => exact Res.le_refl _
  | alwaysPlain clock body => exact Res.le_refl _
  | alwaysComb body => exact Res.le_refl _
  | assign target value => exact Res.le_refl _
  | unsupported svKind text => exact Res.le_refl _

/-- `⊑`-monotonicity of the reset-event pass, by induction on the index list. -/
theorem resetPass2_le (d : Design2) {fuel fuel' : Nat} (h : fuel ≤ fuel') :
    ∀ (is : List Nat) (st : SvState) (nba : NbaQueue2),
      resetPass2 d fuel st nba is ⊑ resetPass2 d fuel' st nba is := by
  intro is
  induction is with
  | nil => intro st nba; exact Res.le_refl _
  | cons i rest ih =>
    intro st nba
    simp only [resetPass2]
    cases d.processes[i]? with
    | some p => exact Res.le_bind (runResetProcess2_le h st nba p) fun q => ih q.1 q.2
    | none => exact Res.le_bind (Res.le_refl _) fun q => ih q.1 q.2

/-- `⊑`-monotonicity of one edge-triggered process run. -/
theorem runEdgeProcess2_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue2) (p : Process2) :
    runEdgeProcess2 fuel st nba p ⊑ runEdgeProcess2 fuel' st nba p := by
  cases p with
  | alwaysFF clock body => exact execStmt2_le h st nba body
  | alwaysPlain clock body => exact execStmt2_le h st nba body
  | alwaysFFR clock rstn body => exact execStmt2_le h st nba body
  | alwaysComb body => exact Res.le_refl _
  | assign target value => exact Res.le_refl _
  | unsupported svKind text => exact Res.le_refl _

/-- `⊑`-monotonicity of the edge pass, by induction on the index list. -/
theorem edgePass2_le (d : Design2) {fuel fuel' : Nat} (h : fuel ≤ fuel') :
    ∀ (is : List Nat) (st : SvState) (nba : NbaQueue2),
      edgePass2 d fuel st nba is ⊑ edgePass2 d fuel' st nba is := by
  intro is
  induction is with
  | nil => intro st nba; exact Res.le_refl _
  | cons i rest ih =>
    intro st nba
    simp only [edgePass2]
    cases d.processes[i]? with
    | some p => exact Res.le_bind (runEdgeProcess2_le h st nba p) fun q => ih q.1 q.2
    | none => exact Res.le_bind (Res.le_refl _) fun q => ih q.1 q.2

/-- `cycleStep2`'s do-block compiles the reset-phase `match` as a join
point: the edge phase and final settle are duplicated into both arms, so the
proof splits on the reset ready list and runs one congruence chain per arm. -/
theorem cycleStep2_le (d : Design2) (σ : ScheduleOracle) {fuel fuel' : Nat}
    (h : fuel ≤ fuel') (inputs st : SvState) (k : Nat) :
    cycleStep2 d σ fuel inputs st k ⊑ cycleStep2 d σ fuel' inputs st k := by
  simp only [cycleStep2]
  refine Res.le_bind (combSettle2_le d σ h _ _) fun p => ?_
  obtain ⟨st1, k1⟩ := p
  dsimp only
  cases d.resetIndices st st1 with
  | nil =>
    refine Res.le_bind (Res.le_refl _) fun q => ?_
    refine Res.le_bind (edgePass2_le d h _ _ _) fun r => ?_
    exact combSettle2_le d σ h _ _
  | cons i is =>
    refine Res.le_bind (resetPass2_le d h _ _ _) fun r => ?_
    refine Res.le_bind (combSettle2_le d σ h _ _) fun q => ?_
    refine Res.le_bind (edgePass2_le d h _ _ _) fun r => ?_
    exact combSettle2_le d σ h _ _

/-- `⊑`-monotonicity of a run from a state, by induction on the stimulus. -/
theorem runFrom2_le (d : Design2) (σ : ScheduleOracle) {fuel fuel' : Nat}
    (h : fuel ≤ fuel') :
    ∀ (stim : List SvState) (st : SvState) (k : Nat),
      runFrom2 d σ fuel st k stim ⊑ runFrom2 d σ fuel' st k stim := by
  intro stim
  induction stim with
  | nil => intro st k; exact Res.le_refl _
  | cons inputs rest ih =>
    intro st k
    simp only [runFrom2]
    refine Res.le_bind (cycleStep2_le d σ h inputs st k) fun p => ?_
    obtain ⟨st', k'⟩ := p
    exact Res.le_bind (ih st' k') fun tr => Res.le_refl _

/-- `⊑`-monotonicity of `run2` (`runFrom2_le` from the startup state). -/
theorem run2_le (d : Design2) (σ : ScheduleOracle) {fuel fuel' : Nat}
    (h : fuel ≤ fuel') (stim : List SvState) :
    run2 d σ fuel stim ⊑ run2 d σ fuel' stim :=
  runFrom2_le d σ h stim (initState2 d) 0

/-! ## Per-function corollaries (implication and threshold forms) -/

private theorem mono_of_le {α : Type} {x y r : Res α}
    (hle : x ⊑ y) (h : x = r) (hr : r ≠ .timeout) : y = r := by
  subst h; exact (Res.le_eq hle hr).symm

/-- Fuel monotonicity for `evalExpr2`: a decided result survives any fuel
increase, exactly. -/
theorem evalExpr2_mono {fuel : Nat} {st : SvState} {e : Expr2} {r : Res LVec}
    (h : evalExpr2 fuel st e = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExpr2 fuel' st e = r := fun _ hf =>
  mono_of_le (evalExpr2_le hf st e) h hr

/-- Fuel monotonicity for `evalExprs2`. -/
theorem evalExprs2_mono {fuel : Nat} {st : SvState} {es : List Expr2}
    {r : Res (List LVec)} (h : evalExprs2 fuel st es = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExprs2 fuel' st es = r := fun _ hf =>
  mono_of_le (evalExprs2_le hf st es) h hr

/-- Fuel monotonicity for `resolveLhs2`. -/
theorem resolveLhs2_mono {fuel : Nat} {st : SvState} {t : Lhs2}
    {r : Res (String × Option (Nat × Nat))} (h : resolveLhs2 fuel st t = r)
    (hr : r ≠ .timeout) : ∀ fuel' ≥ fuel, resolveLhs2 fuel' st t = r := fun _ hf =>
  mono_of_le (resolveLhs2_le hf st t) h hr

/-- Fuel monotonicity for `resolveConcatLhs2`. -/
theorem resolveConcatLhs2_mono {fuel : Nat} {st : SvState} {t : Lhs2}
    {r : Res (List (String × Nat × Nat))} (h : resolveConcatLhs2 fuel st t = r)
    (hr : r ≠ .timeout) : ∀ fuel' ≥ fuel, resolveConcatLhs2 fuel' st t = r :=
  fun _ hf => mono_of_le (resolveConcatLhs2_le hf st t) h hr

/-- Fuel monotonicity for `execStmt2`. -/
theorem execStmt2_mono {fuel : Nat} {st : SvState} {nba : NbaQueue2} {s : Stmt2}
    {r : Res (SvState × NbaQueue2)} (h : execStmt2 fuel st nba s = r)
    (hr : r ≠ .timeout) : ∀ fuel' ≥ fuel, execStmt2 fuel' st nba s = r :=
  fun _ hf => mono_of_le (execStmt2_le hf st nba s) h hr

/-- Fuel monotonicity for `execCase2`. -/
theorem execCase2_mono {fuel : Nat} {st : SvState} {nba : NbaQueue2} {subj : LVec}
    {items : List CaseItem2} {default? : Option Stmt2} {inside : Bool}
    {r : Res (SvState × NbaQueue2)}
    (h : execCase2 fuel st nba subj items default? inside = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execCase2 fuel' st nba subj items default? inside = r :=
  fun _ hf => mono_of_le (execCase2_le hf st nba subj items default? inside) h hr

/-- Fuel monotonicity for `execStmts2`. -/
theorem execStmts2_mono {fuel : Nat} {st : SvState} {nba : NbaQueue2}
    {ss : List Stmt2} {r : Res (SvState × NbaQueue2)}
    (h : execStmts2 fuel st nba ss = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execStmts2 fuel' st nba ss = r := fun _ hf =>
  mono_of_le (execStmts2_le hf st nba ss) h hr

/-- Fuel monotonicity for `runCombProcess2`. -/
theorem runCombProcess2_mono {fuel : Nat} {st : SvState} {p : Process2}
    {r : Res SvState} (h : runCombProcess2 fuel st p = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, runCombProcess2 fuel' st p = r := fun _ hf =>
  mono_of_le (runCombProcess2_le hf st p) h hr

/-- Fuel monotonicity for `combPass2` (one settle pass). -/
theorem combPass2_mono {d : Design2} {fuel : Nat} {st : SvState} {is : List Nat}
    {r : Res SvState} (h : combPass2 d fuel st is = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, combPass2 d fuel' st is = r := fun _ hf =>
  mono_of_le (combPass2_le d hf is st) h hr

/-- Fuel monotonicity for `combSettle2`: a settled state (and pass counter)
survives any fuel increase. -/
theorem combSettle2_mono {d : Design2} {σ : ScheduleOracle} {fuel : Nat}
    {st : SvState} {k : Nat} {r : Res (SvState × Nat)}
    (h : combSettle2 d σ fuel st k = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, combSettle2 d σ fuel' st k = r := fun _ hf =>
  mono_of_le (combSettle2_le d σ hf st k) h hr

/-- Fuel monotonicity for `resetPass2`. -/
theorem resetPass2_mono {d : Design2} {fuel : Nat} {st : SvState} {nba : NbaQueue2}
    {is : List Nat} {r : Res (SvState × NbaQueue2)}
    (h : resetPass2 d fuel st nba is = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, resetPass2 d fuel' st nba is = r := fun _ hf =>
  mono_of_le (resetPass2_le d hf is st nba) h hr

/-- Fuel monotonicity for `edgePass2`. -/
theorem edgePass2_mono {d : Design2} {fuel : Nat} {st : SvState} {nba : NbaQueue2}
    {is : List Nat} {r : Res (SvState × NbaQueue2)}
    (h : edgePass2 d fuel st nba is = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, edgePass2 d fuel' st nba is = r := fun _ hf =>
  mono_of_le (edgePass2_le d hf is st nba) h hr

/-- Fuel monotonicity for `cycleStep2`. -/
theorem cycleStep2_mono {d : Design2} {σ : ScheduleOracle} {fuel : Nat}
    {inputs st : SvState} {k : Nat} {r : Res (SvState × Nat)}
    (h : cycleStep2 d σ fuel inputs st k = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, cycleStep2 d σ fuel' inputs st k = r := fun _ hf =>
  mono_of_le (cycleStep2_le d σ hf inputs st k) h hr

/-- Fuel monotonicity for `runFrom2`. -/
theorem runFrom2_mono {d : Design2} {σ : ScheduleOracle} {fuel : Nat}
    {st : SvState} {k : Nat} {stim : List SvState} {r : Res (List SvState)}
    (h : runFrom2 d σ fuel st k stim = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, runFrom2 d σ fuel' st k stim = r := fun _ hf =>
  mono_of_le (runFrom2_le d σ hf stim st k) h hr

/-- **Fuel monotonicity for `run2`**: a decided trace (`ok` or
`unsupported`) is the same at every larger fuel. -/
theorem run2_mono {d : Design2} {σ : ScheduleOracle} {fuel : Nat}
    {stim : List SvState} {r : Res (List SvState)}
    (h : run2 d σ fuel stim = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, run2 d σ fuel' stim = r := fun _ hf =>
  mono_of_le (run2_le d σ hf stim) h hr

/-- Threshold form of a completed `combSettle2` (comb settle is the fixpoint
recursion a symbolic execution keeps frozen). -/
theorem combSettle2_at_least {d : Design2} {σ : ScheduleOracle} {st : SvState}
    {k : Nat} {p : SvState × Nat}
    (h : ∃ fuel, combSettle2 d σ fuel st k = .ok p) :
    ∃ f₀, ∀ F, f₀ ≤ F → combSettle2 d σ F st k = .ok p := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => combSettle2_mono hf (by simp) F hF⟩

/-- Threshold form of a completed `cycleStep2`: succeed once, succeed at
every sufficiently large fuel — a conditional rewrite rule for
`simp (disch := omega) only [h]`. -/
theorem cycleStep2_at_least {d : Design2} {σ : ScheduleOracle} {inputs st : SvState}
    {k : Nat} {p : SvState × Nat}
    (h : ∃ fuel, cycleStep2 d σ fuel inputs st k = .ok p) :
    ∃ f₀, ∀ F, f₀ ≤ F → cycleStep2 d σ F inputs st k = .ok p := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => cycleStep2_mono hf (by simp) F hF⟩

/-- Threshold form of a completed `run2`. -/
theorem run2_at_least {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : ∃ fuel, run2 d σ fuel stim = .ok tr) :
    ∃ f₀, ∀ F, f₀ ≤ F → run2 d σ F stim = .ok tr := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => run2_mono hf (by simp) F hF⟩

/-! ## Cross-fuel determinism at fixed σ -/

/-- Generic cross-fuel agreement: two decided results of a `⊑`-monotone
fuel-indexed computation agree, whatever the two fuels. -/
private theorem res_det_of_le {α : Type} {F : Nat → Res α}
    (hle : ∀ {f f' : Nat}, f ≤ f' → F f ⊑ F f') {fuel₁ fuel₂ : Nat} {r₁ r₂ : Res α}
    (h₁ : F fuel₁ = r₁) (h₂ : F fuel₂ = r₂)
    (hr₁ : r₁ ≠ .timeout) (hr₂ : r₂ ≠ .timeout) : r₁ = r₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hf | hf
  · exact (mono_of_le (hle hf) h₁ hr₁).symm.trans h₂
  · exact h₁.symm.trans (mono_of_le (hle hf) h₂ hr₂)

/-- Two successful settles of the same state at the same counter, at any two
fuels, agree (settled state AND final counter). -/
theorem combSettle2_det {d : Design2} {σ : ScheduleOracle} {st : SvState} {k : Nat}
    {fuel₁ fuel₂ : Nat} {p₁ p₂ : SvState × Nat}
    (h₁ : combSettle2 d σ fuel₁ st k = .ok p₁)
    (h₂ : combSettle2 d σ fuel₂ st k = .ok p₂) : p₁ = p₂ :=
  Res.ok.inj (res_det_of_le (F := fun f => combSettle2 d σ f st k)
    (fun hf => combSettle2_le d σ hf st k) h₁ h₂ (by simp) (by simp))

/-- Two successful `cycleStep2`s from the same state, inputs, and counter, at
any two fuels, agree (snapshot AND next counter). -/
theorem cycleStep2_det {d : Design2} {σ : ScheduleOracle} {inputs st : SvState}
    {k : Nat} {fuel₁ fuel₂ : Nat} {p₁ p₂ : SvState × Nat}
    (h₁ : cycleStep2 d σ fuel₁ inputs st k = .ok p₁)
    (h₂ : cycleStep2 d σ fuel₂ inputs st k = .ok p₂) : p₁ = p₂ :=
  Res.ok.inj (res_det_of_le (F := fun f => cycleStep2 d σ f inputs st k)
    (fun hf => cycleStep2_le d σ hf inputs st k) h₁ h₂ (by simp) (by simp))

/-- Any two decided (non-`timeout`) results of the same run, at *any* two
fuels, are equal — `.unsupported` messages included. -/
theorem run2_res_det {d : Design2} {σ : ScheduleOracle} {stim : List SvState}
    {fuel₁ fuel₂ : Nat} {r₁ r₂ : Res (List SvState)}
    (h₁ : run2 d σ fuel₁ stim = r₁) (h₂ : run2 d σ fuel₂ stim = r₂)
    (hr₁ : r₁ ≠ .timeout) (hr₂ : r₂ ≠ .timeout) : r₁ = r₂ :=
  res_det_of_le (F := fun f => run2 d σ f stim) (fun hf => run2_le d σ hf stim)
    h₁ h₂ hr₁ hr₂

/-- **Cross-fuel determinism**: two successful traces of the same design,
stimulus, and schedule are equal, whatever the fuels. -/
theorem run2_det {d : Design2} {σ : ScheduleOracle} {stim : List SvState}
    {fuel₁ fuel₂ : Nat} {tr₁ tr₂ : List SvState}
    (h₁ : run2 d σ fuel₁ stim = .ok tr₁) (h₂ : run2 d σ fuel₂ stim = .ok tr₂) :
    tr₁ = tr₂ :=
  Res.ok.inj (run2_res_det h₁ h₂ (by simp) (by simp))

/-- A completed run cannot also be loud: if some fuel yields a trace, no fuel
yields `.unsupported`. -/
theorem run2_ok_unsupported {d : Design2} {σ : ScheduleOracle} {stim : List SvState}
    {fuel₁ fuel₂ : Nat} {tr : List SvState} {msg : String}
    (h₁ : run2 d σ fuel₁ stim = .ok tr) (h₂ : run2 d σ fuel₂ stim = .unsupported msg) :
    False := by
  have := run2_res_det h₁ h₂ (by simp) (by simp)
  simp at this

/-! ## The run judgment is functional -/

/-- `Runs2` is functional: at fixed σ the trace is unique across all fuels. -/
theorem Runs2.functional {d : Design2} {σ : ScheduleOracle} {stim tr₁ tr₂ : List SvState}
    (h₁ : Runs2 d σ stim tr₁) (h₂ : Runs2 d σ stim tr₂) : tr₁ = tr₂ := by
  obtain ⟨fuel₁, hf₁⟩ := h₁
  obtain ⟨fuel₂, hf₂⟩ := h₂
  exact run2_det hf₁ hf₂

/-- Threshold form of `Runs2` (the `CallsTo.at_least` analog): a completed
run completes, with the same trace, at every sufficiently large fuel. -/
theorem Runs2.at_least {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) : ∃ f₀, ∀ F, f₀ ≤ F → run2 d σ F stim = .ok tr :=
  run2_at_least h

/-- With `Terminates2`, every schedule and stimulus has EXACTLY one trace:
termination gives existence, `Runs2.functional` uniqueness. -/
theorem Terminates2.existsUnique {d : Design2} (ht : Terminates2 d)
    (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 d σ stim tr ∧ ∀ tr', Runs2 d σ stim tr' → tr' = tr := by
  obtain ⟨tr, hr⟩ := ht σ stim
  exact ⟨tr, hr, fun tr' hr' => Runs2.functional hr' hr⟩

/-- All legal schedules yield the same trace — `Obs.lean`'s `Deterministic`
at the semantic tier. (Cross-FUEL uniqueness at one schedule is
`Runs2.functional` and holds for every design; this is the cross-SCHEDULE
statement, a property of the design: race-free designs have it, a blocking
race refutes it.) -/
def Deterministic2 (d : Design2) : Prop :=
  ∀ (σ₁ σ₂ : ScheduleOracle) (stim tr₁ tr₂ : List SvState),
    Runs2 d σ₁ stim tr₁ → Runs2 d σ₂ stim tr₂ → tr₁ = tr₂

/-- A deterministic design's trace may be read off any one schedule: if `P`
holds of the trace under some schedule, it holds under every schedule. -/
theorem Deterministic2.transfer {d : Design2} (hd : Deterministic2 d)
    {σ₁ σ₂ : ScheduleOracle} {stim tr₁ tr₂ : List SvState}
    (h₁ : Runs2 d σ₁ stim tr₁) (h₂ : Runs2 d σ₂ stim tr₂)
    {P : List SvState → Prop} (hP : P tr₁) : P tr₂ :=
  hd σ₁ σ₂ stim tr₁ tr₂ h₁ h₂ ▸ hP

/-! ## `Deterministic2` holds of process-free designs

The smallest positive instance (it pairs with `Spec2.lean`'s process-free
`Terminates2` example): with no processes, comb settle is one no-op pass,
no reset or edge process ever fires, and each snapshot is the previous
state with the stimulus applied — whatever the schedule. -/

/-- The trace of a process-free design: each snapshot is the previous state
with the cycle's inputs applied. -/
def holdTrace2 (d : Design2) : SvState → List SvState → List SvState
  | _, [] => []
  | st, inputs :: rest =>
      applyInputs2 d inputs st :: holdTrace2 d (applyInputs2 d inputs st) rest

/-- With no processes, every successful cycle only applies the inputs. -/
theorem cycleStep2_of_processes_empty {d : Design2} (hd : d.processes = #[])
    {σ : ScheduleOracle} {fuel : Nat} {inputs st st' : SvState} {k k' : Nat}
    (h : cycleStep2 d σ fuel inputs st k = .ok (st', k')) :
    st' = applyInputs2 d inputs st := by
  have hc : d.combIndices = [] := by simp [Design2.combIndices, hd]
  have he : d.edgeIndices = [] := by simp [Design2.edgeIndices, hd]
  have hr : ∀ a b, d.resetIndices a b = [] := by
    intro a b; simp [Design2.resetIndices, hd]
  cases fuel with
  | zero => simp [cycleStep2, combSettle2] at h
  | succ f =>
    simp [cycleStep2, combSettle2, combPass2, hc, he, hr, σ.choose_nil, edgePass2,
      commitNba2] at h
    exact h.1.symm

/-- With no processes, every completed run is `holdTrace2`. -/
theorem runFrom2_of_processes_empty {d : Design2} (hd : d.processes = #[])
    {σ : ScheduleOracle} {fuel : Nat} :
    ∀ {stim : List SvState} {st : SvState} {k : Nat} {tr : List SvState},
      runFrom2 d σ fuel st k stim = .ok tr → tr = holdTrace2 d st stim
  | [], st, k, tr, h => by simpa [holdTrace2, eq_comm] using h
  | inputs :: rest, st, k, tr, h => by
      obtain ⟨st', k', tr', h1, h2, rfl⟩ := runFrom2_cons_eq_ok.mp h
      have := cycleStep2_of_processes_empty hd h1
      subst this
      simp [holdTrace2, runFrom2_of_processes_empty hd h2]

/-- A design with no processes is schedule-deterministic. -/
theorem Deterministic2.of_processes_empty {d : Design2} (hd : d.processes = #[]) :
    Deterministic2 d := by
  rintro σ₁ σ₂ stim tr₁ tr₂ ⟨f₁, h₁⟩ ⟨f₂, h₂⟩
  rw [runFrom2_of_processes_empty hd h₁, runFrom2_of_processes_empty hd h₂]

/-! ## Examples: a blocking race refutes `Deterministic2`

Two `always_ff` processes blocking-assign `0` and `1` to the same `x` on
the same edge — the Design2 twin of M0's `race_blk`. Source order leaves
`1`, the reversed schedule leaves `0`; fuel never matters (the `#guard`
rows check one decided run at two fuels and the timeout below them). -/

/-- `always_ff @(posedge clk) x = 0;  always_ff @(posedge clk) x = 1;` -/
private def raceD : Design2 :=
  { name := "race"
    decls := #[{ name := "clk", width := 1, isInput := true }, { name := "x", width := 1 }]
    processes := #[
      .alwaysFF "clk" (.blockingAssign (.ident "x") (.lit (LVec.lit "0"))),
      .alwaysFF "clk" (.blockingAssign (.ident "x") (.lit (LVec.lit "1")))] }

-- Cross-fuel agreement of decided runs (`run2_det` in action) …
#guard run2 raceD σ_src 8 [[], []] == run2 raceD σ_src 64 [[], []]
#guard run2 raceD σ_rev 8 [[], []] == run2 raceD σ_rev 64 [[], []]
-- … above the timeout at fuel 1 (the bottom of `⊑`). The settle is NOT the
-- cause: `raceD` has no comb process, so `combSettle2` at fuel 1 runs one
-- empty pass and returns `.ok`. The edge phase times out: `execStmt2 1`
-- evaluates the right-hand side of `x = 0` with `evalExpr2 0`.
#guard run2 raceD σ_src 1 [[]] == .timeout
-- The two schedules disagree on `x`.
#guard (Res.toOption (run2 raceD σ_src 8 [[]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "x") == some ["1"]
#guard (Res.toOption (run2 raceD σ_rev 8 [[]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "x") == some ["0"]

-- `Runs2.functional` pins the trace from one kernel-checked run.
example (tr : List SvState) (h : Runs2 raceD σ_src [[]] tr) :
    tr = [[("clk", LVec.xVec 1), ("x", LVec.lit "1")]] :=
  Runs2.functional h ⟨8, by decide +kernel⟩

/-- The race is schedule-dependent: `raceD` is NOT `Deterministic2`. -/
private theorem raceD_not_deterministic : ¬ Deterministic2 raceD := fun h =>
  absurd (h σ_src σ_rev [[]] [[("clk", LVec.xVec 1), ("x", LVec.lit "1")]]
      [[("clk", LVec.xVec 1), ("x", LVec.lit "0")]]
      ⟨8, by decide +kernel⟩ ⟨8, by decide +kernel⟩)
    (by decide)

-- The positive instance, on a concrete process-free design.
example : Deterministic2 { name := "hold", decls := #[], processes := #[] } :=
  Deterministic2.of_processes_empty rfl

end LeanModels.Sv
