import LeanModels.Sv.Seq2Cycle
import LeanModels.Sv.SeqFamily

/-!
# The FF-only profile, decided, and the schedule class (`LeanModels.Sv`, PLAN4 Gate 1)

**Status: a `run2` library module** (provisional over `run2`; never trusted). Imported by no
existing module.

* `WellFormedClockStep d order`: the edge processes run in `order`, each exactly once (a permutation
  of `d.edgeIndices`). With NBA-only bodies every right-hand side reads the same pre-state and the
  queue is committed once (`cycleStep2`'s structure, `edgePass2_ffOnly`). `run2`'s schedules are
  exactly this class (`wellFormed_choose`, from `ScheduleOracle.choose_perm`). `clockStep_wellFormed`:
  every well-formed order gives the index-order step. `omitted_process`: an order that omits a
  process is not well formed, and the step it gives differs (no conclusion without the class).
* `Design2.ffOnlyProfileB`, decidable: every process an `always_ff` on one clock, NBA-only bodies with
  static targets (`Lhs2.window?`), no process writing an input, distinct processes writing
  pairwise-disjoint windows. Synchronous reset is an ordinary `if` in the body; `alwaysFFR` is out.
* Soundness: `FFOnly.ofProfile`, and `ffUpd_disj`: the updates of distinct processes are disjoint on
  every state (an update stays inside a window its body names: `upd_covered`). So
  `cycleStep2_profile` is `cycleStep2_ffOnly` with only the run hypothesis left.
-/

namespace LeanModels.Sv

set_option autoImplicit false

/-! ## The schedule class -/

/-- **A well-formed clock step**: the edge processes run in `order`, each exactly once. -/
def WellFormedClockStep (d : Design2) (order : List Nat) : Prop := order.Perm d.edgeIndices

theorem wellFormed_choose (d : Design2) (σ : ScheduleOracle) (k : Nat) :
    WellFormedClockStep d (σ.choose k d.edgeIndices) := σ.choose_perm k _

/-- The clock step along `order`: the listed processes' updates on `pre`, committed in that order. -/
def clockStep (d : Design2) (fuel : Nat) (pre : SvState) (order : List Nat) : SvState :=
  commitNba2 pre (order.flatMap (d.ffUpd fuel pre))

theorem clockStep_wellFormed {d : Design2} {fuel : Nat} {pre : SvState} {order : List Nat}
    (hwf : WellFormedClockStep d order)
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ d.ffUpd fuel pre i, ∀ u' ∈ d.ffUpd fuel pre j, NbaDisj u u')
    (hnd : (pre.map Prod.fst).Nodup) :
    clockStep d fuel pre order = clockStep d fuel pre d.edgeIndices :=
  commitNba2_perm hdisj hwf (hwf.nodup_iff.mpr (List.nodup_range.filter _)) hnd

/-- One flop, `q <= 1`. -/
def negFlop : Design2 where
  name := "negFlop"
  decls := #[{ name := "clk", width := 1, isInput := true }, { name := "q", width := 1, isOutput := true }]
  processes := #[.alwaysFF "clk" (.nbaAssign (.ident "q") (.lit (LVec.ofNat 1 1)))]

def negPre : SvState := [("clk", LVec.ofNat 1 1), ("q", LVec.ofNat 1 0)]

/-- **A schedule that omits a process gives no conclusion**: it is not well formed, and its step
differs from the clock step. -/
theorem omitted_process : ¬ WellFormedClockStep negFlop [] ∧
    clockStep negFlop 4 negPre [] ≠ clockStep negFlop 4 negPre negFlop.edgeIndices := by
  refine ⟨fun h => by simpa [negFlop, Design2.edgeIndices, Process2.isEdgePhase] using h.length_eq, ?_⟩
  decide

/-! ## The profile, decided -/

mutual
/-- Every nonblocking target is a static window. -/
def Stmt2.nbaStaticB (d : Design2) : Stmt2 → Bool
  | .nbaAssign t _ => (t.window? d).isSome
  | .blockingAssign _ _ | .unsupported _ _ => true
  | .ifStmt _ t e => t.nbaStaticB d && Stmt2.optNbaStaticB d e
  | .caseStmt _ items dflt _ _ => CaseItem2.listNbaStaticB d items.toList && Stmt2.optNbaStaticB d dflt
  | .block body => Stmt2.listNbaStaticB d body.toList
termination_by structural s => s
def Stmt2.optNbaStaticB (d : Design2) : Option Stmt2 → Bool
  | none => true
  | some s => s.nbaStaticB d
termination_by structural o => o
def Stmt2.listNbaStaticB (d : Design2) : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.nbaStaticB d && Stmt2.listNbaStaticB d ss
termination_by structural ss => ss
def CaseItem2.listNbaStaticB (d : Design2) : List CaseItem2 → Bool
  | [] => true
  | .mk _ body :: rest => body.nbaStaticB d && CaseItem2.listNbaStaticB d rest
termination_by structural its => its
end

/-- Windows of distinct processes are pairwise disjoint. -/
def Design2.ffDisjB (d : Design2) : Bool :=
  (List.range d.processes.size).all fun i => (List.range d.processes.size).all fun j =>
    i == j || ((d.processes[i]?.map Process2.procWins).getD []).all fun a =>
      ((d.processes[j]?.map Process2.procWins).getD []).all fun b => !a.overlaps b

/-- **The FF-only profile**, decided. -/
def Design2.ffOnlyProfileB (d : Design2) : Bool :=
  let clk := match d.processes.toList.head? with | some (.alwaysFF c _) => c | _ => ""
  d.processes.toList.all (fun p => match p with
    | .alwaysFF c b => c == clk && b.nbaOnly && b.nbaStaticB d &&
        b.drvWins.all fun w => !d.inputNames.toList.contains w.1
    | _ => false) && d.ffDisjB

theorem FFOnly.ofProfile {d : Design2} (h : d.ffOnlyProfileB = true) : FFOnly d := by
  refine ⟨fun i p hp => ?_⟩
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp))
  split at this
  · rename_i c b
    simp only [Bool.and_eq_true] at this
    exact ⟨c, b, rfl, this.1.1.2⟩
  · cases this

/-! ## Soundness: updates stay inside the windows a body names -/

/-- `w` covers the update `u`: same signal, and inside `w`'s bits when `w` is a window. -/
def Covers (w : DrvWin) (u : String × Nat × LVec) : Prop :=
  u.1 = w.1 ∧ ∀ l k, w.2 = some (l, k) → l ≤ u.2.1 ∧ u.2.1 + u.2.2.width ≤ l + k

theorem indexWin?_some {idx : Expr2} {ew l k : Nat} (h : Lhs2.indexWin? idx ew = some (l, k)) :
    ∃ c j, idx = .lit c ∧ c.toNat? = some j ∧ l = j * ew ∧ k = ew := by
  cases idx <;> simp only [Lhs2.indexWin?, reduceCtorEq] at h
  rename_i c
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨j, hj, rfl, rfl⟩ := h
  exact ⟨c, j, rfl, hj, rfl, rfl⟩

/-- The update a resolved nonblocking target issues is covered by one of the target's windows. -/
theorem resolve_covered {fuel : Nat} {st : SvState} {t : Lhs2} {n : String} {lo w : Nat} (v : LVec)
    (h : resolveLhs2 fuel st t = .ok (n, some (lo, w))) :
    ∃ a ∈ t.drvWins, Covers a (n, lo, v.resizeU w) := by
  cases t with
  | ident m =>
      simp only [resolveLhs2] at h
      split at h <;> simp_all [Lhs2.drvWins, Covers]
  | slice m l k =>
      simp only [resolveLhs2, Res.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨_, List.mem_singleton_self _, rfl, fun l' k' hw => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp
  | index m idx ew =>
      refine ⟨_, List.mem_singleton_self _, ?_, fun l k hw => ?_⟩
      · simp only [resolveLhs2, Res.bind_eq_ok] at h
        obtain ⟨iv, -, h⟩ := h
        split at h
        · cases h
        · split at h
          · split at h <;> simp_all
          · simp_all
      · obtain ⟨c, j, rfl, hj, rfl, rfl⟩ := indexWin?_some hw
        simp only [resolveLhs2, Res.bind_eq_ok] at h
        obtain ⟨iv, hiv, h⟩ := h
        cases fuel with
        | zero => simp [evalExpr2] at hiv
        | succ f =>
            simp only [evalExpr2, Res.ok.injEq] at hiv
            subst hiv
            split at h
            · cases h
            · simp only [hj] at h
              split at h
              · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                simp
              · simp at h
  | concat ps => simp [resolveLhs2] at h

/-- **Every update a run issues is covered by a window of the statement.** -/
theorem upd_covered : ∀ fuel : Nat,
    (∀ (st : SvState) s nba st' nba', execStmt2 fuel st nba s = .ok (st', nba') →
      ∀ u ∈ nba', u ∈ nba ∨ ∃ a ∈ s.drvWins, Covers a u) ∧
    (∀ (st : SvState) items dflt sv mode nba st' nba',
      execCase2 fuel st nba sv items dflt mode = .ok (st', nba') →
      ∀ u ∈ nba', u ∈ nba ∨ ∃ a ∈ CaseItem2.drvWinsList items ++ Stmt2.drvWinsOpt dflt, Covers a u) ∧
    (∀ (st : SvState) ss nba st' nba', execStmts2 fuel st nba ss = .ok (st', nba') →
      ∀ u ∈ nba', u ∈ nba ∨ ∃ a ∈ Stmt2.drvWinsList ss, Covers a u)
  | 0 => ⟨fun _ _ _ _ _ h => by simp [execStmt2] at h,
      fun _ items _ _ _ _ _ _ h => by rcases items with _ | ⟨⟨_, _⟩, _⟩ <;> simp [execCase2] at h,
      fun _ _ _ _ _ h => by simp [execStmts2] at h⟩
  | f + 1 => by
      obtain ⟨ihS, ihC, ihL⟩ := upd_covered f
      refine ⟨fun st s nba st' nba' h u hu => ?_, fun st items dflt sv mode nba st' nba' h u hu => ?_,
        fun st ss nba st' nba' h u hu => ?_⟩
      · cases s with
        | nbaAssign t e =>
            simp only [execStmt2, Res.bind_eq_ok] at h
            obtain ⟨v, -, ⟨n, win⟩, hr, h⟩ := h
            cases win with
            | none => simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h; exact Or.inl (h.2 ▸ hu)
            | some lw =>
                obtain ⟨lo, w⟩ := lw
                simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                rw [← h.2, List.mem_append, List.mem_singleton] at hu
                rcases hu with hu | rfl
                · exact Or.inl hu
                · exact Or.inr (by simpa [Stmt2.drvWins] using resolve_covered v hr)
        | blockingAssign t e =>
            simp only [execStmt2, Res.bind_eq_ok] at h
            obtain ⟨v, -, h⟩ := h
            split at h
            · simp only [Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨_, -, _, -, -, rfl⟩ := h
              exact Or.inl hu
            · simp only [Res.bind_eq_ok] at h
              obtain ⟨_, -, h⟩ := h
              split at h
              · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h; exact Or.inl (h.2 ▸ hu)
              · split at h
                · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h; exact Or.inl (h.2 ▸ hu)
                · cases h
        | ifStmt c t e =>
            simp only [execStmt2, Res.bind_eq_ok] at h
            obtain ⟨cv, -, h⟩ := h
            split at h
            · rcases ihS st t nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
              · exact Or.inl h'
              · exact Or.inr ⟨a, by simp [Stmt2.drvWins, ha], hc⟩
            · cases e with
              | none => simp only [Res.ok.injEq, Prod.mk.injEq] at h; exact Or.inl (h.2 ▸ hu)
              | some s =>
                  rcases ihS st s nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
                  · exact Or.inl h'
                  · exact Or.inr ⟨a, by simp [Stmt2.drvWins, Stmt2.drvWinsOpt, ha], hc⟩
        | caseStmt subj items dflt mode chk =>
            simp only [execStmt2, Res.bind_eq_ok] at h
            obtain ⟨sv, -, h⟩ := h
            rcases ihC st items.toList dflt sv mode nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
            · exact Or.inl h'
            · exact Or.inr ⟨a, by simpa [Stmt2.drvWins] using ha, hc⟩
        | block body =>
            simp only [execStmt2] at h
            rcases ihL st body.toList nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
            · exact Or.inl h'
            · exact Or.inr ⟨a, by simpa [Stmt2.drvWins] using ha, hc⟩
        | unsupported _ _ => simp [execStmt2] at h
      · rcases items with _ | ⟨⟨pats, body⟩, rest⟩
        · cases dflt with
          | none => simp only [execCase2, Res.ok.injEq, Prod.mk.injEq] at h; exact Or.inl (h.2 ▸ hu)
          | some s =>
              simp only [execCase2] at h
              rcases ihS st s nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
              · exact Or.inl h'
              · exact Or.inr ⟨a, by simp [CaseItem2.drvWinsList, Stmt2.drvWinsOpt, ha], hc⟩
        · simp only [execCase2, Res.bind_eq_ok] at h
          obtain ⟨pvs, -, h⟩ := h
          split at h
          · rcases ihS st body nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
            · exact Or.inl h'
            · exact Or.inr ⟨a, by simp [CaseItem2.drvWinsList, CaseItem2.drvWins, ha], hc⟩
          · rcases ihC st rest dflt sv mode nba st' nba' h u hu with h' | ⟨a, ha, hc⟩
            · exact Or.inl h'
            · refine Or.inr ⟨a, ?_, hc⟩
              simp only [List.mem_append] at ha ⊢
              rcases ha with ha | ha
              · exact Or.inl (by simp [CaseItem2.drvWinsList, ha])
              · exact Or.inr ha
      · rcases ss with _ | ⟨s, ss⟩
        · simp only [execStmts2, Res.ok.injEq, Prod.mk.injEq] at h; exact Or.inl (h.2 ▸ hu)
        · simp only [execStmts2, Res.bind_eq_ok] at h
          obtain ⟨⟨st1, nba1⟩, h1, h2⟩ := h
          rcases ihL st1 ss nba1 st' nba' h2 u hu with h' | ⟨a, ha, hc⟩
          · rcases ihS st s nba st1 nba1 h1 u h' with h'' | ⟨a, ha, hc⟩
            · exact Or.inl h''
            · exact Or.inr ⟨a, by simp [Stmt2.drvWinsList, ha], hc⟩
          · exact Or.inr ⟨a, by simp [Stmt2.drvWinsList, ha], hc⟩

theorem covers_disj {a b : DrvWin} {u u' : String × Nat × LVec} (hab : a.overlaps b = false)
    (hu : Covers a u) (hu' : Covers b u') : NbaDisj u u' := by
  obtain ⟨n, wa⟩ := a
  obtain ⟨m, wb⟩ := b
  obtain ⟨h1, h2⟩ := hu
  obtain ⟨h1', h2'⟩ := hu'
  by_cases hnm : n = m
  · subst hnm
    cases wa with
    | none => simp [DrvWin.overlaps] at hab
    | some p =>
        cases wb with
        | none => simp [DrvWin.overlaps] at hab
        | some q =>
            obtain ⟨l, k⟩ := p
            obtain ⟨l', k'⟩ := q
            have := h2 l k rfl
            have := h2' l' k' rfl
            simp only [DrvWin.overlaps, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff,
              decide_eq_false_iff_not] at hab
            right; omega
  · exact Or.inl (by rw [h1, h1']; exact hnm)

/-- **The profile makes the updates of distinct processes disjoint**, on every state. -/
theorem ffUpd_disj {d : Design2} (h : d.ffOnlyProfileB = true) (fuel : Nat) (st : SvState) :
    ∀ i j, i ≠ j → ∀ u ∈ d.ffUpd fuel st i, ∀ u' ∈ d.ffUpd fuel st j, NbaDisj u u' := by
  intro i j hij u hu u' hu'
  have cov : ∀ r, ∀ x ∈ d.ffUpd fuel st r, ∃ p, d.processes[r]? = some p ∧
      ∃ a ∈ p.procWins, Covers a x := by
    intro r x hx
    simp only [Design2.ffUpd] at hx
    split at hx
    · rename_i p hp
      split at hx
      · rename_i q hq
        obtain ⟨c, b, rfl, -⟩ := (FFOnly.ofProfile h).procs r _ hp
        rcases (upd_covered fuel).1 st b [] _ q hq x hx with hx | hx
        · cases hx
        · exact ⟨_, hp, hx⟩
      · cases hx
    · cases hx
  obtain ⟨p, hp, a, ha, hca⟩ := cov i u hu
  obtain ⟨q, hq, b, hb, hcb⟩ := cov j u' hu'
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true] at h
  simp only [Design2.ffDisjB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  have hin := h.2 i (Array.getElem?_eq_some_iff.mp hp).1 j (Array.getElem?_eq_some_iff.mp hq).1
  rcases hin with hij' | hin
  · exact absurd hij' hij
  · simp only [hp, hq, Option.map_some, Option.getD_some, Bool.not_eq_true'] at hin
    exact covers_disj (hin a ha b hb) hca hcb

/-- **The clock step under the profile**: `cycleStep2_ffOnly` with the disjointness discharged. -/
theorem cycleStep2_profile {d : Design2} (h : d.ffOnlyProfileB = true) (σ : ScheduleOracle) {fuel : Nat}
    (inputs st : SvState) (k : Nat)
    (hrun : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p →
      ∃ q, runEdgeProcess2 fuel (applyInputs2 d inputs st) [] p = .ok (applyInputs2 d inputs st, q))
    (hnd : ((applyInputs2 d inputs st).map Prod.fst).Nodup) (hf : 1 ≤ fuel) :
    cycleStep2 d σ fuel inputs st k =
      .ok (clockStep d fuel (applyInputs2 d inputs st) d.edgeIndices, k + 3) :=
  cycleStep2_ffOnly (FFOnly.ofProfile h) σ inputs st k hrun (ffUpd_disj h fuel _) hnd hf

/-! ## Shared lemmas of the clock-step proofs (moved from the matmul G1 reference) -/

/-- Pairwise disjoint windows in list order decide `ffDisjB` (which is stated by index). -/
theorem ffDisjB_of_pairwise {d : Design2} (h : d.processes.toList.Pairwise
    fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false) : d.ffDisjB = true := by
  have key : ∀ i j (hi : i < d.processes.size) (hj : j < d.processes.size), i < j →
      ∀ a ∈ d.processes[i].procWins, ∀ b ∈ d.processes[j].procWins, a.overlaps b = false :=
    fun i j hi hj hij => List.pairwise_iff_getElem.mp h i j (by simpa using hi) (by simpa using hj) hij
  simp only [Design2.ffDisjB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  intro i hi j hj
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact Or.inr (by simpa [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj] using key i j hi hj hij)
  · exact Or.inl rfl
  · simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj, Option.map_some,
      Option.getD_some, Bool.not_eq_true']
    exact Or.inr fun a ha b hb => by rw [overlaps_comm]; exact key j i hj hi hij b hb a ha

/-- With every process an edge process, the edge pass visits every process, in order. -/
theorem flatMap_ffUpd {d : Design2} (F : Nat) (st : SvState)
    (h : ∀ p ∈ d.processes.toList, p.isEdgePhase = true) :
    d.edgeIndices.flatMap (d.ffUpd F st) = d.processes.toList.flatMap fun p =>
      match runEdgeProcess2 F st [] p with | .ok (_, q) => q | _ => [] := by
  have he : d.edgeIndices = List.range d.processes.size :=
    List.filter_eq_self.mpr fun i hi => by
      rw [Array.getElem?_eq_getElem (List.mem_range.mp hi)]
      exact h _ (Array.getElem_mem_toList _)
  rw [he, ← Array.length_toList]
  refine flatMap_range_eq _ _ _ fun i hi => ?_
  have hi' : i < d.processes.size := by simpa using hi
  unfold Design2.ffUpd
  rw [Array.getElem?_eq_getElem hi', Array.getElem_toList]
  dsimp only
  cases runEdgeProcess2 F st [] d.processes[i] <;> rfl

#print axioms ffDisjB_of_pairwise
#print axioms flatMap_ffUpd
#print axioms clockStep_wellFormed
#print axioms omitted_process
#print axioms FFOnly.ofProfile
#print axioms upd_covered
#print axioms ffUpd_disj
#print axioms cycleStep2_profile

end LeanModels.Sv
