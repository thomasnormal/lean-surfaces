import LeanModels.Sv.NbaCommit
import LeanModels.Sv.Obs

/-!
# The clock cycle of an FF-only design, in closed form (`LeanModels.Sv`, S1 core)

**Status: a `run2` library theorem** (provisional over `run2`; never trusted).

For a design whose processes are all edge processes (no comb process, no asynchronous reset) and
whose bodies, run on the cycle's pre state, issue only nonblocking updates and leave the state alone,
one cycle of `run2` is: apply the inputs; every process issues its updates on that state; commit
them. When updates of different processes write disjoint bits the result does not depend on the
schedule: `cycleStep2_ffOnly` gives it in process-index order.

* `Stmt2.nbaOnly`: the body profile (nonblocking assignments under `if`/`case`/`begin…end`).
  `execStmt2_nbaOnly`: such a body leaves the state alone and its updates do not depend on the queue
  it is handed (`liftQ`).
* `Design2.ffUpd d fuel st i`: the updates process `i` issues on `st`.
* `FFOnly d`: every process is an `always_ff` or a plain edge-triggered
  `always` with an NBA-only body (so no comb process and no `alwaysFFR`). The
  source style remains in `Process2`; this profile states the shared edge/NBA
  execution contract. The decidable profile and schedule class are in
  `SeqProfile.lean`.
* `CycleModel d`, `CycleModel.snapshot`: any design's clock step as a relation `Step e prev st` on a
  `Shape` of states, and every snapshot of a run as one `Step` from the previous snapshot: what a
  protocol-level proof of a clocked design consumes instead of fuel, schedules and traces.

This is the generic half of the sequential `sv_equations` (`sv_seq_equations`): per design, what
remains is evaluating `ffUpd` on an encoded state and committing it.
-/

namespace LeanModels.Sv

set_option autoImplicit false

mutual
/-- Nonblocking assignments only, under `if`/`case`/`begin…end`. -/
def Stmt2.nbaOnly : Stmt2 → Bool
  | .nbaAssign _ _ => true
  | .blockingAssign _ _ | .unsupported _ _ => false
  | .ifStmt _ t e => t.nbaOnly && Stmt2.optNbaOnly e
  | .caseStmt _ items dflt _ _ => CaseItem2.listNbaOnly items.toList && Stmt2.optNbaOnly dflt
  | .block body => Stmt2.listNbaOnly body.toList
termination_by structural s => s
def Stmt2.optNbaOnly : Option Stmt2 → Bool
  | none => true
  | some s => s.nbaOnly
termination_by structural o => o
def Stmt2.listNbaOnly : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.nbaOnly && Stmt2.listNbaOnly ss
termination_by structural ss => ss
def CaseItem2.listNbaOnly : List CaseItem2 → Bool
  | [] => true
  | .mk _ body :: rest => body.nbaOnly && CaseItem2.listNbaOnly rest
termination_by structural its => its
end

/-- A run that leaves the state `st` alone and appends `q` to the queue it was handed. -/
def liftQ (st : SvState) (nba : NbaQueue2) : Res NbaQueue2 → Res (SvState × NbaQueue2)
  | .ok q => .ok (st, nba ++ q)
  | .timeout => .timeout
  | .unsupported m => .unsupported m

/-- The update a nonblocking assignment issues (none for an out-of-range run-time index). -/
def nbaQ (f : Nat) (st : SvState) (t : Lhs2) (e : Expr2) : Res NbaQueue2 := do
  let v ← evalExpr2 f st e
  let (n, win) ← resolveLhs2 f st t
  match win with
  | none => pure []
  | some (lo, w) => pure [(n, lo, v.resizeU w)]

/-- **An NBA-only body leaves the state alone; its updates do not depend on the queue.** -/
theorem execStmt2_nbaOnly : ∀ (fuel : Nat) (st : SvState),
    (∀ s : Stmt2, s.nbaOnly = true → ∃ r, ∀ nba, execStmt2 fuel st nba s = liftQ st nba r) ∧
    (∀ (items : List CaseItem2) (dflt : Option Stmt2) (sv : LVec) (mode : CaseMode),
      CaseItem2.listNbaOnly items = true → Stmt2.optNbaOnly dflt = true →
      ∃ r, ∀ nba, execCase2 fuel st nba sv items dflt mode = liftQ st nba r) ∧
    (∀ ss : List Stmt2, Stmt2.listNbaOnly ss = true →
      ∃ r, ∀ nba, execStmts2 fuel st nba ss = liftQ st nba r)
  | 0, st => ⟨fun _ _ => ⟨.timeout, fun _ => rfl⟩,
      fun items _ _ _ _ _ => ⟨.timeout, fun _ => by rcases items with _ | ⟨⟨_, _⟩, _⟩ <;> rfl⟩,
      fun _ _ => ⟨.timeout, fun _ => rfl⟩⟩
  | f + 1, st => by
      obtain ⟨ihS, ihC, ihL⟩ := execStmt2_nbaOnly f st
      refine ⟨fun s hs => ?_, fun items dflt sv mode hi hd => ?_, fun ss hss => ?_⟩
      · cases s with
        | nbaAssign t e =>
            refine ⟨nbaQ f st t e, fun nba => ?_⟩
            simp only [execStmt2, nbaQ]
            cases evalExpr2 f st e with
            | timeout => rfl
            | unsupported m => rfl
            | ok v =>
                simp only [Res.ok_bind]
                cases resolveLhs2 f st t with
                | timeout => rfl
                | unsupported m => rfl
                | ok r =>
                    obtain ⟨n, win⟩ := r
                    cases win <;> simp [liftQ]
        | ifStmt c t e =>
            simp only [Stmt2.nbaOnly, Bool.and_eq_true] at hs
            obtain ⟨rt, hrt⟩ := ihS t hs.1
            have he := hs.2
            clear hs
            cases e with
            | none =>
                refine ⟨evalExpr2 f st c >>= fun cv => if cv.condTrue then rt else .ok [], fun nba => ?_⟩
                simp only [execStmt2]
                cases evalExpr2 f st c with
                | timeout => rfl
                | unsupported m => rfl
                | ok cv =>
                    simp only [Res.ok_bind]
                    by_cases hc : cv.condTrue = true
                    · simp only [hc, if_true]; exact hrt nba
                    · simp [hc, liftQ]
            | some s =>
                obtain ⟨rs, hrs⟩ := ihS s (by simpa [Stmt2.optNbaOnly] using he)
                refine ⟨evalExpr2 f st c >>= fun cv => if cv.condTrue then rt else rs, fun nba => ?_⟩
                simp only [execStmt2]
                cases evalExpr2 f st c with
                | timeout => rfl
                | unsupported m => rfl
                | ok cv =>
                    simp only [Res.ok_bind]
                    by_cases hc : cv.condTrue = true
                    · simp only [hc, if_true]; exact hrt nba
                    · simp only [hc, Bool.false_eq_true, if_false]; exact hrs nba
        | caseStmt subj items dflt mode chk =>
            simp only [Stmt2.nbaOnly, Bool.and_eq_true] at hs
            refine ⟨evalExpr2 f st subj >>= fun sv =>
              Classical.choose (ihC items.toList dflt sv mode hs.1 hs.2), fun nba => ?_⟩
            simp only [execStmt2]
            cases evalExpr2 f st subj <;> simp only [Res.ok_bind, Res.timeout_bind,
              Res.unsupported_bind, liftQ]
            rename_i sv
            exact Classical.choose_spec (ihC items.toList dflt sv mode hs.1 hs.2) nba
        | block body =>
            obtain ⟨r, hr⟩ := ihL body.toList (by simpa [Stmt2.nbaOnly] using hs)
            exact ⟨r, fun nba => by simp only [execStmt2]; exact hr nba⟩
        | blockingAssign _ _ => simp [Stmt2.nbaOnly] at hs
        | unsupported _ _ => simp [Stmt2.nbaOnly] at hs
      · cases items with
        | nil =>
            cases dflt with
            | none => exact ⟨.ok [], fun nba => by simp [execCase2, liftQ]⟩
            | some s =>
                obtain ⟨r, hr⟩ := ihS s (by simpa [Stmt2.optNbaOnly] using hd)
                exact ⟨r, fun nba => by simp only [execCase2]; exact hr nba⟩
        | cons it rest =>
            obtain ⟨pats, body⟩ := it
            simp only [CaseItem2.listNbaOnly, Bool.and_eq_true] at hi
            obtain ⟨rb, hrb⟩ := ihS body hi.1
            obtain ⟨rr, hrr⟩ := ihC rest dflt sv mode hi.2 hd
            refine ⟨evalExprs2 f st pats.toList >>= fun pvs =>
              if pvs.any (fun pv => caseHit mode sv pv) then rb else rr, fun nba => ?_⟩
            simp only [execCase2]
            cases evalExprs2 f st pats.toList <;> simp only [Res.ok_bind, Res.timeout_bind,
              Res.unsupported_bind, liftQ]
            rename_i pvs
            by_cases hh : pvs.any (fun pv => caseHit mode sv pv) = true
            · simp only [hh, if_true]; exact hrb nba
            · simp only [hh]; exact hrr nba
      · cases ss with
        | nil => exact ⟨.ok [], fun nba => by simp [execStmts2, liftQ]⟩
        | cons s ss =>
            simp only [Stmt2.listNbaOnly, Bool.and_eq_true] at hss
            obtain ⟨r1, hr1⟩ := ihS s hss.1
            obtain ⟨r2, hr2⟩ := ihL ss hss.2
            refine ⟨r1 >>= fun q1 => r2 >>= fun q2 => pure (q1 ++ q2), fun nba => ?_⟩
            simp only [execStmts2, hr1]
            cases r1 <;> simp only [liftQ, Res.ok_bind, Res.timeout_bind, Res.unsupported_bind]
            rename_i q1
            rw [hr2]
            cases r2 <;> simp [liftQ, List.append_assoc]

/-! ## The edge pass and the cycle -/

/-- The updates process `i` issues on `st` (none if it fails or is not an edge process). -/
def Design2.ffUpd (d : Design2) (fuel : Nat) (st : SvState) (i : Nat) : NbaQueue2 :=
  match d.processes[i]? with
  | some p => match runEdgeProcess2 fuel st [] p with
    | .ok (_, q) => q
    | _ => []
  | none => []

/-- `run2`'s edge-phase process run, with the queue it is handed prepended. -/
theorem runEdgeProcess2_shift {fuel : Nat} {st : SvState} {p : Process2}
    (hp : ∀ (c : String) (b : Stmt2),
      (p = .alwaysFF c b ∨ p = .alwaysPlain c b) → b.nbaOnly = true)
    (hff : ∃ (c : String) (b : Stmt2),
      p = .alwaysFF c b ∨ p = .alwaysPlain c b) (nba : NbaQueue2) :
    runEdgeProcess2 fuel st nba p = liftQ st nba (match runEdgeProcess2 fuel st [] p with
      | .ok (_, q) => .ok q | .timeout => .timeout | .unsupported m => .unsupported m) := by
  obtain ⟨c, b, hpb⟩ := hff
  have hb : b.nbaOnly = true := hp c b hpb
  rcases hpb with hpb | hpb
  · subst p
    obtain ⟨r, hr⟩ := (execStmt2_nbaOnly fuel st).1 b hb
    simp only [runEdgeProcess2, hr]
    cases r <;> simp [liftQ]
  · subst p
    obtain ⟨r, hr⟩ := (execStmt2_nbaOnly fuel st).1 b hb
    simp only [runEdgeProcess2, hr]
    cases r <;> simp [liftQ]

/-! The design profile: every process is an `alwaysFF` or plain edge-triggered
`always` whose body is NBA-only. -/
structure FFOnly (d : Design2) : Prop where
  procs : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p →
    ∃ (c : String) (b : Stmt2),
      (p = .alwaysFF c b ∨ p = .alwaysPlain c b) ∧ b.nbaOnly = true

theorem FFOnly.combIndices {d : Design2} (h : FFOnly d) : d.combIndices = [] := by
  simp only [Design2.combIndices, List.filter_eq_nil_iff, List.mem_range]
  intro i hi
  obtain ⟨c, b, hp, -⟩ := h.procs i _ (Array.getElem?_eq_getElem hi)
  rcases hp with hp | hp <;>
    simp [Array.getElem?_eq_getElem hi, hp, Process2.isCombPhase]

theorem FFOnly.resetIndices {d : Design2} (h : FFOnly d) (a b : SvState) :
    d.resetIndices a b = [] := by
  simp only [Design2.resetIndices, List.filter_eq_nil_iff, List.mem_range]
  intro i hi
  obtain ⟨c, bd, hp, -⟩ := h.procs i _ (Array.getElem?_eq_getElem hi)
  rcases hp with hp | hp <;> simp [Array.getElem?_eq_getElem hi, hp]

/-- **The edge pass of an FF-only design**: every listed process issues its updates on `st`. -/
theorem edgePass2_ffOnly {d : Design2} (h : FFOnly d) {fuel : Nat} {st : SvState}
    (hrun : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → ∃ q, runEdgeProcess2 fuel st [] p = .ok (st, q)) :
    ∀ (l : List Nat) (nba : NbaQueue2), edgePass2 d fuel st nba l = .ok (st, nba ++ l.flatMap (d.ffUpd fuel st))
  | [], nba => by simp [edgePass2]
  | i :: l, nba => by
      cases hp : d.processes[i]? with
      | none =>
          simp only [edgePass2, List.flatMap_cons, hp, Res.pure_eq, Res.ok_bind]
          rw [edgePass2_ffOnly h hrun l nba]
          simp [Design2.ffUpd, hp]
      | some p =>
          obtain ⟨c, b, hpb, hb⟩ := h.procs i _ hp
          obtain ⟨q, hq⟩ := hrun i _ hp
          have hbody : ∀ (c' : String) (b' : Stmt2),
              (p = .alwaysFF c' b' ∨ p = .alwaysPlain c' b') → b'.nbaOnly = true := by
            intro c' b' he
            rcases hpb with hpb | hpb
            · rcases he with he | he
              · have heq : Process2.alwaysFF c b = Process2.alwaysFF c' b' := hpb.symm.trans he
                cases heq
                exact hb
              · have heq : Process2.alwaysFF c b = Process2.alwaysPlain c' b' := hpb.symm.trans he
                cases heq
            · rcases he with he | he
              · have heq : Process2.alwaysPlain c b = Process2.alwaysFF c' b' := hpb.symm.trans he
                cases heq
              · have heq : Process2.alwaysPlain c b = Process2.alwaysPlain c' b' := hpb.symm.trans he
                cases heq
                exact hb
          simp only [edgePass2, List.flatMap_cons, hp]
          rw [runEdgeProcess2_shift hbody ⟨c, b, hpb⟩ nba, hq]
          simp only [liftQ, Res.ok_bind]
          rw [edgePass2_ffOnly h hrun l (nba ++ q)]
          simp [Design2.ffUpd, hp, hq, List.append_assoc]

/-- **One cycle of an FF-only design, in closed form**: the inputs applied, then the commit of every
process's updates computed on that state, in index order, under every schedule. -/
theorem cycleStep2_ffOnly {d : Design2} (h : FFOnly d) (σ : ScheduleOracle) {fuel : Nat}
    (inputs st : SvState) (k : Nat)
    (hrun : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p →
      ∃ q, runEdgeProcess2 fuel (applyInputs2 d inputs st) [] p = .ok (applyInputs2 d inputs st, q))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ d.ffUpd fuel (applyInputs2 d inputs st) i,
      ∀ u' ∈ d.ffUpd fuel (applyInputs2 d inputs st) j, NbaDisj u u')
    (hnd : ((applyInputs2 d inputs st).map Prod.fst).Nodup) (hf : 1 ≤ fuel) :
    cycleStep2 d σ fuel inputs st k = .ok (commitNba2 (applyInputs2 d inputs st)
      (d.edgeIndices.flatMap (d.ffUpd fuel (applyInputs2 d inputs st))), k + 3) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hs : ∀ (s : SvState) (j : Nat), combSettle2 d σ (f + 1) s j = .ok (s, j + 1) := by
    intro s j; simp [combSettle2, h.combIndices, σ.choose_nil]
  have hperm := σ.choose_perm (k + 1) d.edgeIndices
  have hnde : d.edgeIndices.Nodup := List.nodup_range.filter _
  simp only [cycleStep2, hs, Res.ok_bind, Res.pure_eq, h.resetIndices, edgePass2_ffOnly h hrun,
    List.nil_append]
  rw [commitNba2_perm hdisj hperm (hperm.nodup_iff.mpr hnde) hnd]

/-! ## The clock step as a relation (shared by the protocol reductions of a clocked task) -/

/-- **The clock step of a design `d`**, abstracted: a `Shape` of states (widths; any values, `x` included) true
initially and kept by every cycle, and a one-cycle relation `Step e prev st` (stimulus entry, previous snapshot,
next snapshot) that every successful `cycleStep2` from a state of the shape satisfies, at any schedule and fuel.
For an FF-only design `Step` is the evaluated clock step (`cycleStep2_profile` at one fuel, `cycleStep2_det` for
the others). -/
structure CycleModel (d : Design2) where
  /-- The states the design can be in at a snapshot. -/
  Shape : SvState → Prop
  /-- One cycle: stimulus entry, previous snapshot, next snapshot. -/
  Step : SvState → SvState → SvState → Prop
  /-- The initial state has the shape. -/
  init : Shape (initState2 d)
  /-- Every successful cycle from a state of the shape is a `Step`. -/
  cycle : ∀ σ F e prev k st k', Shape prev → cycleStep2 d σ F e prev k = .ok (st, k') →
    Step e prev st
  /-- A `Step` keeps the shape. -/
  shape : ∀ e prev st, Shape prev → Step e prev st → Shape st

/-- Every snapshot of a completed run is a `Step`, at its stimulus entry, from the previous
snapshot (`initState2 d` at cycle 0), which has the shape. -/
theorem CycleModel.snapshot {d : Design2} (M : CycleModel d) {σ : ScheduleOracle}
    {stim tr : List SvState} (hr : Runs2 d σ stim tr) {c : Nat} {st : SvState}
    (hc : tr[c]? = some st) : ∃ e prev, stim[c]? = some e ∧
      (initState2 d :: tr)[c]? = some prev ∧ M.Shape prev ∧ M.Step e prev st := by
  obtain ⟨F, e, prev, k, k', he, hp, hs⟩ := hr.snapshot_step hc
  have hsh : M.Shape prev := by
    cases c with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; exact hp ▸ M.init
    | succ c => exact hr.forall_of_step M.init (fun F e q k s k' hq hs =>
        M.shape e q s hq (M.cycle σ F e q k s k' hq hs)) c prev (by simpa using hp)
  exact ⟨e, prev, he, hp, hsh, M.cycle σ F e prev k st k' hsh hs⟩

#print axioms execStmt2_nbaOnly
#print axioms edgePass2_ffOnly
#print axioms cycleStep2_ffOnly
#print axioms CycleModel.snapshot

end LeanModels.Sv
