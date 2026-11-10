import LeanModels.Sv.Kernel.Core0Comb
import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.NbaCommit

/-!
# E-core-1, the edge fragment, and R-EDGE (X4 spike) (`LeanModels.Sv.Kernel`)

Experiment X4 of `svgolf/design/architecture/ARCH-NOTE.md` §7. **Status: derived from E** (this file
extends E-core-0 with edge processes and the NBA region).

## E-core-1, edge fragment

* An edge process (`FF`) is `always_ff @(posedge clk)` or `@(posedge clk or negedge rst_n)` (an
  active-low asynchronous reset). Its body uses nonblocking assignments only (`if`/`begin-end`
  and unqualified `case`/`casez`/`casex` around them); anything else refuses. It reads the store's view, which does not change while it
  runs, and returns its NBA updates (`execFF`, the queue type `NbaQueue2` of `run2`).
* `Config1` adds the NBA queue. `step1`: if the Active region is not empty, the Choice picks a
  ready process, which runs atomically and appends its updates (the store is unchanged). If
  Active is empty and the queue is not, the NBA region commits the whole queue in issue order
  (`commitNba2` on the view) and the edge processes whose clock rose or whose reset fell across
  the commit become ready. Otherwise the slot closes.
* Slot opening (`Config1.nextSlot`): the input events are applied; the edge processes they fire are
  ready.

Committing the queue as one step, and triggering by comparing the stores before and after it, is
a modelling choice (JUDGED): an LRM simulator updates one NBA at a time and can see a glitch. No
theorem below depends on it, because no edge process may write a clock or a reset (`noEdge`).

## R-EDGE

`rEdge`: in a slot whose ready set is any duplicate-free set of edge processes, from a store `s`
with an empty queue, EVERY process-atomic legal schedule closes the slot, at the store whose view is
`commitNba2 (view s) (queue s act)`: the updates of every ready process, computed on `s`, committed
in index order. The closed store does not depend on the schedule. Hypotheses (`EdgeProfile`, all
decided on the bodies' static NBA windows by `EdgeProfile.ofChecks`): bodies execute; one edge
writer per slice; no process writes a clock or a reset.

The clocking discipline and its audit of `clockExpand` are in `Core1Disc.lean`.
-/

namespace LeanModels.Sv

/-! ## Static NBA windows of a body -/

mutual

/-- Every window a nonblocking assignment of the body may write. -/
def Stmt2.nbaWins (d : Design2) : Stmt2 → List Win
  | .nbaAssign t _ => t.wins d
  | .ifStmt _ t e => t.nbaWins d ++ Stmt2.optNbaWins d e
  | .block body => Stmt2.listNbaWins d body.toList
  | .caseStmt _ items dflt _ _ => CaseItem2.listNbaWins d items.toList ++ Stmt2.optNbaWins d dflt
  | .blockingAssign _ _ | .unsupported _ _ => []
termination_by structural s => s

def Stmt2.optNbaWins (d : Design2) : Option Stmt2 → List Win
  | none => []
  | some s => s.nbaWins d
termination_by structural o => o

def Stmt2.listNbaWins (d : Design2) : List Stmt2 → List Win
  | [] => []
  | s :: ss => s.nbaWins d ++ Stmt2.listNbaWins d ss
termination_by structural ss => ss

def CaseItem2.nbaWins (d : Design2) : CaseItem2 → List Win
  | .mk _ body => body.nbaWins d
termination_by structural it => it

def CaseItem2.listNbaWins (d : Design2) : List CaseItem2 → List Win
  | [] => []
  | it :: rest => it.nbaWins d ++ CaseItem2.listNbaWins d rest
termination_by structural its => its

end

mutual

/-- The bodies E-core-1's edge fragment runs without refusing: nonblocking assignments with static
targets and well-formed right-hand sides, under `if`, unqualified `case`/`casez`/`casex` and `begin-end`. -/
def Stmt2.ffOkB (d : Design2) : Stmt2 → Bool
  | .nbaAssign t e => (t.windows? d).isSome && e.wfB d
  | .ifStmt c t e => c.wfB d && t.ffOkB d && Stmt2.optFfOkB d e
  | .block body => Stmt2.listFfOkB d body.toList
  | .caseStmt subj items dflt mode check =>
      subj.wfB d && CaseItem2.listFfOkB d items.toList && Stmt2.optFfOkB d dflt &&
        decide (mode ≠ .inside) && decide (check = .none)
  | .blockingAssign _ _ | .unsupported _ _ => false
termination_by structural s => s

def Stmt2.optFfOkB (d : Design2) : Option Stmt2 → Bool
  | none => true
  | some s => s.ffOkB d
termination_by structural o => o

def Stmt2.listFfOkB (d : Design2) : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.ffOkB d && Stmt2.listFfOkB d ss
termination_by structural ss => ss

def CaseItem2.ffOkB (d : Design2) : CaseItem2 → Bool
  | .mk pats body => Expr2.listWfB d pats.toList && body.ffOkB d
termination_by structural it => it

def CaseItem2.listFfOkB (d : Design2) : List CaseItem2 → Bool
  | [] => true
  | it :: rest => it.ffOkB d && CaseItem2.listFfOkB d rest
termination_by structural its => its

end

/-! ## Committing nonblocking updates

`nbaStep`, `NbaDisj` and the commit lemmas (`commitNba2_cons`/`_append`, `keys_commitNba2`,
`lookup_commitNba2_of_not_mem`, `nbaStep_comm`, `commitNba2_move`/`_swap`/`_perm`) are in
`LeanModels/Sv/NbaCommit.lean`, where they were moved verbatim from this file. -/

end LeanModels.Sv

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

/-! ## E-core-1, the edge fragment -/

/-! A process clock may fire on either IEEE edge.  The source loader still
keeps negative-edge process metadata at its loud boundary; this selector makes
the E event rule ready for that retained form without changing today's default
positive-edge profile. -/

inductive ClockEdge where
  | posedge
  | negedge
deriving Repr, BEq, DecidableEq, Inhabited

/-- An edge process: `always_ff @(posedge clk)`, or `@(posedge clk or negedge rstn)`. -/
structure FF where
  clk : String
  rstn : Option String
  body : Stmt2
  edge : ClockEdge := .posedge

/-- An elaborated design of edge processes. -/
structure Elab1 where
  decls : Array Decl
  procs : Array FF
  name : String := "core1"

/-- The store, view and typing of E-core-0, for the same declarations. -/
def Elab1.base (E : Elab1) : Elab := { decls := E.decls, procs := #[], name := E.name }

/-- The declarations as a `Design2` (window resolution). -/
def Elab1.design (E : Elab1) : Design2 := E.base.toDesign2

mutual

/-- **Run an edge process's body** on the view (which does not change while it runs): its
nonblocking updates, in issue order. A refusal is loud and cites its clause:
`"<clause>: <message>"` (`Core0`'s `refuse0` form). -/
def execFF (d : Design2) (st : SvState) : Stmt2 → Except String NbaQueue2
  | .nbaAssign t e =>
      match t.windows? d with
      | some ws =>
          match evalPure2 st e with
          | .ok v =>
              .ok ((Win.placed ws).map fun x =>
                (x.1.1, x.1.2.1, (v.resizeU (Win.sumWidth ws)).extract x.2 x.1.2.2))
          | .unsupported m => .error s!"11: {m}"
          | .timeout => .error "11: evaluation exhausted"
      | none => .error "10.4.2: nonblocking assignment target is not a static window"
  | .ifStmt c t e =>
      match evalPure2 st c with
      | .ok cv => if cv.condTrue then execFF d st t else execFFOpt d st e
      | .unsupported m => .error s!"11: {m}"
      | .timeout => .error "11: evaluation exhausted"
  | .block body => execFFList d st body.toList
  | .caseStmt subj items dflt mode check =>
      if mode = .inside ∨ check ≠ .none then
        .error "12.5: case inside and qualified case are outside E-core-1"
      else
        match evalPure2 st subj with
        | .ok sv =>
            match execFFCase d st mode sv items.toList with
            | .ok (some q) => .ok q
            | .ok none => execFFOpt d st dflt
            | .error m => .error m
        | .unsupported m => .error s!"11: {m}"
        | .timeout => .error "11: evaluation exhausted"
  | .blockingAssign _ _ =>
      .error "9.2.2.4: blocking assignment in always_ff is outside E-core-1"
  | .unsupported k _ => .error s!"12: unsupported statement '{k}'"
termination_by structural s => s

def execFFOpt (d : Design2) (st : SvState) : Option Stmt2 → Except String NbaQueue2
  | none => .ok []
  | some s => execFF d st s
termination_by structural o => o

def execFFList (d : Design2) (st : SvState) : List Stmt2 → Except String NbaQueue2
  | [] => .ok []
  | s :: ss =>
      match execFF d st s with
      | .ok q =>
          match execFFList d st ss with
          | .ok q' => .ok (q ++ q')
          | .error m => .error m
      | .error m => .error m
termination_by structural ss => ss

/-- IEEE 1800-2023 §§12.5, 12.5.1: the existing `caseHit` gives plain,
z-wildcard or x/z-wildcard matching. A matching item executes its body on the unchanged
sampled view. `some []` is a match whose body issues no NBA, distinct from a miss. -/
def execFFArm (d : Design2) (st : SvState) (mode : CaseMode) (sv : LVec) :
    CaseItem2 → Except String (Option NbaQueue2)
  | .mk pats body =>
      match evalPures2 st pats.toList with
      | .ok pvs =>
          if pvs.any (caseHit mode sv) then
            match execFF d st body with
            | .ok q => .ok (some q)
            | .error m => .error m
          else .ok none
      | .unsupported m => .error s!"11: {m}"
      | .timeout => .error "11: evaluation exhausted"
termination_by structural it => it

/-- IEEE 1800-2023 §12.5: walk source-order items and stop at the first hit.
The selector is already evaluated; the caller handles the default after a miss. -/
def execFFCase (d : Design2) (st : SvState) (mode : CaseMode) (sv : LVec) :
    List CaseItem2 → Except String (Option NbaQueue2)
  | [] => .ok none
  | it :: rest =>
      match execFFArm d st mode sv it with
      | .ok (some q) => .ok (some q)
      | .ok none => execFFCase d st mode sv rest
      | .error m => .error m
termination_by structural its => its

end

/-- The updates process `p` issues on the store `s`. -/
def Elab1.next (E : Elab1) (s : Store) (p : ProcId) : Except String NbaQueue2 :=
  match E.procs[p]? with
  | some f => execFF E.design (E.base.view s) f.body
  | none => .error "4.5: no such process"

/-- `f` fires across a change: its clock rose, or its reset fell. -/
def FF.fires (f : FF) (st st' : SvState) : Bool :=
  (match f.edge with
   | .posedge => isPosedge (st.bit0 f.clk) (st'.bit0 f.clk)
   | .negedge => isNegedge (st.bit0 f.clk) (st'.bit0 f.clk)) ||
    match f.rstn with
    | some r => isNegedge (st.bit0 r) (st'.bit0 r)
    | none => false

/-- The edge processes a change fires, in index order. -/
def Elab1.triggered (E : Elab1) (st st' : SvState) : List ProcId :=
  (List.range E.procs.size).filter fun p =>
    match E.procs[p]? with
    | some f => f.fires st st'
    | none => false

/-- The NBA region's commit on the store, in issue order. -/
def Elab1.commit (E : Elab1) (s : Store) (q : NbaQueue2) : Store :=
  q.foldl (fun s u => E.base.writeWin s u.1 u.2.1 u.2.2) s

/-- A configuration: store, Active region, NBA queue, Choice counter. -/
structure Config1 where
  store : Store
  active : List ProcId
  nba : NbaQueue2
  k : Nat := 0

inductive StepResult1 where
  | next (c : Config1)
  | slotClosed (c : Config1)
  | refused (msg : String)

/-- **One step of E-core-1** (total, not recursive). -/
def step1 (E : Elab1) (ch : Choice) (c : Config1) : StepResult1 :=
  match ch.choose c.k c.active with
  | p :: rest =>
      match E.next c.store p with
      | .ok q => .next { store := c.store, active := rest, nba := c.nba ++ q, k := c.k + 1 }
      | .error m => .refused m
  | [] =>
      match c.nba with
      | [] => .slotClosed c
      | u :: us =>
          .next { store := E.commit c.store (u :: us)
                  active := E.triggered (E.base.view c.store)
                    (E.base.view (E.commit c.store (u :: us)))
                  nba := []
                  k := c.k + 1 }

inductive Steps1 (E : Elab1) (ch : Choice) : Config1 → Config1 → Prop where
  | refl (c : Config1) : Steps1 E ch c c
  | head {c c' c'' : Config1} : step1 E ch c = .next c' → Steps1 E ch c' c'' → Steps1 E ch c c''

theorem Steps1.tail {E : Elab1} {ch : Choice} {c c' c'' : Config1} (h : Steps1 E ch c c')
    (h' : step1 E ch c' = .next c'') : Steps1 E ch c c'' := by
  induction h with
  | refl c => exact .head h' (.refl _)
  | head hs _ ih => exact .head hs (ih h')

/-- The slot closes at `c'`. -/
def SlotCloses1 (E : Elab1) (ch : Choice) (c c' : Config1) : Prop :=
  Steps1 E ch c c' ∧ step1 E ch c' = .slotClosed c'

/-- A slot opened by input events: the edge processes they fire are ready. -/
def Config1.nextSlot (E : Elab1) (c : Config1) (entry : SvState) : Config1 :=
  { store := E.base.applyInputs c.store entry
    active := E.triggered (E.base.view c.store) (E.base.view (E.base.applyInputs c.store entry))
    nba := []
    k := c.k }

inductive ExecResult1 where
  | closed (c : Config1)
  | refused (msg : String)
  | outOfBudget (c : Config1)

/-- The test executor (the only fuel): iterate `step1` under one Choice, at most `n` times. A
harness instrument, not a semantics (`exec1_sound`). A refusal and an exhausted budget are
different results. -/
def exec1 (E : Elab1) (ch : Choice) : Nat → Config1 → ExecResult1
  | 0, c => .outOfBudget c
  | n + 1, c =>
      match step1 E ch c with
      | .next c' => exec1 E ch n c'
      | .slotClosed c' => .closed c'
      | .refused m => .refused m

theorem step1_slotClosed {E : Elab1} {ch : Choice} {c c' : Config1}
    (h : step1 E ch c = .slotClosed c') : c' = c := by
  unfold step1 at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h; rfl
    · cases h

/-- **The executor is sound**: a closed result is a closed slot. -/
theorem exec1_sound {E : Elab1} {ch : Choice} :
    ∀ {n : Nat} {c c' : Config1}, exec1 E ch n c = .closed c' → SlotCloses1 E ch c c'
  | 0, _, _, h => by simp [exec1] at h
  | n + 1, c, c', h => by
      simp only [exec1] at h
      cases hs : step1 E ch c with
      | next c₁ =>
          simp only [hs] at h
          obtain ⟨hst, hcl⟩ := exec1_sound h
          exact ⟨.head hs hst, hcl⟩
      | slotClosed c₁ =>
          simp only [hs, ExecResult1.closed.injEq] at h
          subst h
          obtain rfl := step1_slotClosed hs
          exact ⟨.refl _, hs⟩
      | refused m => simp [hs] at h

/-! ## What a body writes, and that it runs -/

mutual

/-- Every update an edge body issues writes one of its static NBA windows. -/
theorem execFF_mem {d : Design2} {st : SvState} : ∀ (s : Stmt2) {q : NbaQueue2},
    execFF d st s = .ok q → ∀ u ∈ q, (u.1, u.2.1, u.2.2.width) ∈ s.nbaWins d
  | .nbaAssign t e, q, h, u, hu => by
      simp only [execFF] at h
      split at h
      · rename_i ws hws
        split at h
        · simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
          simp only [Stmt2.nbaWins, Lhs2.wins_of_windows? hws, LVec.width_extract]
          exact Win.mem_of_mem_placed (wn := x.1) (off := x.2) hx
        · cases h
        · cases h
      · cases h
  | .ifStmt c t e, q, h, u, hu => by
      simp only [execFF] at h
      split at h
      · simp only [Stmt2.nbaWins, List.mem_append]
        split at h
        · exact Or.inl (execFF_mem t h u hu)
        · exact Or.inr (execFFOpt_mem e h u hu)
      · cases h
      · cases h
  | .block body, q, h, u, hu => by
      simp only [execFF] at h
      simp only [Stmt2.nbaWins]
      exact execFFList_mem body.toList h u hu
  | .caseStmt subj items dflt mode check, q, h, u, hu => by
      simp only [execFF] at h
      simp only [Stmt2.nbaWins, List.mem_append]
      split at h
      · cases h
      · split at h
        · rename_i sv hsv
          cases hc : execFFCase d st mode sv items.toList with
          | error m => simp [hc] at h
          | ok oq =>
              cases oq with
              | none =>
                  simp only [hc] at h
                  exact Or.inr (execFFOpt_mem dflt h u hu)
              | some qs =>
                  simp only [hc, Except.ok.injEq] at h
                  subst q
                  exact Or.inl (execFFCase_mem items.toList hc u hu)
        · cases h
        · cases h
  | .blockingAssign _ _, _, h, _, _ => by simp [execFF] at h
  | .unsupported _ _, _, h, _, _ => by simp [execFF] at h
termination_by structural s => s

theorem execFFOpt_mem {d : Design2} {st : SvState} : ∀ (o : Option Stmt2) {q : NbaQueue2},
    execFFOpt d st o = .ok q → ∀ u ∈ q, (u.1, u.2.1, u.2.2.width) ∈ Stmt2.optNbaWins d o
  | none, q, h, u, hu => by
      simp only [execFFOpt, Except.ok.injEq] at h
      subst h
      exact absurd hu List.not_mem_nil
  | some s, q, h, u, hu => execFF_mem s h u hu
termination_by structural o => o

theorem execFFList_mem {d : Design2} {st : SvState} : ∀ (ss : List Stmt2) {q : NbaQueue2},
    execFFList d st ss = .ok q → ∀ u ∈ q, (u.1, u.2.1, u.2.2.width) ∈ Stmt2.listNbaWins d ss
  | [], q, h, u, hu => by
      simp only [execFFList, Except.ok.injEq] at h
      subst h
      exact absurd hu List.not_mem_nil
  | s :: ss, q, h, u, hu => by
      simp only [execFFList] at h
      obtain ⟨q₁, h₁, q₂, h₂, rfl⟩ : ∃ q₁, execFF d st s = .ok q₁ ∧ ∃ q₂,
          execFFList d st ss = .ok q₂ ∧ q = q₁ ++ q₂ := by
        split at h
        · rename_i q₁ h₁
          split at h
          · rename_i q₂ h₂
            simp only [Except.ok.injEq] at h
            exact ⟨q₁, h₁, q₂, h₂, h.symm⟩
          · cases h
        · cases h
      simp only [Stmt2.listNbaWins, List.mem_append] at hu ⊢
      rcases hu with hu | hu
      · exact Or.inl (execFF_mem s h₁ u hu)
      · exact Or.inr (execFFList_mem ss h₂ u hu)
termination_by structural ss => ss

/-- A matching case item issues only its body's static NBA windows. -/
theorem execFFArm_mem {d : Design2} {st : SvState} {mode : CaseMode} {sv : LVec} :
    ∀ (it : CaseItem2) {q : NbaQueue2}, execFFArm d st mode sv it = .ok (some q) →
      ∀ u ∈ q, (u.1, u.2.1, u.2.2.width) ∈ it.nbaWins d
  | .mk pats body, q, h, u, hu => by
      simp only [execFFArm] at h
      split at h
      · split at h
        · split at h
          · rename_i qs hqs
            simp only [Except.ok.injEq, Option.some.injEq] at h
            subst q
            exact execFF_mem body hqs u hu
          · cases h
        · cases h
      · cases h
      · cases h
termination_by structural it => it

/-- The first-match walk issues only windows of one of its source arms. -/
theorem execFFCase_mem {d : Design2} {st : SvState} {mode : CaseMode} {sv : LVec} :
    ∀ (its : List CaseItem2) {q : NbaQueue2}, execFFCase d st mode sv its = .ok (some q) →
      ∀ u ∈ q, (u.1, u.2.1, u.2.2.width) ∈ CaseItem2.listNbaWins d its
  | [], _, h, _, _ => by simp [execFFCase] at h
  | it :: rest, q, h, u, hu => by
      simp only [execFFCase] at h
      simp only [CaseItem2.listNbaWins, List.mem_append]
      cases ha : execFFArm d st mode sv it with
      | error m => simp [ha] at h
      | ok oq =>
          cases oq with
          | none =>
              simp only [ha] at h
              exact Or.inr (execFFCase_mem rest h u hu)
          | some qs =>
              simp only [ha, Except.ok.injEq, Option.some.injEq] at h
              subst q
              exact Or.inl (execFFArm_mem it ha u hu)
termination_by structural its => its

end

mutual

/-- A body in the edge profile runs, on any view that binds the declared names. -/
theorem execFF_total {d : Design2} {st : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v) :
    ∀ (s : Stmt2), s.ffOkB d = true → ∃ q, execFF d st s = .ok q
  | .nbaAssign t e, h => by
      simp only [Stmt2.ffOkB, Bool.and_eq_true, Option.isSome_iff_exists] at h
      obtain ⟨⟨ws, hws⟩, he⟩ := h
      obtain ⟨hu, hid⟩ := Expr2.wfB_spec he
      obtain ⟨v, hv⟩ := evalPure2_ok_of_wf hu fun x hx => hb x (hid x hx)
      exact ⟨(Win.placed ws).map fun x =>
          (x.1.1, x.1.2.1, (v.resizeU (Win.sumWidth ws)).extract x.2 x.1.2.2),
        by simp only [execFF, hws, hv]⟩
  | .ifStmt c t e, h => by
      simp only [Stmt2.ffOkB, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ht⟩, he⟩ := h
      obtain ⟨hu, hid⟩ := Expr2.wfB_spec hc
      obtain ⟨cv, hcv⟩ := evalPure2_ok_of_wf hu fun x hx => hb x (hid x hx)
      by_cases hcond : cv.condTrue = true
      · obtain ⟨q, hq⟩ := execFF_total hb t ht
        exact ⟨q, by simp only [execFF, hcv, hcond, if_true]; exact hq⟩
      · obtain ⟨q, hq⟩ := execFFOpt_total hb e he
        exact ⟨q, by simp only [execFF, hcv, hcond]; exact hq⟩
  | .block body, h => by
      simp only [Stmt2.ffOkB] at h
      obtain ⟨q, hq⟩ := execFFList_total hb body.toList h
      exact ⟨q, by simp only [execFF]; exact hq⟩
  | .caseStmt subj items dflt mode check, h => by
      simp only [Stmt2.ffOkB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hs, hi⟩, hd⟩, hm⟩, rfl⟩ := h
      obtain ⟨hu, hid⟩ := Expr2.wfB_spec hs
      obtain ⟨sv, hsv⟩ := evalPure2_ok_of_wf hu fun x hx => hb x (hid x hx)
      obtain ⟨oq, hq⟩ := execFFCase_total hb mode sv items.toList hi
      cases oq with
      | some q => exact ⟨q, by simp [execFF, hm, hsv, hq]⟩
      | none =>
          obtain ⟨q, hd⟩ := execFFOpt_total hb dflt hd
          exact ⟨q, by simp [execFF, hm, hsv, hq, hd]⟩
  | .blockingAssign _ _, h => by simp [Stmt2.ffOkB] at h
  | .unsupported _ _, h => by simp [Stmt2.ffOkB] at h
termination_by structural s => s

theorem execFFOpt_total {d : Design2} {st : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v) :
    ∀ (o : Option Stmt2), Stmt2.optFfOkB d o = true → ∃ q, execFFOpt d st o = .ok q
  | none, _ => ⟨[], rfl⟩
  | some s, h => execFF_total hb s h
termination_by structural o => o

theorem execFFList_total {d : Design2} {st : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v) :
    ∀ (ss : List Stmt2), Stmt2.listFfOkB d ss = true → ∃ q, execFFList d st ss = .ok q
  | [], _ => ⟨[], rfl⟩
  | s :: ss, h => by
      simp only [Stmt2.listFfOkB, Bool.and_eq_true] at h
      obtain ⟨q₁, h₁⟩ := execFF_total hb s h.1
      obtain ⟨q₂, h₂⟩ := execFFList_total hb ss h.2
      exact ⟨q₁ ++ q₂, by simp only [execFFList, h₁, h₂]⟩
termination_by structural ss => ss

/-- An admitted item decides either a miss or a successful NBA queue. -/
theorem execFFArm_total {d : Design2} {st : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v)
    (mode : CaseMode) (sv : LVec) :
    ∀ (it : CaseItem2), it.ffOkB d = true → ∃ oq, execFFArm d st mode sv it = .ok oq
  | .mk pats body, h => by
      simp only [CaseItem2.ffOkB, Bool.and_eq_true] at h
      obtain ⟨hu, hid⟩ := Expr2.listWfB_spec h.1
      obtain ⟨pvs, hpvs⟩ := evalPures2_ok_of_wf hu fun x hx => hb x (hid x hx)
      by_cases hhit : pvs.any (caseHit mode sv) = true
      · obtain ⟨q, hq⟩ := execFF_total hb body h.2
        exact ⟨some q, by simp [execFFArm, hpvs, hhit, hq]⟩
      · exact ⟨none, by simp [execFFArm, hpvs, hhit]⟩
termination_by structural it => it

/-- The finite source-order walk is total on admitted case items. -/
theorem execFFCase_total {d : Design2} {st : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v)
    (mode : CaseMode) (sv : LVec) :
    ∀ (its : List CaseItem2), CaseItem2.listFfOkB d its = true →
      ∃ oq, execFFCase d st mode sv its = .ok oq
  | [], _ => ⟨none, rfl⟩
  | it :: rest, h => by
      simp only [CaseItem2.listFfOkB, Bool.and_eq_true] at h
      obtain ⟨oq, ha⟩ := execFFArm_total hb mode sv it h.1
      cases oq with
      | some q => exact ⟨some q, by simp [execFFCase, ha]⟩
      | none =>
          obtain ⟨oq, ht⟩ := execFFCase_total hb mode sv rest h.2
          exact ⟨oq, by simp [execFFCase, ha, ht]⟩
termination_by structural its => its

end

/-! ## The commit, on the view -/

/-- **The NBA region's commit is `commitNba2` on the view** (4-state declarations). -/
theorem Elab1.view_commit {E : Elab1} (h4 : AllFour E.base) :
    ∀ {s : Store} (q : NbaQueue2), E.base.Typed s →
      E.base.view (E.commit s q) = commitNba2 (E.base.view s) q
  | _, [], _ => rfl
  | s, u :: q, hT => by
      show E.base.view (E.commit (E.base.writeWin s u.1 u.2.1 u.2.2) q) = _
      rw [Elab1.view_commit h4 q (hT.writeWin _ _ _), Elab.view_writeWin hT h4]
      rfl

theorem Elab1.typed_commit {E : Elab1} : ∀ {s : Store} (q : NbaQueue2), E.base.Typed s →
    E.base.Typed (E.commit s q)
  | _, [], hT => hT
  | _, _ :: q, hT => Elab1.typed_commit (E := E) q (hT.writeWin _ _ _)

/-! ## The edge profile -/

/-- **What R-EDGE needs.** Every body runs on a typed store; two processes never write overlapping
bits (one edge writer per slice); no update writes a clock or a reset. -/
structure EdgeProfile (E : Elab1) : Prop where
  four : AllFour E.base
  nodup : (E.decls.toList.map Decl.name).Nodup
  total : ∀ s, E.base.Typed s → ∀ p, p < E.procs.size → ∃ q, E.next s p = .ok q
  oneWriter : ∀ s p p' q q', p ≠ p' → E.next s p = .ok q → E.next s p' = .ok q' →
    ∀ u ∈ q, ∀ u' ∈ q', NbaDisj u u'
  noEdge : ∀ s p q, E.next s p = .ok q → ∀ u ∈ q, ∀ f ∈ E.procs.toList,
    u.1 ≠ f.clk ∧ f.rstn ≠ some u.1

/-- Every body is in the edge profile, decided. -/
def Elab1.okB (E : Elab1) : Bool := E.procs.toList.all fun f => f.body.ffOkB E.design

/-- One edge writer per slice, decided on the static NBA windows. -/
def Elab1.oneWriterB (E : Elab1) : Bool :=
  (List.range E.procs.size).all fun p => (List.range E.procs.size).all fun p' =>
    p == p' ||
      match E.procs[p]?, E.procs[p']? with
      | some f, some f' => (f.body.nbaWins E.design).all fun W =>
          (f'.body.nbaWins E.design).all fun W' => !Win.overlaps W W'
      | _, _ => true

/-- No NBA window is a clock or a reset, decided. -/
def Elab1.noEdgeB (E : Elab1) : Bool :=
  E.procs.toList.all fun f => (f.body.nbaWins E.design).all fun W =>
    E.procs.toList.all fun g => W.1 != g.clk && g.rstn != some W.1

theorem Elab1.next_some {E : Elab1} {s : Store} {p : ProcId} {q : NbaQueue2}
    (h : E.next s p = .ok q) :
    ∃ f, E.procs[p]? = some f ∧ execFF E.design (E.base.view s) f.body = .ok q := by
  simp only [Elab1.next] at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

theorem Elab1.mem_procs {E : Elab1} {p : ProcId} {f : FF} (h : E.procs[p]? = some f) :
    f ∈ E.procs.toList := by
  rw [← Array.getElem?_toList] at h
  exact List.mem_of_getElem? h

/-- **The checks discharge the profile.** -/
theorem EdgeProfile.ofChecks {E : Elab1} (h4 : AllFour E.base)
    (hnd : (E.decls.toList.map Decl.name).Nodup) (hok : E.okB = true) (h1 : E.oneWriterB = true)
    (h2 : E.noEdgeB = true) : EdgeProfile E where
  four := h4
  nodup := hnd
  total := fun s _ p hp => by
    obtain ⟨f, hf⟩ : ∃ f, E.procs[p]? = some f := ⟨_, Array.getElem?_eq_getElem hp⟩
    have hokf : f.body.ffOkB E.design = true := by
      simp only [Elab1.okB, List.all_eq_true] at hok
      exact hok f (Elab1.mem_procs hf)
    have hb : ∀ x ∈ E.design.symNames, ∃ v, SvState.lookup (E.base.view s) x = some v :=
      fun x hx => SvState.exists_lookup_of_mem (by
        rw [E.base.keys_view]; simpa [Design2.symNames, Elab1.design, Elab.toDesign2] using hx)
    obtain ⟨q, hq⟩ := execFF_total hb f.body hokf
    exact ⟨q, by simp only [Elab1.next, hf]; exact hq⟩
  oneWriter := fun s p p' q q' hne hq hq' u hu u' hu' => by
    obtain ⟨f, hf, hx⟩ := Elab1.next_some hq
    obtain ⟨f', hf', hx'⟩ := Elab1.next_some hq'
    have hw := execFF_mem f.body hx u hu
    have hw' := execFF_mem f'.body hx' u' hu'
    have hpn : p < E.procs.size := (Array.getElem?_eq_some_iff.mp hf).1
    have hpn' : p' < E.procs.size := (Array.getElem?_eq_some_iff.mp hf').1
    simp only [Elab1.oneWriterB, List.all_eq_true, List.mem_range] at h1
    have h := h1 p hpn p' hpn'
    simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, hf, hf', List.all_eq_true] at h
    have hov := h _ hw _ hw'
    simp only [Bool.not_eq_true'] at hov
    obtain ⟨n, lo, v⟩ := u
    obtain ⟨n', lo', v'⟩ := u'
    rw [Win.overlaps_eq_false] at hov
    simp only [NbaDisj]
    rcases hov with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  noEdge := fun s p q hq u hu g hg => by
    obtain ⟨f, hf, hx⟩ := Elab1.next_some hq
    have hw := execFF_mem f.body hx u hu
    simp only [Elab1.noEdgeB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
    exact h2 f (Elab1.mem_procs hf) _ hw g hg

/-! ## R-EDGE -/

/-- The updates process `p` issues on `s` (none if it refuses). -/
def Elab1.upd (E : Elab1) (s : Store) (p : ProcId) : NbaQueue2 :=
  match E.next s p with
  | .ok q => q
  | .error _ => []

/-- The updates of the processes `l`, computed on `s`, in the order of `l`. -/
def Elab1.queue (E : Elab1) (s : Store) (l : List ProcId) : NbaQueue2 :=
  l.flatMap (E.upd s)

theorem Elab1.mem_queue {E : Elab1} {s : Store} {l : List ProcId} {u : String × Nat × LVec}
    (h : u ∈ E.queue s l) : ∃ p q, E.next s p = .ok q ∧ u ∈ q := by
  obtain ⟨p, -, hu⟩ := List.mem_flatMap.mp h
  cases hq : E.next s p with
  | error m => simp [Elab1.upd, hq] at hu
  | ok q => simp only [Elab1.upd, hq] at hu; exact ⟨p, q, hq, hu⟩

/-- **The Active region of an edge slot**: under any legal schedule the ready processes all run,
the store does not change, and the queue collects their updates in the order they ran. -/
theorem active_phase {E : Elab1} (hP : EdgeProfile E) (ch : Choice) {s : Store}
    (hT : E.base.Typed s) : ∀ (n : Nat) (c : Config1), c.store = s → c.active.length = n →
      c.active.Nodup → (∀ p ∈ c.active, p < E.procs.size) →
      ∃ (ran : List ProcId) (c' : Config1), ran.Perm c.active ∧ Steps1 E ch c c' ∧
        c'.store = s ∧ c'.active = [] ∧ c'.nba = c.nba ++ E.queue s ran
  | 0, c, hs, hl, _, _ =>
      ⟨[], c, by rw [List.length_eq_zero_iff.mp hl], .refl c, hs, List.length_eq_zero_iff.mp hl,
        by simp [Elab1.queue]⟩
  | n + 1, c, hs, hl, hnd, hr => by
      have hperm := ch.choose_perm c.k c.active
      cases hch : ch.choose c.k c.active with
      | nil =>
          rw [hch] at hperm
          have := hperm.length_eq
          simp only [List.length_nil] at this
          omega
      | cons p rest =>
          rw [hch] at hperm
          have hp : p < E.procs.size := hr p (hperm.mem_iff.mp (List.mem_cons_self ..))
          obtain ⟨q, hq⟩ := hP.total s hT p hp
          have hq' : E.next c.store p = .ok q := by rw [hs]; exact hq
          have hstep : step1 E ch c =
              .next { store := c.store, active := rest, nba := c.nba ++ q, k := c.k + 1 } := by
            unfold step1
            rw [hch]
            simp only [hq']
          have hnd' : (p :: rest).Nodup := hperm.nodup_iff.mpr hnd
          have hlen : rest.length = n := by
            have := hperm.length_eq
            simp only [List.length_cons] at this
            omega
          obtain ⟨ran, c', hran, hsteps, hs', ha', hn'⟩ := active_phase hP ch hT n
            { store := c.store, active := rest, nba := c.nba ++ q, k := c.k + 1 } hs hlen
            (List.nodup_cons.mp hnd').2
            (fun x hx => hr x (hperm.mem_iff.mp (List.mem_cons_of_mem _ hx)))
          refine ⟨p :: ran, c', (hran.cons p).trans hperm, .head hstep hsteps, hs', ha', ?_⟩
          rw [hn']
          simp [Elab1.queue, Elab1.upd, hq, List.append_assoc]

theorem isPosedge_self (b : Logic) : isPosedge b b = false := by cases b <;> rfl
theorem isNegedge_self (b : Logic) : isNegedge b b = false := by cases b <;> rfl

/-- **R-EDGE, edge fragment** (derived from E). In a slot whose ready set `act` is any set of edge
processes (an edge of their clock, or of their reset, fired them), from a store `s` with an empty
queue: EVERY process-atomic legal schedule closes the slot, and the closed store's view is the commit of every
ready process's updates computed on `s`, in index order. The result does not mention the
schedule: it is schedule-independent. -/
theorem rEdge {E : Elab1} (hP : EdgeProfile E) (ch : Choice) {s : Store} (hT : E.base.Typed s)
    {act : List ProcId} (hnd : act.Nodup) (hr : ∀ p ∈ act, p < E.procs.size) (k : Nat) :
    ∃ c', SlotCloses1 E ch { store := s, active := act, nba := [], k := k } c' ∧
      E.base.view c'.store = commitNba2 (E.base.view s) (E.queue s act) := by
  have hk : ((E.base.view s).map Prod.fst).Nodup := by rw [E.base.keys_view]; exact hP.nodup
  have hdisj : ∀ p p', p ≠ p' → ∀ u ∈ E.upd s p, ∀ u' ∈ E.upd s p', NbaDisj u u' := by
    intro p p' hne u hu u' hu'
    cases hq : E.next s p with
    | error m => simp [Elab1.upd, hq] at hu
    | ok q =>
        cases hq' : E.next s p' with
        | error m => simp [Elab1.upd, hq'] at hu'
        | ok q' =>
            simp only [Elab1.upd, hq] at hu
            simp only [Elab1.upd, hq'] at hu'
            exact hP.oneWriter s p p' q q' hne hq hq' u hu u' hu'
  obtain ⟨ran, c1, hran, hsteps, hs1, ha1, hn1⟩ :=
    active_phase hP ch hT act.length { store := s, active := act, nba := [], k := k } rfl rfl hnd hr
  have hcomm : commitNba2 (E.base.view s) (E.queue s ran) =
      commitNba2 (E.base.view s) (E.queue s act) :=
    commitNba2_perm hdisj hran (hran.nodup_iff.mpr hnd) hk
  have hnil : ∀ j, ch.choose j [] = [] := fun j => List.perm_nil.mp (ch.choose_perm j [])
  simp only [List.nil_append] at hn1
  cases hq : E.queue s ran with
  | nil =>
      refine ⟨c1, ⟨hsteps, ?_⟩, ?_⟩
      · unfold step1
        rw [ha1, hnil, hn1, hq]
      · rw [hs1, ← hcomm, hq]
        rfl
  | cons u us =>
      have hview : E.base.view (E.commit s (u :: us)) = commitNba2 (E.base.view s) (u :: us) :=
        Elab1.view_commit hP.four _ hT
      have htr : E.triggered (E.base.view s) (E.base.view (E.commit s (u :: us))) = [] := by
        unfold Elab1.triggered
        rw [List.filter_eq_nil_iff]
        intro p _
        cases hf : E.procs[p]? with
        | none => simp
        | some f =>
            have hnot : ∀ n, (n = f.clk ∨ f.rstn = some n) →
                SvState.lookup (E.base.view (E.commit s (u :: us))) n =
                  SvState.lookup (E.base.view s) n := by
              intro n hn
              rw [hview]
              refine lookup_commitNba2_of_not_mem _ _ fun x hx => ?_
              rw [← hq] at hx
              obtain ⟨p', q', hq', hx'⟩ := Elab1.mem_queue hx
              obtain ⟨hc, hrs⟩ := hP.noEdge s p' q' hq' x hx' f (Elab1.mem_procs hf)
              rcases hn with h | h
              · subst h; exact hc
              · exact fun hx => hrs (by rw [h, hx])
            have hclk : SvState.bit0 (E.base.view (E.commit s (u :: us))) f.clk =
                SvState.bit0 (E.base.view s) f.clk := by
              simp only [SvState.bit0, hnot f.clk (Or.inl rfl)]
            have hreset :
                (match f.rstn with
                 | some r => isNegedge (SvState.bit0 (E.base.view s) r)
                     (SvState.bit0 (E.base.view (E.commit s (u :: us))) r)
                 | none => false) = false := by
              cases hrn : f.rstn with
              | none => rfl
              | some r =>
                  have hr' : SvState.bit0 (E.base.view (E.commit s (u :: us))) r =
                      SvState.bit0 (E.base.view s) r := by
                    simp only [SvState.bit0, hnot r (Or.inr hrn)]
                  simp [hr', isNegedge_self]
            cases fe : f.edge with
            | posedge => simp [FF.fires, fe, hclk, hreset, isPosedge_self]
            | negedge => simp [FF.fires, fe, hclk, hreset, isNegedge_self]
      have hstep : step1 E ch c1 =
          .next { store := E.commit c1.store (u :: us), active := [], nba := [], k := c1.k + 1 } := by
        unfold step1
        rw [ha1, hnil, hn1, hq]
        simp only [hs1, htr]
      refine ⟨_, ⟨hsteps.tail hstep, ?_⟩, ?_⟩
      · unfold step1
        simp only [hnil]
      · simp only [hs1]
        rw [hview, ← hcomm, hq]

/-! ## Fixtures: an asynchronously reset counter, and an NBA swap -/

namespace Core1Smoke

/-- `always_ff @(posedge clk or negedge rst_n) if (!rst_n) q <= 0; else q <= q + 1;` -/
def cnt : Elab1 where
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst_n", width := 1, isInput := true }, { name := "q", width := 4 }]
  procs := #[{ clk := "clk", rstn := some "rst_n",
               body := .ifStmt (.unary .lnot (.ident "rst_n"))
                 (.nbaAssign (.ident "q") (.lit (.ofNat 4 0)))
                 (some (.nbaAssign (.ident "q") (.binary .add (.ident "q") (.lit (.ofNat 4 1))))) }]

/-- Two edge processes on one clock: `a <= b` and `b <= a` (the blocking version is Core0's
`swap`, which closes at two different stores). -/
def nbaSwap : Elab1 where
  decls := #[{ name := "clk", width := 1, isInput := true }, { name := "a", width := 4 },
             { name := "b", width := 4 }]
  procs := #[{ clk := "clk", rstn := none, body := .nbaAssign (.ident "a") (.ident "b") },
             { clk := "clk", rstn := none, body := .nbaAssign (.ident "b") (.ident "a") }]

theorem cnt_profile : EdgeProfile cnt :=
  EdgeProfile.ofChecks (by unfold AllFour; decide) (by decide) rfl rfl rfl

theorem nbaSwap_profile : EdgeProfile nbaSwap :=
  EdgeProfile.ofChecks (by unfold AllFour; decide) (by decide) rfl rfl rfl

/-- **R-EDGE on the NBA swap** (non-vacuity): with both processes ready, every process-atomic legal schedule
closes the slot at the same store, the commit of both updates computed on the pre-state. -/
theorem nbaSwap_rEdge (ch : Choice) {s : Store} (hT : nbaSwap.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 nbaSwap ch { store := s, active := [0, 1], nba := [], k := k } c' ∧
      nbaSwap.base.view c'.store =
        commitNba2 (nbaSwap.base.view s) (nbaSwap.queue s [0, 1]) :=
  rEdge nbaSwap_profile ch hT (by decide) (by decide) k

/-- **R-EDGE on the counter** (non-vacuity). -/
theorem cnt_rEdge (ch : Choice) {s : Store} (hT : cnt.base.Typed s) (k : Nat) :
    ∃ c', SlotCloses1 cnt ch { store := s, active := [0], nba := [], k := k } c' ∧
      cnt.base.view c'.store = commitNba2 (cnt.base.view s) (cnt.queue s [0]) :=
  rEdge cnt_profile ch hT (by decide) (by decide) k

/-! The executable rows (MEASURED). -/

def show1 (E : Elab1) (names : List String) : ExecResult1 → Option (List String)
  | .closed c => some (names.map (SvState.showSignal (E.base.view c.store)))
  | _ => none

/-- The refusal text, if the run refused. -/
def refusal1 : ExecResult1 → Option String
  | .refused m => some m
  | _ => none

/-- An `always_ff` with a blocking assignment, still outside E-core-1. -/
def ffBlocking : Elab1 where
  decls := cnt.decls
  procs := #[⟨"clk", none, .blockingAssign (.ident "q") (.lit (.ofNat 4 0)), .posedge⟩]

def ffCase : Elab1 where
  decls := cnt.decls
  procs := #[⟨"clk", none, .caseStmt (.ident "q") #[] none .normal .none, .posedge⟩]

/-- A closed configuration at `clk = 0` with the given stores, then a slot with `entry`. -/
def openSlot (E : Elab1) (init : List (String × LVec)) (entry : SvState) : Config1 :=
  Config1.nextSlot E
    { store := init.foldl (fun s nv => E.base.setName s nv.1 nv.2) E.base.initStore, active := [],
      nba := [] } entry

-- `a = 3, b = 5`, then a rising clock: both orders swap.
#guard show1 nbaSwap ["a", "b"] (exec1 nbaSwap σ_src 10
    (openSlot nbaSwap [("clk", .ofNat 1 0), ("a", .ofNat 4 3), ("b", .ofNat 4 5)] [("clk", .ofNat 1 1)]))
  == some ["0101", "0011"]
#guard show1 nbaSwap ["a", "b"] (exec1 nbaSwap σ_rev 10
    (openSlot nbaSwap [("clk", .ofNat 1 0), ("a", .ofNat 4 3), ("b", .ofNat 4 5)] [("clk", .ofNat 1 1)]))
  == some ["0101", "0011"]
-- `q = 7` out of reset, a rising clock: `q = 8`.
#guard show1 cnt ["q"] (exec1 cnt σ_src 10
    (openSlot cnt [("clk", .ofNat 1 0), ("rst_n", .ofNat 1 1), ("q", .ofNat 4 7)] [("clk", .ofNat 1 1)]))
  == some ["1000"]
-- `q = 7`, the reset falls with the clock low: the asynchronous reset fires, `q = 0`.
#guard show1 cnt ["q"] (exec1 cnt σ_src 10
    (openSlot cnt [("clk", .ofNat 1 0), ("rst_n", .ofNat 1 1), ("q", .ofNat 4 7)] [("rst_n", .ofNat 1 0)]))
  == some ["0000"]
-- `q = 7`, the clock falls: nothing fires, `q` holds.
#guard show1 cnt ["q"] (exec1 cnt σ_src 10
    (openSlot cnt [("clk", .ofNat 1 1), ("rst_n", .ofNat 1 1), ("q", .ofNat 4 7)] [("clk", .ofNat 1 0)]))
  == some ["0111"]

/-! The async-reset edge table is observable in E, independently of the
clocked body. A reset assertion wakes the process with the clock held low;
release does not, and the IEEE unknown transitions `1→x` and `x→0` do. A
clock edge still wakes the process while reset is asserted. -/
private def edgeState (clk rst : Logic) : SvState :=
  [("clk", LVec.ofLogic clk), ("rst_n", LVec.ofLogic rst)]

#guard cnt.procs[0]?.map (fun f =>
    f.fires (edgeState .l0 .l1) (edgeState .l0 .l0)) == some true
#guard cnt.procs[0]?.map (fun f =>
    f.fires (edgeState .l0 .l0) (edgeState .l0 .l1)) == some false
#guard cnt.procs[0]?.map (fun f =>
    f.fires (edgeState .l0 .l1) (edgeState .l0 .lx)) == some true
#guard cnt.procs[0]?.map (fun f =>
    f.fires (edgeState .l0 .lx) (edgeState .l0 .l0)) == some true
#guard cnt.procs[0]?.map (fun f =>
    f.fires (edgeState .l0 .l0) (edgeState .l1 .l0)) == some true

private def negClock : FF :=
  { clk := "clk", rstn := none, edge := .negedge,
    body := .nbaAssign (.ident "q") (.lit (.ofNat 1 1)) }

#guard negClock.fires (edgeState .l1 .l1) (edgeState .l0 .l1) == true
#guard negClock.fires (edgeState .l0 .l1) (edgeState .l1 .l1) == false

-- A 1→x reset edge runs the whole body, so the released data path is taken;
-- release from x→1 is not itself a reset event.
#guard show1 cnt ["q"] (exec1 cnt σ_src 10
    (openSlot cnt [("clk", .ofNat 1 0), ("rst_n", .ofNat 1 1), ("q", .ofNat 4 7)]
      [("rst_n", .ofLogic .lx)])) == some ["1000"]
#guard show1 cnt ["q"] (exec1 cnt σ_src 10
    (openSlot cnt [("clk", .ofNat 1 0), ("rst_n", .ofLogic .lx), ("q", .ofNat 4 7)]
      [("rst_n", .ofLogic .l1)])) == some ["0111"]

-- Refusals are loud and cite their clause; they are not an exhausted budget.
#guard (refusal1 (exec1 ffBlocking σ_src 10 (openSlot ffBlocking [("clk", .ofNat 1 0)]
    [("clk", .ofNat 1 1)]))).map (·.startsWith "9.2.2.4:") == some true
-- An empty unqualified case without a default is a successful no-op (§12.5).
#guard show1 ffCase ["clk"] (exec1 ffCase σ_src 10
    (openSlot ffCase [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)])) == some ["1"]
#guard ffCase.okB
-- Wildcard cases share the walk; inside and qualified cases remain loud.
#guard (.caseStmt (.ident "q") #[] none .casez .none : Stmt2).ffOkB cnt.design
#guard (.caseStmt (.ident "q") #[] none .casex .none : Stmt2).ffOkB cnt.design
#guard !(.caseStmt (.ident "q") #[] none .inside .none : Stmt2).ffOkB cnt.design
#guard !(.caseStmt (.ident "q") #[] none .normal .unique : Stmt2).ffOkB cnt.design
#guard match execFF cnt.design [] (.caseStmt (.lit (.ofNat 1 0)) #[] none .inside .none) with
  | .error msg => msg.startsWith "12.5:"
  | .ok _ => false
#guard match execFF cnt.design [] (.caseStmt (.lit (.ofNat 1 0)) #[] none .normal .priority) with
  | .error msg => msg.startsWith "12.5:"
  | .ok _ => false

end Core1Smoke

/-! ## Axioms -/

#print axioms nbaStep_comm
#print axioms commitNba2_perm
#print axioms execFF_mem
#print axioms execFF_total
#print axioms execFFArm_mem
#print axioms execFFCase_mem
#print axioms execFFArm_total
#print axioms execFFCase_total
#print axioms Elab1.view_commit
#print axioms EdgeProfile.ofChecks
#print axioms active_phase
#print axioms rEdge
#print axioms exec1_sound
#print axioms Core1Smoke.cnt_profile
#print axioms Core1Smoke.nbaSwap_profile
#print axioms Core1Smoke.nbaSwap_rEdge
#print axioms Core1Smoke.cnt_rEdge

end LeanModels.Sv.Kernel
