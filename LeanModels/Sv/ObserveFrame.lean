import LeanModels.Sv.Observe
import LeanModels.Sv.Comb2Base

/-!
# The input frame of `run2`: a design that writes no input port shows its stimulus in the pre sample

**Status: provisional over `run2`** (library, never trusted). Imported by nothing in the tree; the
svGolf drafts under `svgolf/design/architecture/` use it.

The trusted convention reads inputs from the pre sample (ruling (a), 2026-11-02), so statements
carry a receptiveness conjunct. Golfers must never prove it by hand (lead's steer, Day 5). This
module is the one library theorem it rests on:

* `Design2.writesInput d`: does some process write some input port? A syntactic, decidable
  check: an assignment target names the port. The loader refuses a design that drives its own input
  (register row `le-driver-input`), so it is `false`, by `decide`/`rfl`, for every admitted design.
* `exec_frame`: one fuel induction over `execStmt2`/`execCase2`/`execStmts2`. A statement that
  writes no target named `n` leaves `n`'s binding unchanged and queues no NBA to `n`. It lifts
  through `runCombProcess2`, `combPass2`, `combSettle2`, `resetPass2`, `commitNba2`, `resetPhase2`
  to `cyclePre2_lookup_input`: in the pre sample, an input reads what `applyInputs2` gave it.
* `Obs_run2.pre_input`: in every completed run of such a design, the pre sample of cycle `c` holds
  every input the stimulus entry `c` binds at a known value. This one lemma gives both
  `EntryInPre` and receptiveness (`ObsComb.lean`).

The frame is name-level (no bit windows, no state shape). The bit-level frame of
`CombGuard2Sound.lean` (`sim`) needs shaped states and is about one comb body; this one needs
neither.
-/

namespace LeanModels.Sv

/-! ## Which names a process writes (syntactic, decidable) -/

mutual
/-- Does an assignment target write the signal `n` (as the whole target, a slice, an element, or a
leaf of a concatenation)? Index expressions are reads, not writes. -/
def Lhs2.writesName (n : String) : Lhs2 → Bool
  | .ident m => m == n
  | .slice m _ _ => m == n
  | .index m _ _ => m == n
  | .concat ps => Lhs2.writesNameList n ps
termination_by structural t => t

def Lhs2.writesNameList (n : String) : List Lhs2 → Bool
  | [] => false
  | t :: ts => t.writesName n || Lhs2.writesNameList n ts
termination_by structural ts => ts
end

mutual
/-- Does a statement contain an assignment (blocking or nonblocking) whose target writes `n`? -/
def Stmt2.writesName (n : String) : Stmt2 → Bool
  | .blockingAssign t _ | .nbaAssign t _ => t.writesName n
  | .ifStmt _ t e => t.writesName n || Stmt2.writesNameOpt n e
  | .block body => Stmt2.writesNameList n body.toList
  | .caseStmt _ items dflt _ _ => CaseItem2.writesNameList n items.toList || Stmt2.writesNameOpt n dflt
  | .unsupported _ _ => false
termination_by structural s => s

def Stmt2.writesNameOpt (n : String) : Option Stmt2 → Bool
  | none => false
  | some s => s.writesName n
termination_by structural o => o

def Stmt2.writesNameList (n : String) : List Stmt2 → Bool
  | [] => false
  | s :: ss => s.writesName n || Stmt2.writesNameList n ss
termination_by structural ss => ss

def CaseItem2.writesName (n : String) : CaseItem2 → Bool
  | .mk _ body => body.writesName n
termination_by structural it => it

def CaseItem2.writesNameList (n : String) : List CaseItem2 → Bool
  | [] => false
  | it :: rest => it.writesName n || CaseItem2.writesNameList n rest
termination_by structural its => its
end

/-- Does a process write `n`? -/
def Process2.writesName (n : String) : Process2 → Bool
  | .assign t _ => t.writesName n
  | .alwaysComb b | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ => b.writesName n
  | .unsupported _ _ => false

/-- **Does some process write some input port?** Decidable and syntactic. It is `false` for every
design the loader admits, which refuses a design that drives its own input (`le-driver-input`). -/
def Design2.writesInput (d : Design2) : Bool :=
  d.processes.toList.any fun p => d.inputNames.toList.any fun n => p.writesName n

theorem Design2.writesName_of_writesInput {d : Design2} (hd : d.writesInput = false)
    {p : Process2} (hp : p ∈ d.processes.toList) {n : String} (hn : n ∈ d.inputNames.toList) :
    p.writesName n = false := by
  unfold Design2.writesInput at hd
  rw [List.any_eq_false] at hd
  have := hd p hp
  rw [Bool.not_eq_true, List.any_eq_false] at this
  simpa using this n hn

/-! ## Targets -/

theorem Lhs2.writesNameList_of_mem {n : String} :
    ∀ {ps : List Lhs2} {p : Lhs2}, p ∈ ps → p.writesName n = true →
      Lhs2.writesNameList n ps = true
  | _ :: _, _, .head _, h => by simp [Lhs2.writesNameList, h]
  | _ :: _, _, .tail _ hm, h => by
      simp [Lhs2.writesNameList, Lhs2.writesNameList_of_mem hm h]

/-- A resolved (non-concatenated) target names a signal it writes. -/
theorem resolveLhs2_writes {fuel : Nat} {st : SvState} {t : Lhs2} {m : String}
    {w : Option (Nat × Nat)} (h : resolveLhs2 fuel st t = .ok (m, w)) : t.writesName m = true := by
  cases t with
  | ident n =>
      simp only [resolveLhs2] at h
      cases hl : SvState.lookup st n <;> rw [hl] at h <;> simp at h
      obtain ⟨rfl, -⟩ := h
      simp [Lhs2.writesName]
  | slice n lo w' =>
      simp only [resolveLhs2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [Lhs2.writesName]
  | index n idx ew =>
      simp only [resolveLhs2, Res.bind_eq_ok] at h
      obtain ⟨iv, -, h⟩ := h
      have hmn : m = n := by
        revert h
        cases SvState.lookup st n with
        | none => simp
        | some old =>
            cases hidx : indexInt? idx iv with
            | none => simp [hidx]; exact fun h _ => h.symm
            | some i =>
                simp [hidx]
                split <;> simp <;> exact fun h _ => h.symm
      subst hmn
      simp [Lhs2.writesName]
  | concat ps => simp [resolveLhs2] at h

/-- The windows a concatenation's leaf fold collects come from its leaves. -/
theorem foldlM_append_mem {α β : Type} {g : α → Res (List β)} :
    ∀ (l : List α) (acc ws : List β),
      l.foldlM (fun acc part => do let w ← g part; pure (acc ++ w)) acc = .ok ws →
      ∀ x ∈ ws, x ∈ acc ∨ ∃ p ∈ l, ∃ w, g p = .ok w ∧ x ∈ w
  | [], acc, ws, h => by
      simp only [List.foldlM] at h
      cases h
      exact fun x hx => Or.inl hx
  | p :: ps, acc, ws, h => by
      simp only [List.foldlM] at h
      cases hg : g p with
      | ok w =>
        rw [hg] at h
        simp only [Res.ok_bind, Res.pure_eq] at h
        intro x hx
        rcases foldlM_append_mem ps (acc ++ w) ws h x hx with h1 | ⟨q, hq, w', hw', hx'⟩
        · rcases List.mem_append.mp h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨p, List.mem_cons_self .., w, hg, h1⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, w', hw', hx'⟩
      | timeout => rw [hg] at h; simp at h
      | unsupported m => rw [hg] at h; simp at h

/-- Every window a resolved concatenation returns names a signal the target writes. -/
theorem resolveConcatLhs2_writes {fuel : Nat} {st : SvState} :
    ∀ (t : Lhs2) (ws : List (String × Nat × Nat)), resolveConcatLhs2 fuel st t = .ok ws →
      ∀ x ∈ ws, t.writesName x.1 = true
  | .concat parts, ws, h => by
      rw [resolveConcatLhs2.eq_1] at h
      intro x hx
      rcases foldlM_append_mem parts [] ws h x hx with h1 | ⟨part, hpart, w, hw, hxw⟩
      · exact absurd h1 List.not_mem_nil
      · simp only [Lhs2.writesName]
        exact Lhs2.writesNameList_of_mem hpart (resolveConcatLhs2_writes part w hw x hxw)
  | .ident n, ws, h => by
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      cases win with
      | none => simp at h
      | some lw =>
        simp only [Res.pure_eq, Res.ok.injEq] at h
        subst h
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact resolveLhs2_writes hres
  | .slice n lo w, ws, h => by
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      cases win with
      | none => simp at h
      | some lw =>
        simp only [Res.pure_eq, Res.ok.injEq] at h
        subst h
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact resolveLhs2_writes hres
  | .index n idx ew, ws, h => by
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      cases win with
      | none => simp at h
      | some lw =>
        simp only [Res.pure_eq, Res.ok.injEq] at h
        subst h
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact resolveLhs2_writes hres
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem hpart
  simp_wf
  omega

/-- A concatenation write touches only its windows' names. -/
theorem writeConcatLhs2_go_lookup (repl : LVec) (n : String) :
    ∀ (s : SvState) (rem : List (String × Nat × Nat)) (wd : Nat) (s' : SvState),
      writeConcatLhs2.go repl s rem wd = .ok s' → (∀ x ∈ rem, x.1 ≠ n) →
      SvState.lookup s' n = SvState.lookup s n
  | s, [], _, s', h, _ => by
      rw [writeConcatLhs2.go.eq_1] at h
      cases h; rfl
  | s, (m, lo, w) :: rest, wd, s', h, hn => by
      rw [writeConcatLhs2.go.eq_2] at h
      cases hl : SvState.lookup s m with
      | none => rw [hl] at h; cases h
      | some old =>
          rw [hl] at h
          rw [writeConcatLhs2_go_lookup repl n _ rest _ s' h
            (fun x hx => hn x (List.mem_cons_of_mem _ hx))]
          exact SvState.lookup_set_ne s _ (hn (m, lo, w) (List.mem_cons_self ..))

theorem writeConcatLhs2_lookup {st : SvState} {v : LVec} {ws : List (String × Nat × Nat)}
    {st' : SvState} {n : String} (h : writeConcatLhs2 st v ws = .ok st')
    (hn : ∀ x ∈ ws, x.1 ≠ n) : SvState.lookup st' n = SvState.lookup st n := by
  unfold writeConcatLhs2 at h
  exact writeConcatLhs2_go_lookup _ n st ws _ st' h hn

/-! ## The frame of the statement interpreter -/

/-- What a statement run preserves about a name `n` it does not write: `n`'s binding, and "no
queued NBA targets `n`". -/
def KeepsName (n : String) (st st' : SvState) (nba' : NbaQueue2) : Prop :=
  SvState.lookup st' n = SvState.lookup st n ∧ ∀ x ∈ nba', x.1 ≠ n

theorem KeepsName.trans {n : String} {st st' st'' : SvState} {nba' nba'' : NbaQueue2}
    (h1 : KeepsName n st st' nba') (h2 : KeepsName n st' st'' nba'') : KeepsName n st st'' nba'' :=
  ⟨h2.1.trans h1.1, h2.2⟩

/-- **The frame of `execStmt2`/`execCase2`/`execStmts2`**: one fuel induction. A statement that
writes no target named `n`, run from a queue with no NBA to `n`, leaves `n`'s binding unchanged and
queues no NBA to `n`. -/
theorem exec_frame (n : String) (fuel : Nat) :
    (∀ (st : SvState) (nba : NbaQueue2) (s : Stmt2) (st' : SvState) (nba' : NbaQueue2),
      execStmt2 fuel st nba s = .ok (st', nba') → s.writesName n = false →
      (∀ x ∈ nba, x.1 ≠ n) → KeepsName n st st' nba') ∧
    (∀ (st : SvState) (nba : NbaQueue2) (subj : LVec) (items : List CaseItem2)
        (dflt : Option Stmt2) (mode : CaseMode) (st' : SvState) (nba' : NbaQueue2),
      execCase2 fuel st nba subj items dflt mode = .ok (st', nba') →
      CaseItem2.writesNameList n items = false → Stmt2.writesNameOpt n dflt = false →
      (∀ x ∈ nba, x.1 ≠ n) → KeepsName n st st' nba') ∧
    (∀ (st : SvState) (nba : NbaQueue2) (ss : List Stmt2) (st' : SvState) (nba' : NbaQueue2),
      execStmts2 fuel st nba ss = .ok (st', nba') → Stmt2.writesNameList n ss = false →
      (∀ x ∈ nba, x.1 ≠ n) → KeepsName n st st' nba') := by
  induction fuel with
  | zero =>
    refine ⟨fun st nba s st' nba' h => by simp [execStmt2] at h, ?_,
      fun st nba ss st' nba' h => by simp [execStmts2] at h⟩
    intro st nba subj items dflt mode st' nba' h
    cases items with
    | nil => simp [execCase2] at h
    | cons it rest => cases it; simp [execCase2] at h
  | succ fuel ih =>
    obtain ⟨ihS, ihC, ihSs⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- execStmt2
    · intro st nba s st' nba' h hw hq
      cases s with
      | blockingAssign target value =>
          simp only [Stmt2.writesName] at hw
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨v, -, h⟩ := h
          cases target with
          | concat parts =>
              simp only [Res.bind_eq_ok] at h
              obtain ⟨ws, hws, st2, hst2, h⟩ := h
              simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨writeConcatLhs2_lookup hst2 fun x hx hxn => ?_, hq⟩
              have := resolveConcatLhs2_writes _ ws hws x hx
              rw [hxn, hw] at this
              cases this
          | ident m =>
              simp only [Res.bind_eq_ok] at h
              obtain ⟨⟨m', win⟩, hres, h⟩ := h
              have hm' : m' ≠ n := fun hmn => by
                have := resolveLhs2_writes hres; rw [hmn, hw] at this; cases this
              cases win with
              | none =>
                  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
              | some lw =>
                  obtain ⟨lo, w⟩ := lw
                  simp only at h
                  cases hl : SvState.lookup st m' with
                  | none => rw [hl] at h; simp at h
                  | some old =>
                      rw [hl] at h
                      simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨SvState.lookup_set_ne st _ hm', hq⟩
          | slice m lo' w' =>
              simp only [Res.bind_eq_ok] at h
              obtain ⟨⟨m', win⟩, hres, h⟩ := h
              have hm' : m' ≠ n := fun hmn => by
                have := resolveLhs2_writes hres; rw [hmn, hw] at this; cases this
              cases win with
              | none =>
                  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
              | some lw =>
                  obtain ⟨lo, w⟩ := lw
                  simp only at h
                  cases hl : SvState.lookup st m' with
                  | none => rw [hl] at h; simp at h
                  | some old =>
                      rw [hl] at h
                      simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨SvState.lookup_set_ne st _ hm', hq⟩
          | index m idx ew =>
              simp only [Res.bind_eq_ok] at h
              obtain ⟨⟨m', win⟩, hres, h⟩ := h
              have hm' : m' ≠ n := fun hmn => by
                have := resolveLhs2_writes hres; rw [hmn, hw] at this; cases this
              cases win with
              | none =>
                  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
              | some lw =>
                  obtain ⟨lo, w⟩ := lw
                  simp only at h
                  cases hl : SvState.lookup st m' with
                  | none => rw [hl] at h; simp at h
                  | some old =>
                      rw [hl] at h
                      simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨SvState.lookup_set_ne st _ hm', hq⟩
      | nbaAssign target value =>
          simp only [Stmt2.writesName] at hw
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨v, -, ⟨m', win⟩, hres, h⟩ := h
          have hm' : m' ≠ n := fun hmn => by
            have := resolveLhs2_writes hres; rw [hmn, hw] at this; cases this
          cases win with
          | none =>
              simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
          | some lw =>
              obtain ⟨lo, w⟩ := lw
              simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, fun x hx => ?_⟩
              rcases List.mem_append.mp hx with hx | hx
              · exact hq x hx
              · simp only [List.mem_singleton] at hx; subst hx; exact hm'
      | ifStmt cond thenB elseB =>
          simp only [Stmt2.writesName, Bool.or_eq_false_iff] at hw
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨c, -, h⟩ := h
          split at h
          · exact ihS st nba thenB st' nba' h hw.1 hq
          · cases elseB with
            | none =>
                simp only [Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
            | some s =>
                simp only [Stmt2.writesNameOpt] at hw
                exact ihS st nba s st' nba' h hw.2 hq
      | caseStmt subject items dflt mode check =>
          simp only [Stmt2.writesName, Bool.or_eq_false_iff] at hw
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨sv, -, h⟩ := h
          exact ihC st nba sv items.toList dflt mode st' nba' h hw.1 hw.2 hq
      | block body =>
          simp only [Stmt2.writesName] at hw
          simp only [execStmt2] at h
          exact ihSs st nba body.toList st' nba' h hw hq
      | unsupported svKind text => simp [execStmt2] at h
    -- execCase2
    · intro st nba subj items dflt mode st' nba' h hw hd hq
      cases items with
      | nil =>
          cases dflt with
          | none =>
              simp only [execCase2, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
          | some s =>
              simp only [Stmt2.writesNameOpt] at hd
              simp only [execCase2] at h
              exact ihS st nba s st' nba' h hd hq
      | cons it rest =>
          obtain ⟨pats, body⟩ := it
          simp only [CaseItem2.writesNameList, CaseItem2.writesName, Bool.or_eq_false_iff] at hw
          simp only [execCase2, Res.bind_eq_ok] at h
          obtain ⟨pvs, -, h⟩ := h
          split at h
          · exact ihS st nba body st' nba' h hw.1 hq
          · exact ihC st nba subj rest dflt mode st' nba' h hw.2 hd hq
    -- execStmts2
    · intro st nba ss st' nba' h hw hq
      cases ss with
      | nil =>
          simp only [execStmts2, Res.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
      | cons s rest =>
          simp only [Stmt2.writesNameList, Bool.or_eq_false_iff] at hw
          simp only [execStmts2, Res.bind_eq_ok] at h
          obtain ⟨⟨st1, nba1⟩, h1, h2⟩ := h
          have k1 := ihS st nba s st1 nba1 h1 hw.1 hq
          exact k1.trans (ihSs st1 nba1 rest st' nba' h2 hw.2 k1.2)

/-! ## Lifting the frame to the cycle -/

theorem commitNba2_lookup (n : String) :
    ∀ (st : SvState) (nba : NbaQueue2), (∀ x ∈ nba, x.1 ≠ n) →
      SvState.lookup (commitNba2 st nba) n = SvState.lookup st n
  | _, [], _ => rfl
  | st, (m, lo, v) :: rest, h => by
      have hm : m ≠ n := h (m, lo, v) (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, x.1 ≠ n := fun x hx => h x (List.mem_cons_of_mem _ hx)
      cases hl : SvState.lookup st m with
      | none =>
          have : commitNba2 st ((m, lo, v) :: rest) = commitNba2 st rest := by
            simp [commitNba2, List.foldl_cons, hl]
          rw [this, commitNba2_lookup n st rest hrest]
      | some old =>
          have : commitNba2 st ((m, lo, v) :: rest) =
              commitNba2 (SvState.set st m (old.insertAt lo v)) rest := by
            simp [commitNba2, List.foldl_cons, hl]
          rw [this, commitNba2_lookup n _ rest hrest]
          exact SvState.lookup_set_ne st _ hm

theorem runCombProcess2_lookup {fuel : Nat} {st st' : SvState} {p : Process2} {n : String}
    (h : runCombProcess2 fuel st p = .ok st') (hw : p.writesName n = false) :
    SvState.lookup st' n = SvState.lookup st n := by
  cases p with
  | assign target value =>
      simp only [Process2.writesName] at hw
      simp only [runCombProcess2, Res.bind_eq_ok] at h
      obtain ⟨v, -, h⟩ := h
      cases target with
      | concat parts =>
          simp only [Res.bind_eq_ok] at h
          obtain ⟨ws, hws, h⟩ := h
          refine writeConcatLhs2_lookup h fun x hx hxn => ?_
          have := resolveConcatLhs2_writes _ ws hws x hx
          rw [hxn, hw] at this
          cases this
      | ident m | slice m _ _ | index m _ _ =>
          simp only [Res.bind_eq_ok] at h
          obtain ⟨⟨m', win⟩, hres, h⟩ := h
          have hm' : m' ≠ n := fun hmn => by
            have := resolveLhs2_writes hres; rw [hmn, hw] at this; cases this
          cases win with
          | none => simp only [Res.ok.injEq] at h; subst h; rfl
          | some lw =>
              obtain ⟨lo, w⟩ := lw
              simp only at h
              cases hl : SvState.lookup st m' with
              | none => rw [hl] at h; simp at h
              | some old =>
                  rw [hl] at h
                  simp only [Res.ok.injEq] at h
                  subst h
                  exact SvState.lookup_set_ne st _ hm'
  | alwaysComb body =>
      simp only [Process2.writesName] at hw
      simp only [runCombProcess2, Res.bind_eq_ok] at h
      obtain ⟨⟨st1, nba⟩, h1, h⟩ := h
      cases nba with
      | nil =>
          simp only [Res.ok.injEq] at h
          subst h
          exact ((exec_frame n fuel).1 st [] body st1 [] h1 hw (by simp)).1
      | cons _ _ => simp at h
  | alwaysFF _ _ | alwaysPlain _ _ | alwaysFFR _ _ _ _ =>
      simp only [runCombProcess2, Res.ok.injEq] at h
      subst h; rfl
  | unsupported _ _ => simp [runCombProcess2] at h

/-- A process that `combPass2` runs is one of the design's. -/
theorem mem_of_getElem? {d : Design2} {i : Nat} {p : Process2} (h : d.processes[i]? = some p) :
    p ∈ d.processes.toList := by
  rw [Array.mem_toList_iff]
  exact Array.mem_of_getElem? h

theorem combPass2_lookup {d : Design2} {fuel : Nat} {n : String}
    (hw : ∀ p ∈ d.processes.toList, p.writesName n = false) :
    ∀ (is : List Nat) (st st' : SvState), combPass2 d fuel st is = .ok st' →
      SvState.lookup st' n = SvState.lookup st n
  | [], st, st', h => by simp only [combPass2, Res.ok.injEq] at h; subst h; rfl
  | i :: rest, st, st', h => by
      simp only [combPass2] at h
      cases hp : d.processes[i]? with
      | none =>
          rw [hp] at h
          simp only [Res.pure_eq, Res.ok_bind] at h
          exact combPass2_lookup hw rest st st' h
      | some p =>
          rw [hp] at h
          simp only [Res.bind_eq_ok] at h
          obtain ⟨st1, h1, h2⟩ := h
          rw [combPass2_lookup hw rest st1 st' h2]
          exact runCombProcess2_lookup h1 (hw p (mem_of_getElem? hp))

theorem combSettle2_lookup {d : Design2} {σ : ScheduleOracle} {n : String}
    (hw : ∀ p ∈ d.processes.toList, p.writesName n = false) :
    ∀ (fuel : Nat) (st : SvState) (k : Nat) (st' : SvState) (k' : Nat),
      combSettle2 d σ fuel st k = .ok (st', k') → SvState.lookup st' n = SvState.lookup st n
  | 0, _, _, _, _, h => by simp [combSettle2] at h
  | fuel + 1, st, k, st', k', h => by
      unfold combSettle2 at h
      simp only [Res.bind_eq_ok] at h
      obtain ⟨t, ht, h⟩ := h
      have h1 := combPass2_lookup hw _ st t ht
      split at h
      · simp only [Res.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact h1
      · rw [combSettle2_lookup hw fuel t (k + 1) st' k' h, h1]

theorem resetPass2_lookup {d : Design2} {fuel : Nat} {n : String}
    (hw : ∀ p ∈ d.processes.toList, p.writesName n = false) :
    ∀ (is : List Nat) (st : SvState) (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      resetPass2 d fuel st nba is = .ok (st', nba') → (∀ x ∈ nba, x.1 ≠ n) →
      KeepsName n st st' nba'
  | [], st, nba, st', nba', h, hq => by
      simp only [resetPass2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hq⟩
  | i :: rest, st, nba, st', nba', h, hq => by
      simp only [resetPass2] at h
      cases hp : d.processes[i]? with
      | none =>
          rw [hp] at h
          simp only [Res.pure_eq, Res.ok_bind] at h
          exact resetPass2_lookup hw rest st nba st' nba' h hq
      | some p =>
          rw [hp] at h
          simp only [Res.bind_eq_ok] at h
          obtain ⟨⟨st1, nba1⟩, h1, h2⟩ := h
          have hpw := hw p (mem_of_getElem? hp)
          have k1 : KeepsName n st st1 nba1 := by
            cases p with
            | alwaysFFR _ _ body =>
                simp only [Process2.writesName] at hpw
                simp only [runResetProcess2] at h1
                exact (exec_frame n fuel).1 st nba body st1 nba1 h1 hpw hq
            | alwaysFF _ _ | alwaysPlain _ _ | alwaysComb _ | assign _ _ | unsupported _ _ =>
                simp only [runResetProcess2, Res.ok.injEq, Prod.mk.injEq] at h1
                obtain ⟨rfl, rfl⟩ := h1; exact ⟨rfl, hq⟩
          exact k1.trans (resetPass2_lookup hw rest st1 nba1 st' nba' h2 k1.2)

open Observe in
theorem resetPhase2_lookup {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {prev st1 : SvState}
    {k1 : Nat} {pre : SvState} {k2 : Nat} {n : String}
    (hw : ∀ p ∈ d.processes.toList, p.writesName n = false)
    (h : resetPhase2 d σ fuel prev st1 k1 = .ok (pre, k2)) :
    SvState.lookup pre n = SvState.lookup st1 n := by
  by_cases hn : d.resetIndices prev st1 = []
  · rw [resetPhase2_of_nil hn] at h
    simp only [Res.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  · rw [resetPhase2_of_ne_nil hn, Res.bind_eq_ok] at h
    obtain ⟨⟨str, nbar⟩, hr, hs⟩ := h
    have k1 := resetPass2_lookup hw _ st1 [] str nbar hr (by simp)
    rw [combSettle2_lookup hw _ _ _ _ _ hs, commitNba2_lookup n str nbar k1.2, k1.1]

open Observe in
/-- **The input frame of a cycle**: in a design that writes no input port, the pre sample holds each
input as `applyInputs2` left it. -/
theorem cyclePre2_lookup_input {d : Design2} (hd : d.writesInput = false) {σ : ScheduleOracle}
    {fuel : Nat} {inputs st : SvState} {k : Nat} {pre : SvState} {k2 : Nat}
    (h : cyclePre2 d σ fuel inputs st k = .ok (pre, k2)) {n : String}
    (hn : n ∈ d.inputNames.toList) :
    SvState.lookup pre n = SvState.lookup (applyInputs2 d inputs st) n := by
  have hw : ∀ p ∈ d.processes.toList, p.writesName n = false :=
    fun p hp => Design2.writesName_of_writesInput hd hp hn
  unfold cyclePre2 at h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨⟨st1, k1⟩, h1, h2⟩ := h
  rw [resetPhase2_lookup hw h2, combSettle2_lookup hw _ _ _ _ _ h1]

/-! ## The inputs `applyInputs2` writes -/

theorem LVec.toTwoState_ofBitVec {w : Nat} (x : BitVec w) :
    (LVec.ofBitVec x).toTwoState = LVec.ofBitVec x := by
  simp only [LVec.toTwoState, LVec.ofBitVec, LVec.ofNat, Array.map_ofFn]
  refine congrArg _ (congrArg Array.ofFn (funext fun i => ?_))
  simp only [Function.comp]
  by_cases hb : x.toNat.testBit ↑i = true <;> simp [hb] <;> decide

/-- A fold establishes `P` once some element satisfies `Q`, if a `Q`-step establishes `P` and every
step keeps it. -/
theorem foldl_establish {α : Type} (f : SvState → α → SvState) (P : SvState → Prop) (Q : α → Prop)
    (h1 : ∀ s a, Q a → P (f s a)) (h2 : ∀ s a, P s → P (f s a)) :
    ∀ (l : List α) (s : SvState), (∃ a ∈ l, Q a) → P (List.foldl f s l) := by
  have keep : ∀ (l : List α) (s : SvState), P s → P (List.foldl f s l) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a rest ih => exact fun s h => ih _ (h2 s a h)
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a rest ih =>
      intro s ⟨b, hb, hq⟩
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact keep rest _ (h1 s b hq)
      · exact ih _ ⟨b, hb, hq⟩

/-- An input that the entry binds at a known value holds it after `applyInputs2` (whether the
port is 4-state or 2-state: a known value is its own 2-state image). -/
theorem applyInputs2_lookup_known {d : Design2} {e st : SvState} {n : String} {w : Nat}
    {x : BitVec w} (hn : n ∈ d.inputNames.toList) (he : SvState.lookup e n = some (LVec.ofBitVec x)) :
    SvState.lookup (applyInputs2 d e st) n = some (LVec.ofBitVec x) := by
  have hex : ∃ dc ∈ d.decls.toList, dc.isInput = true ∧ dc.name = n := by
    simpa [Design2.inputNames] using hn
  unfold applyInputs2
  rw [← Array.foldl_toList]
  refine foldl_establish _ (fun s => SvState.lookup s n = some (LVec.ofBitVec x))
    (fun dc => dc.isInput = true ∧ dc.name = n) ?_ ?_ _ st hex
  · rintro s dc ⟨h1, rfl⟩
    simp only [h1, if_true, he]
    split <;> simp [LVec.toTwoState_ofBitVec]
  · intro s dc hs
    by_cases hi : dc.isInput = true
    · simp only [hi, if_true]
      cases hl : SvState.lookup e dc.name with
      | none => exact hs
      | some v =>
          simp only
          by_cases hname : dc.name = n
          · rw [hname] at hl
            rw [he] at hl
            cases hl
            rw [hname]
            split <;> simp [LVec.toTwoState_ofBitVec]
          · rw [SvState.lookup_set_ne _ _ hname]; exact hs
    · simp only [hi, Bool.false_eq_true, if_false]; exact hs

/-! ## The pre sample shows the stimulus -/

open Observe in
/-- From a cycle observation to its pre part. -/
theorem cycleObs2_pre {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {inputs st : SvState}
    {k : Nat} {o : CycleObs SvState} {k' : Nat}
    (h : cycleObs2 d σ fuel inputs st k = .ok (o, k')) :
    ∃ k2, cyclePre2 d σ fuel inputs st k = .ok (o.pre, k2) := by
  unfold cycleObs2 at h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨⟨pre, k2⟩, h1, ⟨post, k3⟩, -, h3⟩ := h
  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  exact ⟨k2, h1⟩

open Observe in
/-- **The pre sample shows the stimulus.** In every completed run of a design that writes no input
port, the pre sample of cycle `c` holds every input that stimulus entry `c` binds at a known value. -/
theorem Observe.Obs_run2.pre_input {d : Design2} (hd : d.writesInput = false) {σ : ScheduleOracle}
    {stim : List SvState} {r : List (CycleObs SvState)} (hr : Obs_run2.Runs d σ stim r)
    {c : Nat} {e : SvState} {o : CycleObs SvState} (he : stim[c]? = some e) (ho : r[c]? = some o)
    {n : String} (hn : n ∈ d.inputNames.toList) {w : Nat} {x : BitVec w}
    (hx : SvState.lookup e n = some (LVec.ofBitVec x)) :
    SvState.lookup o.pre n = some (LVec.ofBitVec x) := by
  obtain ⟨fuel, hrun⟩ := hr
  obtain ⟨inputs, prev, kc, kc', hi, -, hcyc⟩ := runFromObs2_cycle hrun ho
  rw [he, Option.some.injEq] at hi
  subst hi
  obtain ⟨k2, hpre⟩ := cycleObs2_pre hcyc
  rw [cyclePre2_lookup_input hd hpre hn]
  exact applyInputs2_lookup_known hn hx

/-! ## Axiom pins -/

#print axioms Design2.writesName_of_writesInput
#print axioms resolveLhs2_writes
#print axioms resolveConcatLhs2_writes
#print axioms writeConcatLhs2_lookup
#print axioms exec_frame
#print axioms commitNba2_lookup
#print axioms runCombProcess2_lookup
#print axioms combPass2_lookup
#print axioms combSettle2_lookup
#print axioms resetPass2_lookup
#print axioms resetPhase2_lookup
#print axioms cyclePre2_lookup_input
#print axioms LVec.toTwoState_ofBitVec
#print axioms foldl_establish
#print axioms applyInputs2_lookup_known
#print axioms cycleObs2_pre
#print axioms Observe.Obs_run2.pre_input

end LeanModels.Sv
