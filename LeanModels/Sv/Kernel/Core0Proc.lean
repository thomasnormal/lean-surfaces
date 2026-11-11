import LeanModels.Sv.Kernel.Core0Comb
import LeanModels.Sv.Comb2Proc

/-!
# R-BODY-0 and R-COMB-0 with `always_comb` (gate G-B) (`LeanModels.Sv.Kernel`)

Gate G-B of `svgolf/design/architecture/EXECUTION-PLAN.md`: the chain
**E-core-0 → R-BODY → R-COMB-0 → `CombEqs` → `combSettle2`** for designs of
continuous assigns plus `always_comb` blocks, as theorems over every design in
the profile (not a fixture equality), with a fixture showing the hypotheses
are satisfiable and a self-reading body showing they are needed.

**Status: derived from E** (`Core0.lean`); `closed_eq_combSettle2_lower` and
`rcomb1` are the second slice of the *transport theorem* to Design2.

## The chain

1. **E-core-0.** An `always_comb` activation is `execBody` (`Core0.lean`), a
   fuel-free structural execution of the body on the store.
2. **R-BODY-0** (`activate_comb`): on a typed store, that activation succeeds
   and writes, on the view, exactly the continuous assign the body lowers to
   (`Design2.lowerComb`, `Comb2Proc.lean`): `combWrite d' (view s) S.target v`.
   Route: `execBody` is `execStmt2` at sufficient fuel
   (`execBody_of_execStmt2`, a fuel induction; the body's targets are static,
   `Stmt2.staticB_of_symExec`), then `runCombProcess2_alwaysComb_fwd`.
3. **R-COMB-0** (`Settles.ofLower`): the lowered design is an equation design
   for E (`Settles`), so `Core0Comb.lean`'s generic theorems apply: every legal
   schedule closes the slot; the closed store solves `CombEqs d'` and is the
   unique such solution.
4. **`combSettle2`** (`closed_eq_combSettle2_lower`, `rcomb1`): `CombSim`
   (`Comb2Proc.lean`) carries every settle of the design to one of its lowering
   and back, so E's closed store is what `combSettle2` returns on the design
   itself.

## Hypotheses (all static, all decided on a concrete design)

`E.toDesign2.lowerComb = some d'` (the body lowers: static targets, no NBA, no
self-read); `CombDesign d'` (single driver per bit, debt D-X1a); `AllFour E`;
`completeB E d'` (E's sensitivity covers the lowered reads: sensitivity-
completeness, decided per design — debt D-X1d, below); `rankedB E d' rank` and
`boundB E rank` (the rank certificate on E's sensitivity). For an assign-only
design the same theorems are `Core0Comb.lean`'s (`Settles.ofProfile0`).
-/

namespace LeanModels.Sv

/-! ## Static bodies -/

mutual

/-- Every blocking target of the body is static, and it has no NBA and no
`.unsupported` statement: the bodies `execBody` runs without refusing. -/
def Stmt2.staticB (d : Design2) : Stmt2 → Bool
  | .blockingAssign t _ => (Lhs2.staticWin d t).isSome
  | .nbaAssign _ _ => false
  | .ifStmt _ t e => t.staticB d && Stmt2.optStaticB d e
  | .block body => Stmt2.listStaticB d body.toList
  | .caseStmt _ items dflt mode chk =>
      decide (chk = .none) && Kernel.caseModeInE0 mode && CaseItem2.listStaticB d items.toList &&
        Stmt2.optStaticB d dflt
  | .unsupported _ _ => false
termination_by structural s => s

def Stmt2.optStaticB (d : Design2) : Option Stmt2 → Bool
  | none => true
  | some s => s.staticB d
termination_by structural o => o

def Stmt2.listStaticB (d : Design2) : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.staticB d && Stmt2.listStaticB d ss
termination_by structural ss => ss

def CaseItem2.staticB (d : Design2) : CaseItem2 → Bool
  | .mk _ body => body.staticB d
termination_by structural it => it

def CaseItem2.listStaticB (d : Design2) : List CaseItem2 → Bool
  | [] => true
  | it :: rest => it.staticB d && CaseItem2.listStaticB d rest
termination_by structural its => its

end

/-- E's static target window is the lowering's (`Lhs2.symWin`). -/
theorem Lhs2.staticWin_eq_symWin (d : Design2) (t : Lhs2) : Lhs2.staticWin d t = Lhs2.symWin d t := by
  cases t <;> rfl

/-- What a static target window is. -/
theorem Lhs2.staticWin_spec {d : Design2} {t : Lhs2} {n : String} {lo w : Nat}
    (h : Lhs2.staticWin d t = some (n, lo, w)) :
    t.window? d = some (n, lo, w) ∧ (∀ ps, t = .concat ps → False) ∧
      ∃ dw, d.declWidth n = some dw ∧ lo + w ≤ dw := by
  cases t with
  | concat ps => simp [Lhs2.staticWin] at h
  | _ =>
      simp only [Lhs2.staticWin, Option.bind_eq_some_iff] at h
      obtain ⟨W, hW, dw, hdw, hif⟩ := h
      split at hif
      · next hle =>
          cases hif
          exact ⟨hW, (fun _ h => by cases h), dw, hdw, hle⟩
      · cases hif

mutual

/-- Target windows read only the declarations. -/
theorem Lhs2.windows?_congr {d d' : Design2} (h : d'.decls = d.decls) :
    ∀ t : Lhs2, t.windows? d' = t.windows? d
  | .ident n => by rw [Lhs2.windows?_ident, Lhs2.windows?_ident, Design2.declWidth_congr h]
  | .slice n lo w => by rw [Lhs2.windows?_slice, Lhs2.windows?_slice]
  | .index n idx ew => by cases idx <;> rfl
  | .concat ps => by
      rw [Lhs2.windows?_concat, Lhs2.windows?_concat, Lhs2.listWindows?_congr h ps]
termination_by structural t => t

theorem Lhs2.listWindows?_congr {d d' : Design2} (h : d'.decls = d.decls) :
    ∀ ps : List Lhs2, Lhs2.listWindows? d' ps = Lhs2.listWindows? d ps
  | [] => by rw [Lhs2.listWindows?_nil, Lhs2.listWindows?_nil]
  | t :: ts => by
      rw [Lhs2.listWindows?_cons, Lhs2.listWindows?_cons, Lhs2.windows?_congr h t,
        Lhs2.listWindows?_congr h ts]
termination_by structural ps => ps

end

/-! ### A body the lowering accepts is static -/

mutual

/-- No qualified `case` (`unique`, `unique0`, `priority`) anywhere in the body: the bodies whose
lowering (first match) is E's activation on every state. A qualified case refuses on a violated
claim (`execBody`), so the lowering theorems take this as a hypothesis, as `run2`'s take
`hasQualifiedCase = false` (master 2218821b). It also excludes `casez`/`casex`, which `run2` and
`symExec` execute (master 9237c380) and E-core-0 refuses (`caseModeRefusal`). -/
def Stmt2.qualFree : Stmt2 → Bool
  | .ifStmt _ t e => t.qualFree && Stmt2.optQualFree e
  | .block body => Stmt2.listQualFree body.toList
  | .caseStmt _ items dflt mode chk =>
      decide (chk = .none) && Kernel.caseModeInE0 mode && CaseItem2.listQualFree items.toList &&
        Stmt2.optQualFree dflt
  | .blockingAssign _ _ | .nbaAssign _ _ | .unsupported _ _ => true
termination_by structural s => s

def Stmt2.optQualFree : Option Stmt2 → Bool
  | none => true
  | some s => s.qualFree
termination_by structural o => o

def Stmt2.listQualFree : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.qualFree && Stmt2.listQualFree ss
termination_by structural ss => ss

def CaseItem2.qualFree : CaseItem2 → Bool
  | .mk _ body => body.qualFree
termination_by structural it => it

def CaseItem2.listQualFree : List CaseItem2 → Bool
  | [] => true
  | it :: rest => it.qualFree && CaseItem2.listQualFree rest
termination_by structural its => its

end

mutual

theorem Stmt2.staticB_of_symExec : ∀ (s : Stmt2) {d : Design2} {S S' : SymState},
    s.symExec d S = some S' → s.qualFree = true → s.staticB d = true
  | .blockingAssign t e, d, S, S', h, _ => by
      simp only [Stmt2.symExec] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨e', -, W, hW, -⟩ := h
        simp [Stmt2.staticB, Lhs2.staticWin_eq_symWin, hW]
      · cases h
  | .ifStmt c t e, d, S, S', h, hq => by
      simp only [Stmt2.qualFree, Bool.and_eq_true] at hq
      simp only [Stmt2.symExec] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨c', -, St, ht, Sf, hf, -⟩ := h
        simp [Stmt2.staticB, Stmt2.staticB_of_symExec t ht hq.1,
          Stmt2.optStaticB_of_symExecOpt e hf hq.2]
      · cases h
  | .block body, d, S, S', h, hq => by
      simp only [Stmt2.qualFree] at hq
      simp only [Stmt2.symExec] at h
      simp [Stmt2.staticB, Stmt2.listStaticB_of_symExecList body.toList h hq]
  | .caseStmt subj items dflt mode chk, d, S, S', h, hq => by
      simp only [Stmt2.qualFree, Bool.and_eq_true] at hq
      obtain ⟨⟨⟨hc, hm⟩, hi⟩, hdq⟩ := hq
      simp only [Stmt2.symExec] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨subj', -, Sd, hd, hl⟩ := h
        simp [Stmt2.staticB, hc, hm, CaseItem2.listStaticB_of_symExecList items.toList hl hi,
          Stmt2.optStaticB_of_symExecOpt dflt hd hdq]
      · cases h
  | .nbaAssign _ _, d, S, S', h, _ => by simp [Stmt2.symExec] at h
  | .unsupported _ _, d, S, S', h, _ => by simp [Stmt2.symExec] at h
termination_by structural s => s

theorem Stmt2.optStaticB_of_symExecOpt : ∀ (o : Option Stmt2) {d : Design2} {S S' : SymState},
    Stmt2.symExecOpt d S o = some S' → Stmt2.optQualFree o = true → Stmt2.optStaticB d o = true
  | none, _, _, _, _, _ => by simp [Stmt2.optStaticB]
  | some s, d, S, S', h, hq => by
      simp only [Stmt2.symExecOpt] at h
      simp only [Stmt2.optQualFree] at hq
      simp [Stmt2.optStaticB, Stmt2.staticB_of_symExec s h hq]
termination_by structural o => o

theorem Stmt2.listStaticB_of_symExecList : ∀ (ss : List Stmt2) {d : Design2} {S S' : SymState},
    Stmt2.symExecList d S ss = some S' → Stmt2.listQualFree ss = true → Stmt2.listStaticB d ss = true
  | [], _, _, _, _, _ => by simp [Stmt2.listStaticB]
  | s :: ss, d, S, S', h, hq => by
      simp only [Stmt2.listQualFree, Bool.and_eq_true] at hq
      simp only [Stmt2.symExecList, Option.bind_eq_some_iff] at h
      obtain ⟨S1, h1, h2⟩ := h
      simp [Stmt2.listStaticB, Stmt2.staticB_of_symExec s h1 hq.1,
        Stmt2.listStaticB_of_symExecList ss h2 hq.2]
termination_by structural ss => ss

theorem CaseItem2.staticB_of_symArm : ∀ (it : CaseItem2) {d : Design2} {S : SymState}
    {pats : List Expr2} {Sb : SymState}, it.symArm d S = some (pats, Sb) → it.qualFree = true →
      it.staticB d = true
  | .mk ps body, d, S, pats, Sb, h, hq => by
      simp only [CaseItem2.qualFree] at hq
      simp only [CaseItem2.symArm] at h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨p, -, Sb', hb, -⟩ := h
        simp [CaseItem2.staticB, Stmt2.staticB_of_symExec body hb hq]
      · cases h
termination_by structural it => it

theorem CaseItem2.listStaticB_of_symExecList : ∀ (its : List CaseItem2) {d : Design2}
    {S : SymState} {subj : Expr2} {mode : CaseMode} {Sd S' : SymState},
    CaseItem2.symExecList d S subj mode Sd its = some S' → CaseItem2.listQualFree its = true →
      CaseItem2.listStaticB d its = true
  | [], _, _, _, _, _, _, _, _ => by simp [CaseItem2.listStaticB]
  | it :: rest, d, S, subj, mode, Sd, S', h, hq => by
      simp only [CaseItem2.listQualFree, Bool.and_eq_true] at hq
      simp only [CaseItem2.symExecList, Option.bind_eq_some_iff] at h
      obtain ⟨⟨pats, Sb⟩, harm, Sr, hr, -⟩ := h
      simp [CaseItem2.listStaticB, CaseItem2.staticB_of_symArm it harm hq.1,
        CaseItem2.listStaticB_of_symExecList rest hr hq.2]
termination_by structural its => its

end

end LeanModels.Sv

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

/-! ## Typed stores, any equation design -/

/-- A declared name is bound in the view, at its declared width. -/
theorem Elab.lookup_declared {E : Elab} {s : Store} (hT : E.Typed s) {n : String} {dw : Nat}
    (h : E.toDesign2.declWidth n = some dw) :
    ∃ old, SvState.lookup (E.view s) n = some old ∧ old.width = dw := by
  cases hx : E.resolve n with
  | none =>
      rw [Elab.resolve_none hx] at h
      cases h
  | some x =>
      obtain ⟨dc, hdecl, -, -, hwd⟩ := Elab.resolve_some hx
      rw [hwd, Option.some.injEq] at h
      refine ⟨(s x).bits, by rw [E.lookup_view, hx]; rfl, ?_⟩
      rw [(s x).width_eq, hT x dc hdecl, ← h]
      rfl

/-- A typed store's view has the comb shape of any comb design with E's
declarations. -/
theorem Elab.shape_view_of {E : Elab} {d : Design2} (hd : CombDesign d) (hdecls : d.decls = E.decls)
    {s : Store} (hT : E.Typed s) : StateShape d (E.view s) := by
  refine ⟨by rw [E.keys_view s, hdecls], fun n hn => ?_⟩
  obtain ⟨i, lo, w, hW⟩ := hn
  obtain ⟨dw, hdw, -⟩ := hd.inWidth i n lo w hW
  have hdw' : E.toDesign2.declWidth n = some dw := by
    simp only [Design2.declWidth, hdecls] at hdw
    exact hdw
  obtain ⟨old, hold, hw⟩ := Elab.lookup_declared hT hdw'
  exact ⟨old, hold, by rw [hdw, hw]⟩

/-! ## `execBody`, one step at a time -/

theorem execBody_assign_run {E : Elab} {s : Store} {t : Lhs2} {e : Expr2} {n : String}
    {lo w : Nat} {v : LVec} (hW : Lhs2.staticWin E.toDesign2 t = some (n, lo, w))
    (hv : evalPure2 (E.view s) e = .ok v) :
    execBody E (.blockingAssign t e) s = .ok (.ok (), E.writeWin s n lo (v.resizeU w)) := by
  simp only [execBody, hW]
  rw [SemMWith.run_bind_ok (SemMWith.run_get s)]
  rw [SemMWith.run_bind_ok (show ofRes (evalPure2 (E.view s) e) s = .ok (.ok v, s) by
    rw [hv]; rfl)]
  rfl

theorem execBody_if_run {E : Elab} {s : Store} {c : Expr2} {t : Stmt2} {e : Option Stmt2}
    {cv : LVec} (hc : evalPure2 (E.view s) c = .ok cv) :
    execBody E (.ifStmt c t e) s = (if cv.condTrue then execBody E t else execBodyOpt E e) s := by
  simp only [execBody]
  rw [SemMWith.run_bind_ok (SemMWith.run_get s)]
  rw [SemMWith.run_bind_ok (show ofRes (evalPure2 (E.view s) c) s = .ok (.ok cv, s) by
    rw [hc]; rfl)]

theorem execBody_case_run {E : Elab} {s : Store} {subj : Expr2} {items : Array CaseItem2}
    {dflt : Option Stmt2} {mode : CaseMode} {chk : CaseCheck} {sv : LVec}
    (hchk : chk = .none) (hm : caseModeInE0 mode = true)
    (hsv : evalPure2 (E.view s) subj = .ok sv) :
    execBody E (.caseStmt subj items dflt mode chk) s =
      (execArms E sv mode items.toList >>= fun hit =>
        if hit then pure () else execBodyOpt E dflt) s := by
  subst hchk
  simp only [execBody, hm, ↓reduceIte]
  rw [SemMWith.run_bind_ok (SemMWith.run_get s)]
  rw [SemMWith.run_bind_ok (show ofRes (evalPure2 (E.view s) subj) s = .ok (.ok sv, s) by
    rw [hsv]; rfl)]

theorem execArm_run {E : Elab} {s : Store} {sv : LVec} {mode : CaseMode} {pats : Array Expr2}
    {body : Stmt2} {pvs : List LVec} (hp : evalPures2 (E.view s) pats.toList = .ok pvs) :
    execArm E sv mode (.mk pats body) s =
      (if pvs.any (fun pv => caseHit mode sv pv) then (execBody E body >>= fun _ => pure true)
        else pure false) s := by
  simp only [execArm]
  rw [SemMWith.run_bind_ok (SemMWith.run_get s)]
  rw [SemMWith.run_bind_ok (show ofRes (evalPures2 (E.view s) pats.toList) s = .ok (.ok pvs, s) by
    rw [hp]; rfl)]

/-! ## `execBody` is `execStmt2` -/

/-- **`execBody` is the interpreter, without fuel.** Whenever `execStmt2` (any
fuel) runs a static body from the view of a typed store, `execBody` runs it
on the store to a store with that view (and no NBA was issued). A fuel
induction over the interpreter's mutual block. -/
theorem execBody_of_execStmt2 {E : Elab} (h4 : AllFour E) : ∀ fuel : Nat,
    (∀ (stmt : Stmt2) (s : Store) (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      E.Typed s → stmt.staticB E.toDesign2 = true →
      execStmt2 fuel (E.view s) nba stmt = .ok (st', nba') →
      nba' = nba ∧ ∃ s', execBody E stmt s = .ok (.ok (), s') ∧ E.view s' = st' ∧ E.Typed s') ∧
    (∀ (sv : LVec) (items : List CaseItem2) (dflt : Option Stmt2) (mode : CaseMode) (s : Store)
      (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      E.Typed s → CaseItem2.listStaticB E.toDesign2 items = true →
      Stmt2.optStaticB E.toDesign2 dflt = true →
      execCase2 fuel (E.view s) nba sv items dflt mode = .ok (st', nba') →
      nba' = nba ∧ ∃ s', (execArms E sv mode items >>= fun hit =>
        if hit then pure () else execBodyOpt E dflt) s = .ok (.ok (), s') ∧
        E.view s' = st' ∧ E.Typed s') ∧
    (∀ (ss : List Stmt2) (s : Store) (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      E.Typed s → Stmt2.listStaticB E.toDesign2 ss = true →
      execStmts2 fuel (E.view s) nba ss = .ok (st', nba') →
      nba' = nba ∧ ∃ s', execBodyList E ss s = .ok (.ok (), s') ∧ E.view s' = st' ∧ E.Typed s')
  | 0 => by
      refine ⟨fun _ _ _ _ _ _ _ h => by simp [execStmt2] at h,
        fun _ items _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => by simp [execStmts2] at h⟩
      rcases items with _ | ⟨⟨pats, body⟩, rest⟩ <;> simp [execCase2] at h
  | f + 1 => by
      obtain ⟨ihS, ihC, ihL⟩ := execBody_of_execStmt2 h4 f
      refine ⟨?_, ?_, ?_⟩
      · intro stmt s nba st' nba' hT hst h
        cases stmt with
        | blockingAssign t e =>
            simp only [Stmt2.staticB, Option.isSome_iff_exists] at hst
            obtain ⟨⟨n, lo, w⟩, hW⟩ := hst
            obtain ⟨hwin, hnc, dw, hdw, hin⟩ := Lhs2.staticWin_spec hW
            obtain ⟨old, hold, hwold⟩ := Elab.lookup_declared hT hdw
            -- the interpreter's run of a static leaf target, at any value of the right-hand side
            have key : ∀ v, evalExpr2 f (E.view s) e = .ok v →
                execStmt2 (f + 1) (E.view s) nba (.blockingAssign t e) =
                  .ok (SvState.set (E.view s) n (old.insertAt lo (v.resizeU w)), nba) := by
              intro v hv
              have hf : 0 < f := by
                cases f with
                | zero => simp [evalExpr2] at hv
                | succ => omega
              have hres := resolveLhs2_of_window? hf hwin hold (by omega) (by rw [hdw, hwold])
              cases t with
              | concat ps => exact absurd rfl (hnc ps)
              | _ => simp [execStmt2, hv, hres, hold]
            cases hv : evalExpr2 f (E.view s) e with
            | ok v =>
                rw [key v hv] at h
                simp only [Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨rfl, _, execBody_assign_run hW (evalPure2_of_evalExpr2_ok hv), ?_,
                  hT.writeWin _ _ _⟩
                rw [Elab.view_writeWin hT h4, hold]
            | timeout => simp [execStmt2, hv] at h
            | unsupported m => simp [execStmt2, hv] at h
        | nbaAssign t e => simp [Stmt2.staticB] at hst
        | ifStmt c t e =>
            simp only [Stmt2.staticB, Bool.and_eq_true] at hst
            obtain ⟨ht, he⟩ := hst
            simp only [execStmt2, Res.bind_eq_ok] at h
            obtain ⟨cv, hcv, h⟩ := h
            rw [execBody_if_run (evalPure2_of_evalExpr2_ok hcv)]
            by_cases hc : cv.condTrue = true
            · rw [if_pos hc] at h ⊢
              exact ihS t s nba st' nba' hT ht h
            · rw [if_neg hc] at h ⊢
              cases e with
              | none =>
                  simp only [Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨rfl, s, rfl, rfl, hT⟩
              | some s0 =>
                  simp only [Stmt2.optStaticB] at he
                  simp only [execBodyOpt]
                  exact ihS s0 s nba st' nba' hT he h
        | block body =>
            simp only [Stmt2.staticB] at hst
            simp only [execStmt2] at h
            simp only [execBody]
            exact ihL body.toList s nba st' nba' hT hst h
        | caseStmt subj items dflt mode chk =>
            simp only [Stmt2.staticB, Bool.and_eq_true, decide_eq_true_eq] at hst
            obtain ⟨⟨⟨hc, hm⟩, hi⟩, hd⟩ := hst
            simp only [execStmt2, Res.bind_eq_ok] at h
            obtain ⟨sv, hsv, h⟩ := h
            rw [execBody_case_run hc hm (evalPure2_of_evalExpr2_ok hsv)]
            exact ihC sv items.toList dflt mode s nba st' nba' hT hi hd h
        | unsupported k x => simp [Stmt2.staticB] at hst
      · intro sv items dflt mode s nba st' nba' hT hi hd h
        cases items with
        | nil =>
            simp only [execCase2] at h
            simp only [execArms]
            rw [SemMWith.run_bind_ok (SemMWith.run_pure false s)]
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases dflt with
            | none =>
                simp only [Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨rfl, s, rfl, rfl, hT⟩
            | some s0 =>
                simp only [Stmt2.optStaticB] at hd
                simp only [execBodyOpt]
                exact ihS s0 s nba st' nba' hT hd h
        | cons it rest =>
            obtain ⟨pats, body⟩ := it
            simp only [CaseItem2.listStaticB, CaseItem2.staticB, Bool.and_eq_true] at hi
            obtain ⟨hb, hr⟩ := hi
            simp only [execCase2, Res.bind_eq_ok] at h
            obtain ⟨pvs, hpvs, h⟩ := h
            have harm := execArm_run (E := E) (s := s) (sv := sv) (mode := mode) (body := body)
              (evalPures2_of_evalExprs2_ok hpvs)
            simp only [execArms, bind_assoc]
            by_cases hhit : pvs.any (fun pv => caseHit mode sv pv) = true
            · rw [if_pos hhit] at h harm
              obtain ⟨rfl, s', hs', hv', hT'⟩ := ihS body s nba st' nba' hT hb h
              refine ⟨rfl, s', ?_, hv', hT'⟩
              have h1 : execArm E sv mode (.mk pats body) s = .ok (.ok true, s') := by
                rw [harm, SemMWith.run_bind_ok hs']
                rfl
              rw [SemMWith.run_bind_ok h1]
              rfl
            · rw [if_neg hhit] at h harm
              obtain ⟨rfl, s', hs', hv', hT'⟩ := ihC sv rest dflt mode s nba st' nba' hT hr hd h
              refine ⟨rfl, s', ?_, hv', hT'⟩
              rw [SemMWith.run_bind_ok (harm.trans (SemMWith.run_pure false s))]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hs'
      · intro ss s nba st' nba' hT hss h
        cases ss with
        | nil =>
            simp only [execStmts2, Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, s, rfl, rfl, hT⟩
        | cons s0 ss =>
            simp only [Stmt2.listStaticB, Bool.and_eq_true] at hss
            obtain ⟨h0, hrest⟩ := hss
            simp only [execStmts2, Res.bind_eq_ok] at h
            obtain ⟨⟨st1, nba1⟩, h1, h2⟩ := h
            obtain ⟨hn1, s1, hs1, hv1, hT1⟩ := ihS s0 s nba st1 nba1 hT h0 h1
            subst nba1
            subst hv1
            obtain ⟨rfl, s', hs', hv', hT'⟩ := ihL ss s1 nba st' nba' hT1 hrest h2
            refine ⟨rfl, s', ?_, hv', hT'⟩
            simp only [execBodyList]
            rw [SemMWith.run_bind_ok hs1]
            exact hs'

/-! ## R-BODY-0 -/

/-- **R-BODY-0.** An `always_comb` activation of E, on a typed store, succeeds
and writes, on the view, exactly the continuous assign its body lowers to. -/
theorem activate_comb {E : Elab} {d' : Design2} (hl : E.toDesign2.lowerComb = some d')
    (hd' : CombDesign d') (h4 : AllFour E) {p : ProcId} {body : Stmt2}
    (hp : E.procs[p]? = some (.comb body)) (hqf : body.qualFree = true) {s : Store} (hT : E.Typed s) :
    ∃ t e v s', d'.processes[p]? = some (.assign t e) ∧ evalPure2 (E.view s) e = .ok v ∧
      activate E p s = .ok (.ok (), s') ∧ E.view s' = combWrite d' (E.view s) t v ∧ E.Typed s' := by
  have hp2 : E.toDesign2.processes[p]? = some (.alwaysComb body) := by
    simp [Elab.toDesign2, hp, Proc0.toProcess2]
  obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp2
  obtain ⟨S, hsym, -, rfl⟩ := Process2.lowerComb_alwaysComb hq
  have hdecls : d'.decls = E.toDesign2.decls := (Design2.lowerComb_spec hl).2.1
  have hs : StateShape d' (E.view s) := Elab.shape_view_of hd' hdecls hT
  obtain ⟨v, hv, hrun⟩ :=
    runCombProcess2_alwaysComb_fwd hd' hdecls hsym hq' hs (Nat.le_refl body.fuelB)
  simp only [runCombProcess2, Res.bind_eq_ok] at hrun
  obtain ⟨⟨st', nba⟩, hex, hm⟩ := hrun
  cases nba with
  | cons u us => simp at hm
  | nil =>
      simp only [Res.ok.injEq] at hm
      obtain ⟨-, s', hs', hv', hT'⟩ := (execBody_of_execStmt2 h4 body.fuelB).1 body s [] st' []
        hT (Stmt2.staticB_of_symExec body hsym hqf) hex
      refine ⟨S.target, S.rhs, v, s', hq', hv, ?_, by rw [hv', hm], hT'⟩
      simp only [activate, hp]
      exact hs'

/-! ## The certificate and completeness as checks -/

/-- Sensitivity-completeness, decided: every read of every lowered right-hand
side is in E's sensitivity of that process. -/
def completeB (E : Elab) (d : Design2) : Bool :=
  (List.range d.processes.size).all fun q =>
    match d.processes[q]? with
    | some (.assign _ e) => e.reads.all fun r => decide (r ∈ E.sens q)
    | _ => true

/-- The rank certificate on E's sensitivity, decided. -/
def rankedB (E : Elab) (d : Design2) (rank : Nat → Nat) : Bool :=
  (List.range d.processes.size).all fun p => (List.range E.procs.size).all fun q =>
    match d.processes[p]? with
    | some (.assign t _) =>
        (E.sens q).all fun r => (t.wins d).all fun w => !(r.overlaps w) || decide (rank p < rank q)
    | _ => true

/-- Ranks below the number of processes, decided. -/
def boundB (E : Elab) (rank : Nat → Nat) : Bool :=
  (List.range E.procs.size).all fun i => decide (rank i < E.procs.size)

theorem complete_of_completeB {E : Elab} {d : Design2} (h : completeB E d = true) :
    ∀ (q : ProcId) (t : Lhs2) (e : Expr2), d.processes[q]? = some (.assign t e) →
      ∀ r ∈ e.reads, r ∈ E.sens q := by
  intro q t e hq r hr
  have hqn : q < d.processes.size := (Array.getElem?_eq_some_iff.mp hq).1
  simp only [completeB, List.all_eq_true, List.mem_range] at h
  have h' := h q hqn
  rw [hq] at h'
  simp only [List.all_eq_true, decide_eq_true_eq] at h'
  exact h' r hr

theorem Elab.lt_of_mem_sens {E : Elab} {q : ProcId} {r : ReadWin} (h : r ∈ E.sens q) :
    q < E.procs.size := by
  cases hq : E.procs[q]? with
  | none => simp [Elab.sens, hq] at h
  | some _ => exact (Array.getElem?_eq_some_iff.mp hq).1

theorem ranked_of_rankedB {E : Elab} {d : Design2} {rank : Nat → Nat} (h : rankedB E d rank = true) :
    ∀ (p q : ProcId) (t : Lhs2) (e : Expr2), d.processes[p]? = some (.assign t e) →
      ∀ r ∈ E.sens q, ∀ w ∈ t.wins d, r.overlaps w = true → rank p < rank q := by
  intro p q t e hp r hr w hw hov
  have hpn : p < d.processes.size := (Array.getElem?_eq_some_iff.mp hp).1
  simp only [rankedB, List.all_eq_true, List.mem_range] at h
  have h' := h p hpn q (Elab.lt_of_mem_sens hr)
  rw [hp] at h'
  simp only [List.all_eq_true] at h'
  have h2 := h' r hr w hw
  rw [hov] at h2
  simpa using h2

theorem bound_of_boundB {E : Elab} {rank : Nat → Nat} (h : boundB E rank = true) :
    ∀ i, i < E.procs.size → rank i < E.procs.size := by
  intro i hi
  simp only [boundB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

/-! ## R-COMB-0 with `always_comb`: the lowering is an equation design -/

/-- Every `always_comb` body of `E` is free of qualified cases, decided. -/
def Elab.qualFreeB (E : Elab) : Bool :=
  E.procs.toList.all fun p => match p with
    | .comb body => body.qualFree
    | .assign _ _ => true
    | .implicit body => body.qualFree

theorem Elab.qualFree_of_qualFreeB {E : Elab} (h : E.qualFreeB = true) {p : ProcId} {body : Stmt2}
    (hp : E.procs[p]? = some (.comb body)) : body.qualFree = true := by
  simp only [Elab.qualFreeB, List.all_eq_true] at h
  have hm : Proc0.comb body ∈ E.procs.toList := by
    rw [← Array.getElem?_toList] at hp
    exact List.mem_of_getElem? hp
  simpa using h _ hm

/-- **The lowered design is an equation design for E.** Assigns activate as
themselves (`activate_assign`), `always_comb` bodies as their lowered assign
(R-BODY-0, `activate_comb`). -/
theorem Settles.ofLower {E : Elab} {d' : Design2} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d') (h4 : AllFour E)
    (hq : E.qualFreeB = true)
    (hc : completeB E d' = true) (hr : rankedB E d' rank = true) (hb : boundB E rank = true) :
    Settles E d' rank where
  comb := hd'
  decls := (Design2.lowerComb_spec hl).2.1
  size := by rw [(Design2.lowerComb_spec hl).2.2.1, Elab.size_toDesign2]
  four := h4
  startReady := fun p hp => by
    cases hpp : E.procs[p]? with
    | none =>
        rw [Array.getElem?_eq_getElem hp] at hpp
        simp at hpp
    | some pr =>
        cases pr with
        | assign t e =>
            have hget : E.procs[p] = .assign t e := by
              simpa [Array.getElem?_eq_getElem hp] using hpp
            rw [Elab.startActive]
            apply List.mem_filter.mpr
            refine ⟨List.mem_range.mpr hp, ?_⟩
            rw [hpp]
            rfl
        | comb body =>
            have hget : E.procs[p] = .comb body := by
              simpa [Array.getElem?_eq_getElem hp] using hpp
            rw [Elab.startActive]
            apply List.mem_filter.mpr
            refine ⟨List.mem_range.mpr hp, ?_⟩
            rw [hpp]
            rfl
        | implicit body =>
            have hpE : E.toDesign2.processes[p]? = some (.unsupported
                "ProceduralBlockSymbol:Always" "source-level event-controlled always is retained; the frozen process AST has no event-list constructor") := by
              simp [Elab.toDesign2, hpp, Proc0.toProcess2]
            obtain ⟨q, hq, hqp⟩ := Design2.lowerComb_proc hl hpE
            simp [Process2.lowerComb] at hq
  act := fun s p hT hpn => by
    have hdecls : d'.decls = E.toDesign2.decls := (Design2.lowerComb_spec hl).2.1
    cases hpp : E.procs[p]? with
    | none =>
        rw [Array.getElem?_eq_getElem hpn] at hpp
        cases hpp
    | some pr =>
        cases pr with
        | assign t e =>
            have hp2 : E.toDesign2.processes[p]? = some (.assign t e) :=
              Elab.proc_assign_iff.mpr hpp
            obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp2
            simp only [Process2.lowerComb, Option.some.injEq] at hq
            subst hq
            have hws := hd'.windows?_of_proc hq'
            rw [Lhs2.windows?_congr hdecls] at hws
            have hs := Elab.shape_view_of hd' hdecls hT
            obtain ⟨v, hv⟩ := hd'.evalPure2_ok hs hq'
            refine ⟨t, e, v, _, hq', hv, activate_assign hpp hws hv, ?_, hT.writeWins _ _⟩
            rw [Elab.view_writeWins h4 _ _ hT, combWrite]
        | comb body => exact activate_comb hl hd' h4 hpp (Elab.qualFree_of_qualFreeB hq hpp) hT
        | implicit body =>
            have hpE : E.toDesign2.processes[p]? = some (.unsupported
                "ProceduralBlockSymbol:Always" "source-level event-controlled always is retained; the frozen process AST has no event-list constructor") := by
              simp [Elab.toDesign2, hpp, Proc0.toProcess2]
            obtain ⟨q, hq, hqp⟩ := Design2.lowerComb_proc hl hpE
            simp [Process2.lowerComb] at hq
  complete := complete_of_completeB hc
  ranked := ranked_of_rankedB hr
  bound := bound_of_boundB hb

/-! ## The chain to `combSettle2` -/

/-- **E's closed store is `combSettle2`'s result on the design itself** (fuel-
free form): whenever `combSettle2` on the design (not its lowering) returns
from the view of the slot's start, any schedule, any fuel, it returns E's
closed view. -/
theorem closed_eq_combSettle2_lower {E : Elab} {d' : Design2} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hS : Settles E d' rank) {ch : Choice} {c c' : Config}
    (hI : SettleInv E d' c) (h : SlotCloses E ch c c') {σ : ScheduleOracle} {fuel k : Nat}
    {S : SvState} {k' : Nat}
    (hS2 : combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (S, k')) :
    E.view c'.store = S := by
  obtain ⟨-, f', hf'⟩ := (CombSim.of_lowerComb hl hS.comb).combSettle2 σ fuel (E.view c.store) k S k'
    (hS.shape hI.typed) hS2
  exact hS.closed_eq_combSettle2 hI h hf'

/-- **Gate G-B: the chain E-core-0 → R-BODY → R-COMB-0 → `CombEqs` →
`combSettle2`** (derived from E; transport, second slice). For a design of
assigns and `always_comb` blocks whose lowering `d'` is an equation design,
from any typed store with every process ready, under every legal Choice: the
slot closes; the closed store solves the lowered equations and is their
unique solution with the start's undriven bits; and for every
`ScheduleOracle`, `combSettle2` on the DESIGN returns exactly that store. -/
theorem rcomb1 {E : Elab} {d' : Design2} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hS : Settles E d' rank) (ch : Choice)
    (σ : ScheduleOracle) {s : Store} (hT : E.Typed s) (k : Nat) :
    ∃ c', SlotCloses E ch (Config.init E s) c' ∧ CombEqs d' (E.view c'.store) ∧
      (∀ st, StateShape d' st → CombEqs d' st → Frame d' (E.view s) st → st = E.view c'.store) ∧
      ∃ fuel k', combSettle2 E.toDesign2 σ fuel (E.view s) k = .ok (E.view c'.store, k') := by
  have hI := SettleInv.init hS.size hS.startReady hT (d := d')
  obtain ⟨c', S, k', hcl, hS2, heq⟩ := hS.rcomb_combSettle2 ch σ hT k d'.settleFuel (Nat.le_refl _)
  obtain ⟨he, hsh, hf⟩ := hS.slotCloses_combEqs hI hcl
  obtain ⟨-, f', hf'⟩ := (CombSim.of_lowerComb' hl hS.comb).combSettle2 σ d'.settleFuel (E.view s) k
    S k' (hS.shape hT) hS2
  refine ⟨c', hcl, he, fun st hst hest hfst =>
    combEqs_unique hS.comb hS.acyclic hst hsh hest he (hfst.symm.trans hf), f', k', ?_⟩
  rw [heq]
  exact hf'

/-! ## The fixture: two assigns around one `always_comb`

`Core0Smoke.mux1` (`Core0.lean`): `w = z ^ a`, `z = y + 1`, and
`always_comb begin t = a & b; if (c) y = t; else y = ~t; end`. -/

namespace Core0Smoke

/-- The equation of `t`. -/
def eT : Expr2 := .resize 4 (.binary .and (.ident "a") (.ident "b"))

/-- The equation of `y`: the `if` is a known-bit guard on `c`. -/
def eY : Expr2 :=
  .ternary (Expr2.ifGuard (.ident "c")) (.resize 4 eT) (.resize 4 (.unary .bnot eT))

def mux1Sym : SymState := [(("t", 0, 4), eT), (("y", 0, 4), eY)]

def mux1P0 : Process2 := .assign (.ident "w") (.binary .xor (.ident "z") (.ident "a"))
def mux1P1 : Process2 := .assign (.ident "z") (.binary .add (.ident "y") (.lit (.ofNat 4 1)))

/-- The lowered design: the `always_comb` replaced by
`assign {t, y} = {eT, eY}`. -/
def mux1Low : Design2 := { mux1.toDesign2 with processes := #[mux1P0, mux1P1, mux1Sym.toAssign] }

theorem mux1_lower : mux1.toDesign2.lowerComb = some mux1Low := rfl

theorem mux1Low_proc {i : Nat} {p : Process2} : mux1Low.processes[i]? = some p ↔
    (i = 0 ∧ p = mux1P0) ∨ (i = 1 ∧ p = mux1P1) ∨ (i = 2 ∧ p = mux1Sym.toAssign) := by
  match i with
  | 0 | 1 | 2 => simp [mux1Low, eq_comm]
  | i + 3 => simp [mux1Low]

theorem mux1Low_writes {i : Nat} {wn : Win} : mux1Low.Writes i wn ↔
    (i = 0 ∧ wn = ("w", 0, 4)) ∨ (i = 1 ∧ wn = ("z", 0, 4)) ∨
    (i = 2 ∧ (wn = ("t", 0, 4) ∨ wn = ("y", 0, 4))) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases mux1Low_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp only [mux1P0, mux1P1, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2] at hw; simp [hw]
    · simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2] at hw; simp [hw]
    · rw [SymState.target_wins] at hw
      simp [mux1Sym] at hw
      simp [hw]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩)
    · exact ⟨_, _, rfl, by simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2]⟩
    · exact ⟨_, _, rfl, by simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2]⟩
    · exact ⟨_, _, rfl, by rw [SymState.target_wins]; simp [mux1Sym]⟩
    · exact ⟨_, _, rfl, by rw [SymState.target_wins]; simp [mux1Sym]⟩

theorem mux1Low_driven {n : String} : Driven mux1Low n ↔ n = "w" ∨ n = "z" ∨ n = "t" ∨ n = "y" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases mux1Low_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, 4, mux1Low_writes.mpr (by simp)⟩
    · exact ⟨1, 0, 4, mux1Low_writes.mpr (by simp)⟩
    · exact ⟨2, 0, 4, mux1Low_writes.mpr (by simp)⟩
    · exact ⟨2, 0, 4, mux1Low_writes.mpr (by simp)⟩

/-- The lowered design is in the comb profile. -/
theorem mux1Low_comb : CombDesign mux1Low where
  nodup := by decide
  assign := by
    intro i p hp
    rcases mux1Low_proc.mp hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨_, _, [("w", 0, 4)], rfl, by simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2]⟩
    · exact ⟨_, _, [("z", 0, 4)], rfl, by simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2]⟩
    · exact ⟨_, _, _, rfl, SymState.target_windows _ _⟩
  inWidth := by
    intro i n lo w h
    rcases mux1Low_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, mux1Low, mux1, Elab.toDesign2]
  notInput := by
    intro n hn
    rcases mux1Low_driven.mp hn with rfl | rfl | rfl | rfl <;>
      simp [Design2.inputNames, mux1Low, mux1, Elab.toDesign2]
  disjoint := by
    intro i j wi wj hij hi hj
    rcases mux1Low_writes.mp hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
    rcases mux1Low_writes.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      first | exact absurd rfl hij | decide
  selfDisjoint := by
    intro i t e hp
    rcases mux1Low_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [mux1P0, mux1P1, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h
    · exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
    · exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
    · rw [SymState.target_wins]; decide
  rhsFree := by
    intro i t e hp
    rcases mux1Low_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [mux1P0, mux1P1, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro i t e hp
    rcases mux1Low_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [mux1P0, mux1P1, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> decide
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [mux1Low, mux1, Elab.toDesign2] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [mux1Low, mux1, Elab.toDesign2] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The rank: the `always_comb` reads only inputs (0), `z` reads `y` (1),
`w` reads `z` (2). -/
def mux1Rank (i : Nat) : Nat := if i = 2 then 0 else if i = 1 then 1 else 2

/-- **The hypotheses hold**: the fixture is an equation design for E. -/
theorem mux1_settles : Settles mux1 mux1Low mux1Rank :=
  Settles.ofLower mux1_lower mux1Low_comb (by unfold AllFour; decide) rfl rfl rfl rfl

/-- **The chain, instantiated** (non-vacuity): from the startup store, every
schedule closes the slot at the unique solution of the lowered equations, and
`combSettle2` on the design returns it. -/
theorem mux1_rcomb1 (ch : Choice) (σ : ScheduleOracle) (k : Nat) :
    ∃ c', SlotCloses mux1 ch (Config.init mux1 mux1.initStore) c' ∧
      CombEqs mux1Low (mux1.view c'.store) ∧
      ∃ fuel k', combSettle2 mux1.toDesign2 σ fuel (mux1.view mux1.initStore) k =
        .ok (mux1.view c'.store, k') := by
  obtain ⟨c', hcl, he, -, hfin⟩ := rcomb1 mux1_lower mux1_settles ch σ (Elab.typed_initStore mux1) k
  exact ⟨c', hcl, he, hfin⟩

/-! ## The negative: a self-reading body fails the hypotheses

`Core0Smoke.selfRead` (`Core0.lean`): `always_comb begin y = t; t = a; end`.
The body reads `t` before writing it, so its lowering is refused (the
self-read check), and the chain's conclusion is false: E closes the slot with
`y` stale (`x`, the block is never woken by its own write of `t`), while
`combSettle2` re-runs every comb process until nothing changes and returns
`y = 0`. -/

theorem selfRead_not_lowered : selfRead.toDesign2.lowerComb = none := rfl

/-- `combSettle2` from the same start: `y` settles to `0`. -/
def selfReadSettle : Option (List String) :=
  ((combSettle2 selfRead.toDesign2 σ_src 10 (selfRead.view selfReadStart.store) 0).toOption).map
    fun (st, _) => ["a", "t", "y"].map (SvState.showSignal st)

#guard showClosed selfRead ["a", "t", "y"] (exec selfRead σ_src 10 selfReadStart)
  == some ["0", "0", "x"]
#guard selfReadSettle == some ["0", "0", "0"]

end Core0Smoke

/-! ## Axioms -/

#print axioms Stmt2.staticB_of_symExec
#print axioms Lhs2.windows?_congr
#print axioms execBody_of_execStmt2
#print axioms activate_comb
#print axioms Settles.ofLower
#print axioms closed_eq_combSettle2_lower
#print axioms rcomb1
#print axioms Core0Smoke.mux1_lower
#print axioms Core0Smoke.mux1Low_comb
#print axioms Core0Smoke.mux1_settles
#print axioms Core0Smoke.mux1_rcomb1
#print axioms Core0Smoke.selfRead_not_lowered

end LeanModels.Sv.Kernel
