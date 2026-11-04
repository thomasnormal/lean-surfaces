import LeanModels.Sv.Loop2E
import LeanModels.Sv.Kernel.Core0Obs

/-!
# Ordinary `always_comb` bodies over E-core-0 (WS3, the comb fragment) — *derived from E*

The loop fragment (`Loop2Frag`) reads one written signal as a value. Ordinary `always_comb` style writes
SEVERAL signals, assigns defaults and overrides them, and selects with `case` (ibex: X7 B.3). This module
gives such bodies their single-activation meaning over E-core-0, as a STATE function computed by
structural recursion, with E's own evaluator:

* **`Stmt2.combOk d`**: blocking assignments to static in-range windows (`Lhs2.staticWin`) of
  well-formed expressions (`Expr2.wfB`: declared names, no unsupported node: concatenations,
  replications, ternaries, shifts are all in), `if`/`else`, blocks, and `case` (plain, `inside`, and
  qualified: below) with well-formed subjects and patterns. Any set of signals and windows may be
  written; nothing limits the order.
* **`Stmt2.sem d`**: the meaning on the view, `evalPure2` for every expression (`ev`), first match for
  `case` (E's `execArms`), the default when nothing matches.
* **`Stmt2.sem_run`**: on every typed store of an all-4-state elaboration, one `execBody` succeeds and
  ends in a typed store whose view is `sem` of the view (no `run2`, no fuel).

`casez`/`casex` are outside the fragment (`caseModeInE0`): E-core-0 refuses them (LRM 12.5.1).

**Qualified `case` (`unique`/`unique0`/`priority`).** E-core-0 runs the first matching arm and
refuses at once when the claim does not hold at the activation (arch-x1 `2d4cdd55`; a known divergence:
LRM 12.4.2.1 defers that report and flushes it on re-trigger, X1-NOTE §13); `run2` makes a violated
claim loud too (master `2218821b`). So the meaning is asserted only where every claim on the executed
path holds: `Stmt2.claims d st` (master's `checkCaseObligation`, counted over the arms) is an explicit
hypothesis of `sem_run`, never dropped.
-/

namespace LeanModels.Sv.Loop2

open Kernel

/-- E's value of an expression (`evalPure2`; `default` where it refuses, never under `combOk`). -/
def ev (st : SvState) (e : Expr2) : LVec := match evalPure2 st e with | .ok v => v | _ => default

/-- E's values of a pattern list. -/
def evs (st : SvState) (es : List Expr2) : List LVec :=
  match evalPures2 st es with | .ok vs => vs | _ => []

/-- A case arm's patterns hit the subject value. -/
def armHit (st : SvState) (sv : LVec) (mode : CaseMode) (pats : Array Expr2) : Bool :=
  (evs st pats.toList).any fun pv => caseHit mode sv pv

mutual
/-- **The fragment's meaning** on the view (see the module docstring). -/
def _root_.LeanModels.Sv.Stmt2.sem (d : Design2) : Stmt2 → SvState → SvState
  | .blockingAssign t e, st =>
      match Lhs2.staticWin d t with
      | some (n, lo, w) => SvState.set st n ((sig st n).insertAt lo ((ev st e).resizeU w))
      | none => st
  | .ifStmt c a b, st => if (ev st c).condTrue then a.sem d st else Stmt2.optSem d b st
  | .block ss, st => Stmt2.listSem d ss.toList st
  | .caseStmt subj items dflt mode _, st =>
      (CaseItem2.listSem d (ev st subj) mode items.toList st).getD (Stmt2.optSem d dflt st)
  | _, st => st
termination_by structural s _ => s

def _root_.LeanModels.Sv.Stmt2.optSem (d : Design2) : Option Stmt2 → SvState → SvState
  | none, st => st
  | some s, st => s.sem d st
termination_by structural o _ => o

def _root_.LeanModels.Sv.Stmt2.listSem (d : Design2) : List Stmt2 → SvState → SvState
  | [], st => st
  | s :: ss, st => Stmt2.listSem d ss (s.sem d st)
termination_by structural l _ => l

/-- One arm: its body's meaning if it hits. -/
def _root_.LeanModels.Sv.CaseItem2.armSem (d : Design2) (sv : LVec) (mode : CaseMode) :
    CaseItem2 → SvState → Option SvState
  | .mk pats body, st => if armHit st sv mode pats then some (body.sem d st) else none
termination_by structural it _ => it

/-- The first hitting arm's meaning (`none`: no arm hits). -/
def _root_.LeanModels.Sv.CaseItem2.listSem (d : Design2) (sv : LVec) (mode : CaseMode) :
    List CaseItem2 → SvState → Option SvState
  | [], _ => none
  | it :: rest, st =>
      match it.armSem d sv mode st with
      | some st' => some st'
      | none => CaseItem2.listSem d sv mode rest st
termination_by structural l _ => l
end

mutual
/-- **The fragment** over `d` (see the module docstring). -/
def _root_.LeanModels.Sv.Stmt2.combOk (d : Design2) : Stmt2 → Bool
  | .blockingAssign t e => (Lhs2.staticWin d t).isSome && e.wfB d
  | .ifStmt c a b => c.wfB d && a.combOk d && Stmt2.optCombOk d b
  | .block ss => Stmt2.listCombOk d ss.toList
  | .caseStmt subj items dflt mode _ =>
      caseModeInE0 mode && subj.wfB d && CaseItem2.listCombOk d items.toList && Stmt2.optCombOk d dflt
  | _ => false
termination_by structural s => s

def _root_.LeanModels.Sv.Stmt2.optCombOk (d : Design2) : Option Stmt2 → Bool
  | none => true
  | some s => s.combOk d
termination_by structural o => o

def _root_.LeanModels.Sv.Stmt2.listCombOk (d : Design2) : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.combOk d && Stmt2.listCombOk d ss
termination_by structural l => l

def _root_.LeanModels.Sv.CaseItem2.combOk (d : Design2) : CaseItem2 → Bool
  | .mk pats body => Expr2.listWfB d pats.toList && body.combOk d
termination_by structural it => it

def _root_.LeanModels.Sv.CaseItem2.listCombOk (d : Design2) : List CaseItem2 → Bool
  | [] => true
  | it :: rest => it.combOk d && CaseItem2.listCombOk d rest
termination_by structural l => l
end

/-- A qualifier's claim on the number of hitting arms (master `2218821b`, `checkCaseObligation`). -/
def caseClaim (check : CaseCheck) (hasDefault : Bool) (n : Nat) : Prop :=
  match check with
  | .none => True
  | .unique => n = 1 ∨ (n = 0 ∧ hasDefault = true)
  | .unique0 => n ≤ 1
  | .priority => 1 ≤ n ∨ hasDefault = true

mutual
/-- **Every qualified case on the executed path keeps its claim** (and every arm that could run
keeps its own: a hitting arm's body, the default when nothing hits). -/
def _root_.LeanModels.Sv.Stmt2.claims (d : Design2) : Stmt2 → SvState → Prop
  | .ifStmt c a b, st => if (ev st c).condTrue then a.claims d st else Stmt2.optClaims d b st
  | .block ss, st => Stmt2.listClaims d ss.toList st
  | .caseStmt subj items dflt mode check, st =>
      caseClaim check dflt.isSome
        (items.toList.filter fun it => armHit st (ev st subj) mode it.pats).length ∧
        CaseItem2.listClaims d (ev st subj) mode items.toList st ∧
        ((items.toList.filter fun it => armHit st (ev st subj) mode it.pats).length = 0 →
          Stmt2.optClaims d dflt st)
  | _, _ => True
termination_by structural s _ => s

def _root_.LeanModels.Sv.Stmt2.optClaims (d : Design2) : Option Stmt2 → SvState → Prop
  | none, _ => True
  | some s, st => s.claims d st
termination_by structural o _ => o

def _root_.LeanModels.Sv.Stmt2.listClaims (d : Design2) : List Stmt2 → SvState → Prop
  | [], _ => True
  | s :: ss, st => s.claims d st ∧ Stmt2.listClaims d ss (s.sem d st)
termination_by structural l _ => l

def _root_.LeanModels.Sv.CaseItem2.armClaims (d : Design2) (sv : LVec) (mode : CaseMode) :
    CaseItem2 → SvState → Prop
  | .mk pats body, st => armHit st sv mode pats = true → body.claims d st
termination_by structural it _ => it

def _root_.LeanModels.Sv.CaseItem2.listClaims (d : Design2) (sv : LVec) (mode : CaseMode) :
    List CaseItem2 → SvState → Prop
  | [], _ => True
  | it :: rest, st => it.armClaims d sv mode st ∧ CaseItem2.listClaims d sv mode rest st
termination_by structural l _ => l
end

/-! ## Soundness over E -/

/-- A declared name is bound in a typed view. -/
theorem bound_of_symNames {E : Elab} {σ : Store} (hT : E.Typed σ) {x : String}
    (hx : x ∈ E.toDesign2.symNames) : ∃ v, SvState.lookup (E.view σ) x = some v := by
  obtain ⟨dc, hdc, rfl⟩ := List.mem_map.mp hx
  have : (E.toDesign2.decls.toList.find? fun c => c.name == dc.name).isSome := by
    rw [List.find?_isSome]; exact ⟨dc, hdc, by simp⟩
  obtain ⟨dc', hf⟩ := Option.isSome_iff_exists.mp this
  obtain ⟨old, hold, -⟩ := Elab.lookup_declared hT (n := dc.name) (dw := dc'.width)
    (by rw [Design2.declWidth, hf]; rfl)
  exact ⟨old, hold⟩

theorem ev_ok {E : Elab} {σ : Store} (hT : E.Typed σ) {e : Expr2} (h : e.wfB E.toDesign2 = true) :
    evalPure2 (E.view σ) e = .ok (ev (E.view σ) e) := by
  obtain ⟨hu, hn⟩ := Expr2.wfB_spec h
  obtain ⟨v, hv⟩ := evalPure2_ok_of_wf hu fun x hx => bound_of_symNames hT (hn x hx)
  simp [ev, hv]

theorem evs_ok {E : Elab} {σ : Store} (hT : E.Typed σ) {es : List Expr2}
    (h : Expr2.listWfB E.toDesign2 es = true) :
    evalPures2 (E.view σ) es = .ok (evs (E.view σ) es) := by
  obtain ⟨hu, hn⟩ := Expr2.listWfB_spec h
  obtain ⟨v, hv⟩ := evalPures2_ok_of_wf hu fun x hx => bound_of_symNames hT (hn x hx)
  simp [evs, hv]

/-- What an activation of `s` does, on the store (the statement `sem_run` proves). -/
def RunsTo (E : Elab) (x : EM Unit) (σ : Store) (st : SvState) : Prop :=
  ∃ σ', x σ = .ok (.ok (), σ') ∧ E.Typed σ' ∧ E.view σ' = st

theorem caseClaimOk_of {chk : CaseCheck} {b : Bool} {n : Nat} (h : caseClaim chk b n) :
    caseClaimOk chk b n = true := by
  cases chk <;> simp_all [caseClaim, caseClaimOk]

/-- E's count of hitting arms is the claims' count. -/
theorem caseHits_ok {E : Elab} {σ : Store} (hT : E.Typed σ) (sv : LVec) (mode : CaseMode) :
    ∀ items : List CaseItem2, CaseItem2.listCombOk E.toDesign2 items = true → caseHits (E.view σ) sv mode
      items = .ok (items.filter fun it => armHit (E.view σ) sv mode it.pats).length
  | [], _ => rfl
  | .mk pats body :: rest, h => by
      simp only [CaseItem2.listCombOk, CaseItem2.combOk, Bool.and_eq_true] at h
      simp only [caseHits, evs_ok hT h.1.1, caseHits_ok hT sv mode rest h.2]
      have hb : ∀ {α β : Type} (a : α) (f : α → Res β), (Res.ok a >>= f) = f a := fun _ _ => rfl
      by_cases hh : armHit (E.view σ) sv mode pats = true <;> simp only [armHit] at hh <;>
        simp only [hb, List.filter_cons, CaseItem2.pats, armHit, hh, Bool.false_eq_true, ↓reduceIte,
          List.length_cons] <;> rfl

theorem listSem_none_count {d : Design2} {sv : LVec} {mode : CaseMode} {st : SvState} :
    ∀ items : List CaseItem2, CaseItem2.listSem d sv mode items st = none →
      (items.filter fun it => armHit st sv mode it.pats).length = 0
  | [], _ => rfl
  | .mk pats body :: rest, h => by
      by_cases hh : armHit st sv mode pats = true
      · simp [CaseItem2.listSem, CaseItem2.armSem, hh] at h
      · simp only [CaseItem2.listSem, CaseItem2.armSem, hh, Bool.false_eq_true, ↓reduceIte] at h
        simpa [List.filter_cons, CaseItem2.pats, hh] using listSem_none_count rest h

/-- A qualified `case` whose claim holds runs as a plain one (E checks it first, LRM 12.5.3). -/
theorem execBody_case_ok {E : Elab} {s : Store} {subj : Expr2} {items : Array CaseItem2}
    {dflt : Option Stmt2} {mode : CaseMode} {chk : CaseCheck} {sv : LVec} {n : Nat}
    (hm : caseModeInE0 mode = true) (hsv : evalPure2 (E.view s) subj = .ok sv)
    (hn : caseHits (E.view s) sv mode items.toList = .ok n)
    (hok : caseClaimOk chk dflt.isSome n = true) : execBody E (.caseStmt subj items dflt mode chk) s =
      (execArms E sv mode items.toList >>= fun hit => if hit then pure () else execBodyOpt E dflt) s := by
  cases chk
  · exact execBody_case_run rfl hm hsv
  all_goals
    simp only [execBody, hm, ↓reduceIte]
    rw [SemMWith.run_bind_ok (SemMWith.run_get s), SemMWith.run_bind_ok (show ofRes (evalPure2 (E.view s)
      subj) s = .ok (.ok sv, s) by rw [hsv]; rfl), SemMWith.run_bind_ok (show ofRes (caseHits (E.view s) sv
      mode items.toList) s = .ok (.ok n, s) by rw [hn]; rfl)]
    simp only [hok, if_true]

section
variable {E : Elab} (h4 : AllFour E)
include h4

mutual
theorem Stmt2.sem_runs : ∀ (s : Stmt2) (σ : Store), s.combOk E.toDesign2 = true → E.Typed σ →
    s.claims E.toDesign2 (E.view σ) → RunsTo E (execBody E s) σ (s.sem E.toDesign2 (E.view σ))
  | .blockingAssign t e, σ, h, hT, _ => by
      simp only [Stmt2.combOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
      obtain ⟨⟨⟨n, lo, w⟩, hW⟩, he⟩ := h
      obtain ⟨-, -, dw, hdw, -⟩ := Lhs2.staticWin_spec hW
      refine ⟨_, execBody_assign_run hW (ev_ok hT he), hT.writeWin _ _ _, ?_⟩
      rw [(view_writeWin_decl hT h4 hdw _ _).1]
      simp only [Stmt2.sem, hW]
  | .ifStmt c a b, σ, h, hT, hc => by
      simp only [Stmt2.combOk, Bool.and_eq_true] at h
      rw [RunsTo, execBody_if_run (ev_ok hT h.1.1)]
      simp only [Stmt2.sem]
      simp only [Stmt2.claims] at hc
      by_cases hC : (ev (E.view σ) c).condTrue = true
      · simp only [hC, ↓reduceIte] at hc ⊢; exact Stmt2.sem_runs a σ h.1.2 hT hc
      · simp only [hC, Bool.false_eq_true, ↓reduceIte] at hc ⊢; exact Stmt2.optSem_runs b σ h.2 hT hc
  | .block ss, σ, h, hT, hc => by
      rw [RunsTo, execBody_block]
      simp only [Stmt2.sem]
      exact Stmt2.listSem_runs ss.toList σ h hT hc
  | .caseStmt subj items dflt mode chk, σ, h, hT, hc => by
      simp only [Stmt2.combOk, Bool.and_eq_true] at h
      simp only [Stmt2.claims] at hc
      rw [RunsTo, execBody_case_ok h.1.1.1 (ev_ok hT h.1.1.2) (caseHits_ok hT _ mode _ h.1.2)
        (caseClaimOk_of hc.1)]
      simp only [Stmt2.sem]
      exact CaseItem2.listSem_runs (ev (E.view σ) subj) mode dflt items.toList σ h.1.2 hT hc.2.1
        fun hn => Stmt2.optSem_runs dflt σ h.2 hT (hc.2.2 (listSem_none_count _ hn))
  | .nbaAssign _ _, _, h, _, _ | .unsupported _ _, _, h, _, _ => by
      simp [Stmt2.combOk] at h
termination_by structural s => s

theorem Stmt2.optSem_runs : ∀ (b : Option Stmt2) (σ : Store), Stmt2.optCombOk E.toDesign2 b = true →
    E.Typed σ → Stmt2.optClaims E.toDesign2 b (E.view σ) →
      RunsTo E (execBodyOpt E b) σ (Stmt2.optSem E.toDesign2 b (E.view σ))
  | none, σ, _, hT, _ => ⟨σ, execBodyOpt_none E σ, hT, rfl⟩
  | some s, σ, h, hT, hc => by
      rw [RunsTo, execBodyOpt_some]; exact Stmt2.sem_runs s σ h hT hc
termination_by structural b => b

theorem Stmt2.listSem_runs : ∀ (l : List Stmt2) (σ : Store), Stmt2.listCombOk E.toDesign2 l = true →
    E.Typed σ → Stmt2.listClaims E.toDesign2 l (E.view σ) →
      RunsTo E (execBodyList E l) σ (Stmt2.listSem E.toDesign2 l (E.view σ))
  | [], σ, _, hT, _ => ⟨σ, execBodyList_nil E σ, hT, rfl⟩
  | s :: ss, σ, h, hT, hc => by
      simp only [Stmt2.listCombOk, Bool.and_eq_true] at h
      obtain ⟨σ₁, h₁, hT₁, hv₁⟩ := Stmt2.sem_runs s σ h.1 hT hc.1
      obtain ⟨σ₂, h₂, hT₂, hv₂⟩ := Stmt2.listSem_runs ss σ₁ h.2 hT₁ (by rw [hv₁]; exact hc.2)
      refine ⟨σ₂, by rw [execBodyList_cons, SemMWith.run_bind_ok h₁, h₂], hT₂, ?_⟩
      rw [hv₂, hv₁]; rfl
termination_by structural l => l

theorem CaseItem2.armSem_runs (sv : LVec) (mode : CaseMode) :
    ∀ (it : CaseItem2) (σ : Store), it.combOk E.toDesign2 = true → E.Typed σ →
      it.armClaims E.toDesign2 sv mode (E.view σ) →
      (it.armSem E.toDesign2 sv mode (E.view σ) = none →
        execArm E sv mode it σ = .ok (.ok false, σ)) ∧
      ∀ st, it.armSem E.toDesign2 sv mode (E.view σ) = some st →
        ∃ σ', execArm E sv mode it σ = .ok (.ok true, σ') ∧ E.Typed σ' ∧ E.view σ' = st
  | .mk pats body, σ, h, hT, hc => by
      simp only [CaseItem2.combOk, Bool.and_eq_true] at h
      rw [execArm_run (evs_ok hT h.1)]
      simp only [CaseItem2.armClaims] at hc
      simp only [CaseItem2.armSem, armHit] at hc ⊢
      by_cases hh : ((evs (E.view σ) pats.toList).any fun pv => caseHit mode sv pv) = true
      · refine ⟨fun hn => by simp [hh] at hn, fun st hst => ?_⟩
        simp only [hh, ↓reduceIte, Option.some.injEq] at hst
        obtain ⟨σ', h1, hT', hv⟩ := Stmt2.sem_runs body σ h.2 hT (hc hh)
        exact ⟨σ', by simp only [hh, ↓reduceIte]; rw [SemMWith.run_bind_ok h1]; rfl, hT', hv.trans hst⟩
      · refine ⟨fun _ => by simp only [hh, ↓reduceIte, Bool.false_eq_true]; rfl, fun st hst => ?_⟩
        simp [hh] at hst
termination_by structural it => it

theorem CaseItem2.listSem_runs (sv : LVec) (mode : CaseMode) (dflt : Option Stmt2) :
    ∀ (items : List CaseItem2) (σ : Store), CaseItem2.listCombOk E.toDesign2 items = true →
      E.Typed σ → CaseItem2.listClaims E.toDesign2 sv mode items (E.view σ) →
      (CaseItem2.listSem E.toDesign2 sv mode items (E.view σ) = none →
        RunsTo E (execBodyOpt E dflt) σ (Stmt2.optSem E.toDesign2 dflt (E.view σ))) →
      RunsTo E (execArms E sv mode items >>= fun hit => if hit then pure () else execBodyOpt E dflt) σ
        ((CaseItem2.listSem E.toDesign2 sv mode items (E.view σ)).getD
          (Stmt2.optSem E.toDesign2 dflt (E.view σ)))
  | [], σ, _, _, _, hd => by
      simp only [execArms, CaseItem2.listSem, Option.getD_none]
      rw [RunsTo, SemMWith.run_bind_ok (SemMWith.run_pure false σ)]
      exact hd rfl
  | it :: rest, σ, h, hT, hc, hd => by
      simp only [CaseItem2.listCombOk, Bool.and_eq_true] at h
      obtain ⟨hnone, hsome⟩ := CaseItem2.armSem_runs sv mode it σ h.1 hT hc.1
      simp only [CaseItem2.listSem]
      rw [RunsTo, execArms, bind_assoc]
      cases ha : it.armSem E.toDesign2 sv mode (E.view σ) with
      | none =>
          rw [SemMWith.run_bind_ok (hnone ha)]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact CaseItem2.listSem_runs sv mode dflt rest σ h.2 hT hc.2
            fun hn => hd (by simp [CaseItem2.listSem, ha, hn])
      | some st =>
          obtain ⟨σ', h1, hT', hv⟩ := hsome st ha
          refine ⟨σ', ?_, hT', by simpa using hv⟩
          rw [SemMWith.run_bind_ok h1]
          rfl
termination_by structural l => l
end
end

/-- **One activation of a fragment body over E-core-0** is its meaning, wherever every qualified
case on the executed path keeps its claim (E checks the claim and refuses loudly otherwise, LRM 12.5.3). -/
theorem Stmt2.sem_run {E : Elab} (h4 : AllFour E) {s : Stmt2} (h : s.combOk E.toDesign2 = true)
    {σ : Store} (hT : E.Typed σ) (hclaim : s.claims E.toDesign2 (E.view σ)) :
    ∃ σ', execBody E s σ = .ok (.ok (), σ') ∧ E.Typed σ' ∧
      E.view σ' = s.sem E.toDesign2 (E.view σ) :=
  Stmt2.sem_runs h4 s σ h hT hclaim

/-- **The single `always_comb` of a design, activated once by E-core-0**, is its body's meaning (the
design's E elaboration `Elab.ofDesign2`; claims as in `sem_run`). -/
theorem activate_single {d : Design2} {body : Stmt2} (hp : d.processes = #[.alwaysComb body])
    (h4 : AllFour (Elab.ofDesign2 d)) (h : body.combOk d = true) {σ : Store}
    (hT : (Elab.ofDesign2 d).Typed σ) (hc : body.claims d ((Elab.ofDesign2 d).view σ)) :
    ∃ σ', activate (Elab.ofDesign2 d) 0 σ = .ok (.ok (), σ') ∧ (Elab.ofDesign2 d).Typed σ' ∧
      (Elab.ofDesign2 d).view σ' = body.sem d ((Elab.ofDesign2 d).view σ) := by
  have hE : (Elab.ofDesign2 d).toDesign2 = d := Elab.toDesign2_ofDesign2 fun p hp' => by
    rw [hp] at hp'; simp only [List.mem_singleton] at hp'; subst hp'; rfl
  have hact : activate (Elab.ofDesign2 d) 0 σ = execBody (Elab.ofDesign2 d) body σ := by
    simp [activate, Elab.ofDesign2, hp, Proc0.ofProcess2]
  rw [hact]
  have := Stmt2.sem_run h4 (by rw [hE]; exact h) hT (by rw [hE]; exact hc)
  rwa [hE] at this

/-- A plain case arm on known values: equality. -/
theorem caseHit_ofBitVec {w : Nat} (x y : BitVec w) :
    caseHit .normal (LVec.ofBitVec x) (LVec.ofBitVec y) = decide (x = y) := by
  by_cases h : x = y <;> simp [caseHit, h]

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.activate_single LeanModels.Sv.Loop2.caseHit_ofBitVec LeanModels.Sv.Loop2.bound_of_symNames LeanModels.Sv.Loop2.ev_ok LeanModels.Sv.Loop2.evs_ok
  LeanModels.Sv.Loop2.Stmt2.sem_runs LeanModels.Sv.Loop2.CaseItem2.listSem_runs
  LeanModels.Sv.Loop2.Stmt2.sem_run LeanModels.Sv.Loop2.execBody_case_ok LeanModels.Sv.Loop2.caseHits_ok
