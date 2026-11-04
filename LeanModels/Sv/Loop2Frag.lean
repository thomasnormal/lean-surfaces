import LeanModels.Sv.Loop2Sem

/-!
# Loop bodies by recursion (`sv_loop_rows`, `sv_loop_sem`; WS3) — *provisional over `run2`*

A loop body is read by a **recursive recognizer**, not matched against a fixed shape: a trip may be
any statement of the fragment `Stmt2.fragOk n` — blocks (hence inner loops: an instantiated `for` is
a block of trips), `if`/`else` on simple conditions, and blocking assignments of simple expressions to
the whole of `n` or to a constant slice of it — and its meaning on `n` is COMPUTED, by structural
recursion, as a plain function of values (`Stmt2.step`, a derived view): what the run leaves in `n`,
the other signals read from the start state. One soundness theorem (`Stmt2.frag_den`), one guard
theorem (`Stmt2.frag_guard`) and one driver theorem (`Stmt2.frag_writes`) cover every statement of
the fragment, by one induction (`Stmt2.frag_rec`).

The body is `n = c; for k < N: T k` (`initLoop`), any fragment trip `T`. `sv_loop_rows` introduces

* `row_init : row st 0 = c.resizeU (sig st n).width`,
* `row_step : row st (k + 1) = <T k's step on row st k>`, evaluated by `simp` into a plain value
  equation (an `if` becomes an `if` on `condTrue`, an assignment its resized right-hand side),
* `row_width`, and `body_step : ∀ st, body.step n st (sig st n) = row st N`, the link to the body's
  meaning `initLoop.meaning` (whose run is `loop1_single` over `run2` and `Stmt2.frag_denE` over E);

and when a trip is itself a loop (a nest), its step is that loop's rows (`listStep_range`) and
`rows_nest` names them: `row_in`, `row_in_init : row_in st i 0 = row st i`, `row_in_step` (the inner
trip, a plain equation) and `row_next : row st (i + 1) = row_in st i N` replace `row_step`.

`sv_loop_sem` proves `X.sem N` is the loop process, through `sem_single` (the comb chain's
declaration staging, unchanged) and the ascending unit-step headers `it < P` and `it <= P` from any
literal start (`forValues2_up`).

**Backend seam** (five primitives): `Denotes.block` and `DenotesL.cons`/`nil` (`Loop2`),
`Denotes.assignSliceE` (`Loop2Rows`), and here `Denotes.assignE` (a whole-signal assignment) and
`Denotes.ite` (an `if`, with or without `else`): one `Stmt2` construct each, each meeting
`execStmt2` once and `evalExpr2` only through `evalExpr2_eq_evalPure2`. Everything else here is
about pure functions on `SvState`.
-/

namespace LeanModels.Sv.Loop2

open CombGuard

/-! ## The backend seam: two more primitives -/

/-- `Denotes` along a function equal on `I`. -/
theorem Denotes.congr {I : SvState → Prop} {s : Stmt2} {g g' : SvState → SvState}
    (h : Denotes I s g) (he : ∀ st, I st → g st = g' st) : Denotes I s g' :=
  let ⟨F, hF⟩ := h
  ⟨F, fun st hst fuel hf => (hF st hst fuel hf).trans (by rw [he st hst])⟩

theorem DenotesL.congr {I : SvState → Prop} {ss : List Stmt2} {g g' : SvState → SvState}
    (h : DenotesL I ss g) (he : ∀ st, I st → g st = g' st) : DenotesL I ss g' :=
  let ⟨F, hF⟩ := h
  ⟨F, fun st hst fuel hf => (hF st hst fuel hf).trans (by rw [he st hst])⟩

/-- **A whole-signal assignment** `n = e` of a simple expression (seam primitive). -/
theorem Denotes.assignE {I : SvState → Prop} {n : String} {e : Expr2} (hs : simpleExpr e = true)
    (hb : ∀ st, I st → ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v)
    (hn : ∀ st, I st → ∃ v, SvState.lookup st n = some v) :
    Denotes I (.blockingAssign (.ident n) e) fun st =>
      SvState.set st n ((valE st e).resizeU (sig st n).width) := by
  refine ⟨e.size + 2, fun st hst fuel hf => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨old, hold⟩ := hn st hst
  simp [execStmt2, evalExpr2_eq_evalPure2 (show e.size < f by omega), evalPure2_valE hs (hb st hst),
    resolveLhs2, hold, sig, LVec.insertAt_zero_of_width_eq]

/-- **An `if`, with or without `else`**, on a simple condition (seam primitive). -/
theorem Denotes.ite {I : SvState → Prop} {c : Expr2} {a : Stmt2} {b : Option Stmt2}
    {ga gb : SvState → SvState} (hs : simpleExpr c = true)
    (hc : ∀ st, I st → ∀ x ∈ c.idents, ∃ v, SvState.lookup st x = some v) (ha : Denotes I a ga)
    (hb : match b with | none => gb = id | some e => Denotes I e gb) :
    Denotes I (.ifStmt c a b) fun st => if (valE st c).condTrue then ga st else gb st := by
  obtain ⟨Fa, hFa⟩ := ha
  have hev : ∀ st, I st → ∀ f, c.size < f → evalExpr2 f st c = .ok (valE st c) := fun st h f hf => by
    rw [evalExpr2_eq_evalPure2 hf, evalPure2_valE hs (hc st h)]
  cases b with
  | none =>
      subst hb
      refine ⟨c.size + Fa + 2, fun st hst fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [execStmt2, hev st hst f (by omega), Res.ok_bind]
      split <;> simp_all [hFa st hst f (by omega)]
  | some e =>
      obtain ⟨Fb, hFb⟩ := hb
      refine ⟨c.size + Fa + Fb + 2, fun st hst fuel hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [execStmt2, hev st hst f (by omega), Res.ok_bind]
      split
      · simp_all [hFa st hst f (by omega)]
      · simp_all [hFb st hst f (by omega)]

/-! ## The fragment and its meaning on one signal -/

/-- An expression the fragment admits: simple, every identifier passing `rd`. -/
def exprOk (rd : String → Bool) (e : Expr2) : Bool := simpleExpr e && e.idents.all rd

mutual
/-- **The trip fragment writing only `n`**: blocks, `if`/`else` on admitted conditions, blocking
assignments of admitted expressions to `n` or to a slice `n[lo +: w]` passing `sl`. -/
def _root_.LeanModels.Sv.Stmt2.fragOk (n : String) (sl : Nat → Nat → Bool) (rd : String → Bool) : Stmt2 → Bool
  | .blockingAssign (.ident x) e => x == n && exprOk rd e
  | .blockingAssign (.slice x lo w) e => x == n && sl lo w && exprOk rd e
  | .ifStmt c a b => exprOk rd c && a.fragOk n sl rd && Stmt2.optFragOk n sl rd b
  | .block ss => Stmt2.listFragOk n sl rd ss.toList
  | _ => false
termination_by structural s => s

def _root_.LeanModels.Sv.Stmt2.optFragOk (n : String) (sl : Nat → Nat → Bool) (rd : String → Bool) : Option Stmt2 → Bool
  | none => true
  | some s => s.fragOk n sl rd
termination_by structural o => o

def _root_.LeanModels.Sv.Stmt2.listFragOk (n : String) (sl : Nat → Nat → Bool) (rd : String → Bool) : List Stmt2 → Bool
  | [] => true
  | s :: ss => s.fragOk n sl rd && Stmt2.listFragOk n sl rd ss
termination_by structural l => l
end

mutual
/-- **The fragment's meaning on `n`**: the value a run of `s` from `set st n v` leaves in `n` (the
other signals are read from `st`; nothing else is written). -/
def _root_.LeanModels.Sv.Stmt2.step (n : String) (st : SvState) : Stmt2 → LVec → LVec
  | .blockingAssign (.ident _) e, v => (valE (SvState.set st n v) e).resizeU v.width
  | .blockingAssign (.slice _ lo w) e, v => v.insertAt lo ((valE (SvState.set st n v) e).resizeU w)
  | .ifStmt c a b, v =>
      if (valE (SvState.set st n v) c).condTrue then a.step n st v else Stmt2.optStep n st b v
  | .block ss, v => Stmt2.listStep n st ss.toList v
  | _, v => v
termination_by structural s _ => s

def _root_.LeanModels.Sv.Stmt2.optStep (n : String) (st : SvState) : Option Stmt2 → LVec → LVec
  | none, v => v
  | some s, v => s.step n st v
termination_by structural o _ => o

def _root_.LeanModels.Sv.Stmt2.listStep (n : String) (st : SvState) : List Stmt2 → LVec → LVec
  | [], v => v
  | s :: ss, v => Stmt2.listStep n st ss (s.step n st v)
termination_by structural l _ => l
end

theorem Stmt2.listFragOk_iff {n : String} {sl : Nat → Nat → Bool} {rd : String → Bool} :
    ∀ {l : List Stmt2}, Stmt2.listFragOk n sl rd l = true ↔ ∀ s ∈ l, s.fragOk n sl rd = true
  | [] => by simp [Stmt2.listFragOk]
  | s :: ss => by simp [Stmt2.listFragOk, Stmt2.listFragOk_iff (l := ss)]

theorem Stmt2.listStep_append (n : String) (st : SvState) :
    ∀ (l₁ l₂ : List Stmt2) (v : LVec),
      Stmt2.listStep n st (l₁ ++ l₂) v = Stmt2.listStep n st l₂ (Stmt2.listStep n st l₁ v)
  | [], _, _ => rfl
  | s :: ss, l₂, v => Stmt2.listStep_append n st ss l₂ (s.step n st v)

mutual
/-- `n`'s own value in the start state is never read (the trip reads it through `v`). -/
theorem Stmt2.step_set (n : String) (st : SvState) (V : LVec) :
    ∀ (s : Stmt2) (v : LVec), s.step n (SvState.set st n V) v = s.step n st v
  | .blockingAssign (.ident _) _, _ | .blockingAssign (.slice _ _ _) _, _ => by
      simp only [Stmt2.step, set_set]
  | .blockingAssign (.index _ _ _) _, _ | .blockingAssign (.concat _) _, _ | .nbaAssign _ _, _
  | .caseStmt _ _ _ _ _, _ | .unsupported _ _, _ => by simp only [Stmt2.step]
  | .ifStmt c a b, v => by
      simp only [Stmt2.step, set_set, Stmt2.step_set n st V a v, Stmt2.optStep_set n st V b v]
  | .block ss, v => by simp only [Stmt2.step]; exact Stmt2.listStep_set n st V ss.toList v
termination_by structural s _ => s

theorem Stmt2.optStep_set (n : String) (st : SvState) (V : LVec) :
    ∀ (b : Option Stmt2) (v : LVec), Stmt2.optStep n (SvState.set st n V) b v = Stmt2.optStep n st b v
  | none, _ => rfl
  | some s, v => Stmt2.step_set n st V s v
termination_by structural b _ => b

theorem Stmt2.listStep_set (n : String) (st : SvState) (V : LVec) :
    ∀ (l : List Stmt2) (v : LVec), Stmt2.listStep n (SvState.set st n V) l v = Stmt2.listStep n st l v
  | [], _ => rfl
  | s :: ss, v => by
      simp only [Stmt2.listStep, Stmt2.step_set n st V s v]; exact Stmt2.listStep_set n st V ss _
termination_by structural l _ => l
end

mutual
/-- A trip keeps `n`'s width. -/
theorem Stmt2.width_step (n : String) (st : SvState) :
    ∀ (s : Stmt2) (v : LVec), (s.step n st v).width = v.width
  | .blockingAssign (.ident _) _, _ | .blockingAssign (.slice _ _ _) _, _ => by simp [Stmt2.step]
  | .blockingAssign (.index _ _ _) _, _ | .blockingAssign (.concat _) _, _ | .nbaAssign _ _, _
  | .caseStmt _ _ _ _ _, _ | .unsupported _ _, _ => by simp only [Stmt2.step]
  | .ifStmt c a b, v => by
      simp only [Stmt2.step]; split
      · exact Stmt2.width_step n st a v
      · exact Stmt2.width_optStep n st b v
  | .block ss, v => by simp only [Stmt2.step]; exact Stmt2.width_listStep n st ss.toList v
termination_by structural s _ => s

theorem Stmt2.width_optStep (n : String) (st : SvState) :
    ∀ (b : Option Stmt2) (v : LVec), (Stmt2.optStep n st b v).width = v.width
  | none, _ => rfl
  | some s, v => Stmt2.width_step n st s v
termination_by structural b _ => b

theorem Stmt2.width_listStep (n : String) (st : SvState) :
    ∀ (l : List Stmt2) (v : LVec), (Stmt2.listStep n st l v).width = v.width
  | [], _ => rfl
  | s :: ss, v => by
      simp only [Stmt2.listStep]; rw [Stmt2.width_listStep n st ss, Stmt2.width_step n st s v]
termination_by structural l _ => l
end

/-! ## One induction over the fragment -/

section rec
variable {n : String} {sl : Nat → Nat → Bool} {rd : String → Bool} (P : Stmt2 → Prop)
  (hid : ∀ e, exprOk rd e = true → P (.blockingAssign (.ident n) e))
  (hsl : ∀ lo w e, sl lo w = true → exprOk rd e = true → P (.blockingAssign (.slice n lo w) e))
  (hif : ∀ c a b, exprOk rd c = true → P a → (∀ e, b = some e → P e) → P (.ifStmt c a b))
  (hbl : ∀ arr : Array Stmt2, (∀ s ∈ arr.toList, P s) → P (.block arr))
include hid hsl hif hbl

mutual
/-- **Induction over the fragment**: a property of assignments to `n`, closed under `if` and blocks,
holds of every statement of the fragment. -/
theorem Stmt2.frag_rec : ∀ s : Stmt2, s.fragOk n sl rd = true → P s
  | .blockingAssign (.ident x) e, h => by
      simp only [Stmt2.fragOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h; exact hid e h
  | .blockingAssign (.slice x lo w) e, h => by
      simp only [Stmt2.fragOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, h1⟩, h2⟩ := h; exact hsl lo w e h1 h2
  | .ifStmt c a b, h => by
      simp only [Stmt2.fragOk, Bool.and_eq_true] at h
      exact hif c a b h.1.1 (Stmt2.frag_rec a h.1.2) (Stmt2.optFrag_rec b h.2)
  | .block ss, h => hbl ss (Stmt2.listFrag_rec ss.toList h)
  | .blockingAssign (.index _ _ _) _, h | .blockingAssign (.concat _) _, h | .nbaAssign _ _, h
  | .caseStmt _ _ _ _ _, h | .unsupported _ _, h => by simp [Stmt2.fragOk] at h
termination_by structural s => s

theorem Stmt2.optFrag_rec : ∀ b : Option Stmt2, Stmt2.optFragOk n sl rd b = true →
    ∀ e, b = some e → P e
  | none, _, _, h => nomatch h
  | some s, h, _, he => by have h1 := Stmt2.frag_rec s h; cases he; exact h1
termination_by structural b => b

theorem Stmt2.listFrag_rec : ∀ l : List Stmt2, Stmt2.listFragOk n sl rd l = true → ∀ s ∈ l, P s
  | [], _, _, h => nomatch h
  | s :: ss, h, t, ht => by
      simp only [Stmt2.listFragOk, Bool.and_eq_true] at h
      have h1 := Stmt2.frag_rec s h.1
      have h2 := Stmt2.listFrag_rec ss h.2
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h1
      · exact h2 t ht
termination_by structural l => l
end
end rec

/-! ## Soundness, the guard and the one-driver rule, once for the fragment -/

theorem exprOk_mem {ns : List String} {e : Expr2} (h : exprOk (fun x => decide (x ∈ ns)) e = true) :
    simpleExpr e = true ∧ ∀ st, BoundAll ns st → ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v := by
  simp only [exprOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun st hst x hx => hst x (h.2 x hx)⟩

/-- **Every trip of the fragment runs to its `step`** on the states binding `ns`. -/
theorem Stmt2.frag_den {n : String} {ns : List String} {sl : Nat → Nat → Bool} (hn : n ∈ ns) :
    ∀ s : Stmt2, s.fragOk n sl (fun x => decide (x ∈ ns)) = true →
      Denotes (BoundAll ns) s fun st => SvState.set st n (s.step n st (sig st n)) := by
  have hbn : ∀ st, BoundAll ns st → ∃ v, SvState.lookup st n = some v := fun st h => h n hn
  have hself : ∀ st, BoundAll ns st → SvState.set st n (sig st n) = st := fun st h => by
    obtain ⟨v, hv⟩ := hbn st h
    rw [show sig st n = v by simp [sig, hv]]; exact set_self hv
  refine Stmt2.frag_rec _ (fun e he => ?_) (fun lo w e _ he => ?_) (fun c a b hc ha hb => ?_)
    (fun arr h => ?_)
  · exact (Denotes.assignE (exprOk_mem he).1 (exprOk_mem he).2 hbn).congr fun st h => by
      simp only [Stmt2.step, hself st h]
  · exact (Denotes.assignSliceE (exprOk_mem he).1 (exprOk_mem he).2 hbn).congr fun st h => by
      simp only [Stmt2.step, hself st h]
  · obtain ⟨hcs, hcb⟩ := exprOk_mem hc
    cases b with
    | none =>
        exact (Denotes.ite (b := none) (gb := id) hcs hcb ha rfl).congr fun st h => by
          by_cases hC : (valE st c).condTrue = true <;> simp [Stmt2.step, Stmt2.optStep, hself st h, hC]
    | some e =>
        exact (Denotes.ite (b := some e) hcs hcb ha (hb e rfl)).congr fun st h => by
          by_cases hC : (valE st c).condTrue = true <;> simp [Stmt2.step, Stmt2.optStep, hself st h, hC]
  · have key : ∀ l : List Stmt2, (∀ s ∈ l, Denotes (BoundAll ns) s
        fun st => SvState.set st n (s.step n st (sig st n))) →
        DenotesL (BoundAll ns) l fun st => SvState.set st n (Stmt2.listStep n st l (sig st n)) := by
      intro l
      induction l with
      | nil => exact fun _ => (DenotesL.nil _).congr fun st h => by simp [Stmt2.listStep, hself st h]
      | cons s ss ih =>
          intro hl
          exact (DenotesL.cons (hl s (List.mem_cons_self ..)) (fun st h => h.set n _)
            (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))).congr fun st _ => by
              simp only [Stmt2.listStep, sig_set_self, set_set, Stmt2.listStep_set]
    exact (Denotes.block (key arr.toList h)).congr fun st _ => by simp only [Stmt2.step]

/-- An `if` whose branches are guard-safe is guard-safe (its condition reads only covered bits). -/
theorem GuardIn.ifStmt {wd : String → Option Nat} {M0 : List BWin} {c : Expr2} {a : Stmt2}
    {b : Option Stmt2} (ha : GuardIn wd M0 a) (hb : ∀ e, b = some e → GuardIn wd M0 e) :
    GuardIn wd M0 (.ifStmt c a b) := by
  have hbm : ∀ x ∈ Stmt2.optMayW wd b, Covered M0 x := by
    cases b with
    | none => simp [Stmt2.optMayW]
    | some e => exact (hb e rfl).1
  have hbv : ∀ M A, (∀ x, Covered M0 x → Covered M x) → (∀ x ∈ A, Covered M0 x) →
      Stmt2.optCombViol wd M A b = none := by
    cases b with
    | none => intros; rfl
    | some e => exact (hb e rfl).2
  refine ⟨fun x hx => ?_, fun M A hM hA => ?_⟩
  · simp only [Stmt2.mayW, List.mem_append] at hx
    exact hx.elim (ha.1 x) (hbm x)
  · have h1 : readsViol M (a.mayW wd ++ Stmt2.optMayW wd b ++ A) (c.rdW wd) = none :=
      readsViol_covered fun x hx => by
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hM x (ha.1 x hx)
        · exact hM x (hbm x hx)
        · exact hM x (hA x hx)
    simp only [Stmt2.combViol]
    rw [h1, ha.2 M A hM hA, hbv M A hM hA]
    rfl

/-- **Every trip of the fragment is guard-safe** under `n`'s whole window. -/
theorem Stmt2.frag_guard {wd : String → Option Nat} {n : String} {W : Nat} {rd : String → Bool}
    (hwd : wd n = some W) :
    ∀ s : Stmt2, s.fragOk n (fun lo w => decide (lo + w ≤ W)) rd = true → GuardIn wd [(n, 0, W)] s := by
  have cov : ∀ lo w, lo + w ≤ W → Covered [(n, 0, W)] (n, lo, w) := fun lo w h m k hm => by
    obtain ⟨h1, h2, h3⟩ := hm
    exact ⟨_, List.mem_singleton_self _, h1, Nat.zero_le _, by simp at h3 ⊢; omega⟩
  refine Stmt2.frag_rec _ (fun e _ => ?_) (fun lo w e h _ => ?_)
    (fun c a b _ ha hb => GuardIn.ifStmt ha hb) (fun arr h => GuardIn.block h)
  · exact GuardIn.assign fun x hx => by
      simp only [Lhs2.mayW, List.mem_singleton, whole, hwd, Option.getD_some] at hx
      subst hx; exact cov 0 W (by omega)
  · exact GuardIn.assign fun x hx => by
      simp only [Lhs2.mayW, List.mem_singleton] at hx
      subst hx; exact cov lo w (by simpa using h)

/-- **Every trip of the fragment writes only `n`.** -/
theorem Stmt2.frag_writes {n : String} {sl : Nat → Nat → Bool} {rd : String → Bool} :
    ∀ s : Stmt2, s.fragOk n sl rd = true → WritesOnly n s := by
  refine Stmt2.frag_rec _ (fun e _ => ?_) (fun lo w e _ _ => ?_) (fun c a b _ ha hb => ?_)
    (fun arr h => WritesOnly.block h)
  · intro w hw; simp [Stmt2.drvWins, Lhs2.drvWins] at hw; simp [hw]
  · intro w hw; simp [Stmt2.drvWins, Lhs2.drvWins] at hw; simp [hw]
  · intro w hw
    simp only [Stmt2.drvWins, List.mem_append] at hw
    rcases hw with hw | hw
    · exact ha w hw
    · cases b with
      | none => simp [Stmt2.drvWinsOpt] at hw
      | some e => exact hb e rfl w hw

/-! ## The one-level shape and its rows -/

/-- **The shape**: `n = c`, then `for k < N: T k`, every trip in the fragment. -/
def initLoop (n : String) (c : LVec) (N : Nat) (T : Nat → Stmt2) : Stmt2 :=
  .block #[.blockingAssign (.ident n) (.lit c), .block ((List.range N).map T).toArray]

theorem listStep_range (n : String) (st : SvState) (T : Nat → Stmt2) : ∀ (N : Nat) (v : LVec),
    Stmt2.listStep n st ((List.range N).map T) v = vrows (fun k st v => (T k).step n st v) st N v
  | 0, _ => rfl
  | N + 1, v => by
      rw [List.range_succ, List.map_append, Stmt2.listStep_append, listStep_range n st T N v]; rfl

theorem vrows_step_set (n : String) (st : SvState) (V : LVec) (T : Nat → Stmt2) : ∀ (k : Nat) (v : LVec),
    vrows (fun k st v => (T k).step n st v) (SvState.set st n V) k v =
      vrows (fun k st v => (T k).step n st v) st k v
  | 0, _ => rfl
  | k + 1, v => by simp only [vrows, Stmt2.step_set, vrows_step_set n st V T k v]

/-- The meaning of an `initLoop` body on its state: `n` takes the last row (`initLoop_step`). -/
def initLoop.meaning (n : String) (c : LVec) (N : Nat) (T : Nat → Stmt2) (st : SvState) : SvState :=
  SvState.set st n ((initLoop n c N T).step n st (sig st n))

/-- The rows of an `initLoop` body, from the start state. -/
def initLoop.row (n : String) (c : LVec) (T : Nat → Stmt2) (st : SvState) (k : Nat) : LVec :=
  vrows (fun k st v => (T k).step n st v) st k (c.resizeU (sig st n).width)

theorem initLoop_step (n : String) (c : LVec) (N : Nat) (T : Nat → Stmt2) (st : SvState) :
    (initLoop n c N T).step n st (sig st n) = initLoop.row n c T st N := by
  simp [initLoop, initLoop.row, Stmt2.step, Stmt2.listStep, valE, listStep_range]

theorem width_initLoop_row (n : String) (c : LVec) (T : Nat → Stmt2) (st : SvState) (k : Nat) :
    (initLoop.row n c T st k).width = (sig st n).width := by
  rw [initLoop.row, width_vrows fun k v => Stmt2.width_step n st (T k) v, width_resizeU]

/-- The meaning is idempotent (the init overwrites `n`, the trips read it through the row). -/
theorem initLoop_idem (n : String) (c : LVec) (N : Nat) (T : Nat → Stmt2) (st : SvState) :
    initLoop.meaning n c N T (initLoop.meaning n c N T st) = initLoop.meaning n c N T st := by
  have h1 : ∀ st, initLoop.meaning n c N T st = SvState.set st n (initLoop.row n c T st N) :=
    fun st => by rw [initLoop.meaning, initLoop_step]
  have h2 : ∀ V, V.width = (sig st n).width →
      initLoop.row n c T (SvState.set st n V) N = initLoop.row n c T st N := fun V hV => by
    simp only [initLoop.row, vrows_step_set, sig_set_self, hV]
  rw [h1, h1, set_set, h2 _ (width_initLoop_row n c T st N)]

/-- **The printed recurrence of the one-level shape** (what `sv_loop_rows` introduces): pure, no
backend; `body_step` links it to the body's meaning `Stmt2.step`. -/
theorem loop1_rows {body : Stmt2} {n : String} {c : LVec} {N : Nat} {T : Nat → Stmt2}
    (hbody : body = initLoop n c N T) :
    ∃ row : SvState → Nat → LVec,
      (∀ st, row st 0 = c.resizeU (sig st n).width) ∧
      (∀ st k, row st (k + 1) = (T k).step n st (row st k)) ∧
      (∀ st k, (row st k).width = (sig st n).width) ∧
      ∀ st, body.step n st (sig st n) = row st N := by
  subst hbody
  exact ⟨initLoop.row n c T, fun _ => rfl, fun _ _ => rfl, width_initLoop_row n c T,
    initLoop_step n c N T⟩

theorem listHasQualifiedCase_false : ∀ l : List Stmt2, (∀ s ∈ l, s.hasQualifiedCase = false) →
    Stmt2.listHasQualifiedCase l = false
  | [], _ => rfl
  | s :: ss, h => by simp [Stmt2.listHasQualifiedCase, h s (List.mem_cons_self ..),
      listHasQualifiedCase_false ss fun t ht => h t (List.mem_cons_of_mem _ ht)]

/-- The fragment has no `case`, so no qualified one (`SingleComb.noq`). -/
theorem Stmt2.noq_of_fragOk {n : String} {sl : Nat → Nat → Bool} {rd : String → Bool} (s : Stmt2)
    (h : s.fragOk n sl rd = true) : s.hasQualifiedCase = false :=
  Stmt2.frag_rec (fun s => s.hasQualifiedCase = false) (fun _ _ => by simp [Stmt2.hasQualifiedCase])
    (fun _ _ _ _ _ => by simp [Stmt2.hasQualifiedCase])
    (fun _ _ b _ ha hb => by cases b <;> simp_all [Stmt2.hasQualifiedCase])
    (fun _ h => by simpa [Stmt2.hasQualifiedCase] using listHasQualifiedCase_false _ h) s h

theorem initLoop_noq {n : String} {c : LVec} {N : Nat} {T : Nat → Stmt2} {sl : Nat → Nat → Bool}
    {rd : String → Bool} (hT : ∀ k, k < N → (T k).fragOk n sl rd = true) :
    (initLoop n c N T).hasQualifiedCase = false := by
  simpa [initLoop, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase] using
    listHasQualifiedCase_false _ fun s hs => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs; exact Stmt2.noq_of_fragOk _ (hT k (List.mem_range.mp hk))

/-- **The body over `run2`** (Bridge S's input): it runs to its meaning, keeps the names bound, and is
idempotent. -/
theorem loop1_single {n : String} {c : LVec} {N : Nat} {T : Nat → Stmt2} (ns : List String)
    (hn : n ∈ ns)
    (hT : ∀ k, k < N → (T k).fragOk n (fun _ _ => true) (fun x => decide (x ∈ ns)) = true) :
    SingleBody (BoundAll ns) (initLoop n c N T) (initLoop.meaning n c N T) := by
  have hfr : (initLoop n c N T).fragOk n (fun _ _ => true) (fun x => decide (x ∈ ns)) = true := by
    simp [initLoop, Stmt2.fragOk, Stmt2.listFragOk, Stmt2.listFragOk_iff, exprOk, simpleExpr,
      Expr2.idents, hn]
    exact hT
  exact ⟨Stmt2.frag_den hn _ hfr, fun st h => h.set n _, initLoop_idem n c N T⟩

/-- **The self-read guard admits the shape** when every slice lies inside `n`. -/
theorem loop1_admits {wd : String → Option Nat} {n : String} {c : LVec} {N W : Nat}
    {T : Nat → Stmt2} (hwd : wd n = some W)
    (hT : ∀ k, k < N → (T k).fragOk n (fun lo w => decide (lo + w ≤ W)) (fun _ => true) = true) :
    (initLoop n c N T).combAdmits wd = true :=
  GuardIn.admits (M0 := [(n, 0, W)])
    (fun A => by simp [Stmt2.combViol, Expr2.rdW, Lhs2.rdW, CombGuard.readsViol])
    (by simp [Stmt2.mustW, Lhs2.mustW, CombGuard.whole, hwd])
    (Stmt2.frag_guard hwd _ (by
      simp only [Stmt2.fragOk, Stmt2.listFragOk_iff, List.mem_map, List.mem_range]
      rintro _ ⟨k, hk, rfl⟩; exact hT k hk))

/-- The shape writes only `n`. -/
theorem loop1_writes {n : String} {c : LVec} {N : Nat} {T : Nat → Stmt2}
    (hT : ∀ k, k < N → (T k).fragOk n (fun _ _ => true) (fun _ => true) = true) :
    WritesOnly n (initLoop n c N T) :=
  Stmt2.frag_writes _ (by
    simp [initLoop, Stmt2.fragOk, Stmt2.listFragOk, Stmt2.listFragOk_iff, exprOk, simpleExpr,
      Expr2.idents]
    exact hT)


/-- **A trip that is itself a loop** (a nest): once the trip's step is evaluated, the outer row's
step is the inner loop's rows (`listStep_range`), and the inner row is named. Applies at any depth. -/
theorem rows_nest {row : SvState → Nat → LVec} {N : Nat} {H : Nat → Nat → SvState → LVec → LVec}
    (h : ∀ st i, row st (i + 1) = vrows (H i) st N (row st i)) :
    ∃ row_in : SvState → Nat → Nat → LVec, (∀ st i, row_in st i 0 = row st i) ∧
      (∀ st i j, row_in st i (j + 1) = H i j st (row_in st i j)) ∧
      ∀ st i, row st (i + 1) = row_in st i N :=
  ⟨fun st i j => vrows (H i) st j (row st i), fun _ _ => rfl, fun _ _ _ => rfl, h⟩

/-! ## The ascending unit-step headers against a parameter -/

/-- **`for (it = s; it < P; it++)` and `for (it = s; it <= P; it++)` instantiate to their trips**
`s, s+1, …` (`c.bound P - s` of them, none when negative), every value of `P`. -/
theorem forValues2_up {env : IEnv} {it p : String} {c : Cmp} (hc : c = .lt ∨ c = .le)
    (h : (env.vals.lookup p).isSome = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary c.op (.genvarRef it) (.paramRef p none))
      (.unary .inc (.genvarRef it)) = .ok (intRange s (c.bound (envVal env p) - s).toNat) := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp h
  have hl : ∀ u, (env.bindVal it u).vals.lookup p = some B := fun u => by
    rw [vals_lookup_bindVal_ne u hne, hB]
  rw [envVal_of_lookup hB]
  have hf : forFuel2 env it (.int s) (.binary c.op (.genvarRef it) (.paramRef p none))
      (.unary .inc (.genvarRef it)) = .ok ((c.bound B - s).toNat + 2) := by
    rcases hc with rfl | rfl
    · by_cases hsb : s < B
      · have h1 : ¬ (B - s < 0) := by omega
        simp [forFuel2, Cmp.op, Cmp.bound, evalInt_paramRef_of hB, Gen2.except_ok_bind, hsb, h1]
        rfl
      · have h1 : (B - s).toNat = 0 := by omega
        simp [forFuel2, Cmp.op, Cmp.bound, evalInt_paramRef_of hB, Gen2.except_ok_bind, hsb, h1]
        rfl
    · by_cases hsb : s ≤ B
      · have h1 : ¬ (B - s + 1 < 0) := by omega
        have h2 : B + 1 - s = B - s + 1 := by omega
        simp [forFuel2, Cmp.op, Cmp.bound, evalInt_paramRef_of hB, Gen2.except_ok_bind, hsb, h1, h2]
        rfl
      · have h1 : (B + 1 - s).toNat = 0 := by omega
        simp [forFuel2, Cmp.op, Cmp.bound, evalInt_paramRef_of hB, Gen2.except_ok_bind, hsb, h1]
        rfl
  rw [forValues2, hf]
  simp only [forValuesFuel2, evalInt_int, procStepDelta2_inc]
  rw [← TripSchema.toList_arith_one]
  have hg := guard_canon c (fun u => isInt_paramRef_of (hl u)) (fun u => evalInt_paramRef_of (hl u))
  apply forValuesFuel2_go_arith _ s _ (by omega)
  · intro k hk
    obtain ⟨r, hr, hiff⟩ := hg (s + k * 1)
    exact ⟨r, hr, hiff.mpr (by rw [Cmp.holds_iff]; rcases hc with rfl | rfl <;> simp [Cmp.sign, Cmp.bound] at * <;> omega)⟩
  · obtain ⟨r, hr, hiff⟩ := hg (s + ((c.bound B - s).toNat : Nat) * 1)
    rw [hr]
    by_cases h0 : r = 0
    · rw [h0]
    · exact absurd (hiff.mp h0) (by rw [Cmp.holds_iff]; rcases hc with rfl | rfl <;> simp [Cmp.sign, Cmp.bound] <;> omega)

/-- Trip values `s + k` from a nonnegative literal start, read back as `Nat` (instantiation). -/
theorem toNat_add_natCast {s : Int} (hs : 0 ≤ s) (k : Nat) : (s + (k : Int)).toNat = s.toNat + k := by
  omega

theorem le_add_natCast (s : Int) (k : Nat) : (s ≤ s + (k : Int)) = True := eq_true (by omega)

theorem forValues2_slt {env : IEnv} {it p : String} (h : (env.vals.lookup p).isSome = true)
    (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary .slt (.genvarRef it) (.paramRef p none))
      (.unary .inc (.genvarRef it)) = .ok (intRange s (envVal env p - s).toNat) :=
  forValues2_up (c := .lt) (.inl rfl) h hne s

theorem forValues2_sle {env : IEnv} {it p : String} (h : (env.vals.lookup p).isSome = true)
    (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary .sle (.genvarRef it) (.paramRef p none))
      (.unary .inc (.genvarRef it)) = .ok (intRange s (envVal env p + 1 - s).toNat) :=
  forValues2_up (c := .le) (.inr rfl) h hne s

/-! ## The tactics -/

/-- `sv_frag_ok [d₁, …]` closes a fragment side condition `s.fragOk n sl rd = true` (or one per trip,
`∀ k, k < N → …`) of a concrete-shape statement, slice bounds by `omega` (`d₁, …` unfold the
agent's names). -/
syntax (name := svFragOk) "sv_frag_ok" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| sv_frag_ok $[[$ds,*]]?) => do
    let ds : Array Lean.Ident := match ds with | some ds => ds.getElems | none => #[]
    let dsT : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ds.mapM fun d => `(Lean.Parser.Tactic.simpLemma| $d:ident)
    `(tactic| (simp [LeanModels.Sv.Stmt2.fragOk, LeanModels.Sv.Stmt2.optFragOk,
      LeanModels.Sv.Stmt2.listFragOk, LeanModels.Sv.Loop2.Stmt2.listFragOk_iff,
      LeanModels.Sv.Loop2.exprOk, LeanModels.Sv.Loop2.simpleExpr, LeanModels.Sv.Expr2.idents,
      LeanModels.Sv.Loop2.initLoop, $dsT,*] <;> (intros; omega)))

/-- `sv_loop_rows (body := B) [d₁, …]` on a body `B` of the `initLoop` shape (by unfolding):
introduces `row`, `row_init`, `row_step` (or, for a nest, `row_in`, `row_in_init`, `row_in_step`,
`row_next`), `row_width` and `body_step` (`loop1_rows`, no backend), with the trip's step evaluated
into a plain value equation (`d₁, …` unfold the agent's names in `B`). -/
syntax (name := svLoopRows) "sv_loop_rows " "(" &"body" " := " term ")" (" [" ident,* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| sv_loop_rows (body := $b) $[[$ds,*]]?) => do
    let ds : Array Lean.Ident := match ds with | some ds => ds.getElems | none => #[]
    let dsT : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ds.mapM fun d => `(Lean.Parser.Tactic.simpLemma| $d:ident)
    `(tactic| (
      obtain ⟨row, row_init, row_step, row_width, body_step⟩ :=
        LeanModels.Sv.Loop2.loop1_rows (body := $b) rfl
      simp only [LeanModels.Sv.Stmt2.step, LeanModels.Sv.Stmt2.optStep, LeanModels.Sv.Stmt2.listStep,
        List.toList_toArray, LeanModels.Sv.Loop2.listStep_range, LeanModels.Sv.Loop2.valE,
        LeanModels.Sv.Loop2.sig_set_self, $dsT,*] at row_step
      simp (disch := decide) only [LeanModels.Sv.Loop2.sig_set_ne] at row_step
      try (obtain ⟨row_in, row_in_init, row_in_step, row_next⟩ := LeanModels.Sv.Loop2.rows_nest row_step
           clear row_step
           try simp only at row_in_step)))

/-- `sv_loop_sem [d₁, …]` closes `X.sem N = ⟨name, decls, #[.alwaysComb B]⟩` for a flat
single-`always_comb` envelope whose instantiated body `B` is of the `initLoop` shape, its header
`it < P` or `it <= P` from a literal start (`d₁, …` unfold the agent's names in `B`). -/
syntax (name := svLoopSem) "sv_loop_sem" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| sv_loop_sem $[[$ds,*]]?) => do
    let ds : Array Lean.Ident := match ds with | some ds => ds.getElems | none => #[]
    let dsT : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ds.mapM fun d => `(Lean.Parser.Tactic.simpLemma| $d:ident)
    `(tactic| (
      refine LeanModels.Sv.Loop2.sem_single rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
      · simp [LeanModels.Sv.CombView.DeclT.toDecl, LeanModels.Sv.CombView.DeclT.width,
          LeanModels.Sv.CombView.dimsW, LeanModels.Sv.Loop2.envVal,
          LeanModels.Sv.CombView.Aff.eval, LeanModels.Sv.CombView.Aff.evalTerms,
          LeanModels.Sv.CombView.Aff.var, LeanModels.Sv.CombView.Aff.const,
          LeanModels.Sv.CombView.Aff.sub, LeanModels.Sv.CombView.Aff.add,
          LeanModels.Sv.CombView.Aff.neg, LeanModels.Sv.CombView.Aff.negTerms,
          LeanModels.Sv.CombView.Aff.scale, LeanModels.Sv.CombView.Aff.scaleTerms, $dsT,*] <;> omega
      · simp [instStmt2, instStmts2, LeanModels.Sv.Loop2.forValues2_slt,
          LeanModels.Sv.Loop2.forValues2_sle, LeanModels.Sv.Loop2.toNat_add_natCast,
          LeanModels.Sv.Loop2.le_add_natCast,
          LeanModels.Sv.Loop2.envVal_bindVal_ne, LeanModels.Sv.Loop2.lookup_isSome_bindVal_ne,
          intRange_zero, intRange_eq_map, List.map_map, Function.comp_def, LeanModels.Sv.Loop2.toNat_natCast_add,
          instLhs2, instLhsLeaf2, fitExpr2, instExpr2, rigidExpr, selfWidth2, evalInt, IEnv.bindVal,
          PExpr.isInt, SymBinOp.intArith, List.lookup, Gen2.except_ok_bind, ctxOpWidth2,
          rigidMax2, LeanModels.Sv.CombView.DeclT.elemW, LeanModels.Sv.Loop2.initLoop,
          Gen2.int_add_nonneg, LeanModels.Sv.Loop2.envVal, $dsT,*] <;> (try intros) <;> rfl
      · exact LeanModels.Sv.Loop2.loop1_admits rfl (by sv_frag_ok [$ds,*])
      · exact LeanModels.Sv.Loop2.driversOk_single
          (LeanModels.Sv.Loop2.loop1_writes (by sv_frag_ok [$ds,*])) (by decide)))

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.Denotes.congr LeanModels.Sv.Loop2.DenotesL.congr
  LeanModels.Sv.Loop2.Denotes.assignE LeanModels.Sv.Loop2.Denotes.ite
  LeanModels.Sv.Loop2.Stmt2.listFragOk_iff LeanModels.Sv.Loop2.Stmt2.listStep_append
  LeanModels.Sv.Loop2.Stmt2.step_set LeanModels.Sv.Loop2.Stmt2.width_step
  LeanModels.Sv.Loop2.Stmt2.frag_rec LeanModels.Sv.Loop2.exprOk_mem LeanModels.Sv.Loop2.Stmt2.frag_den
  LeanModels.Sv.Loop2.GuardIn.ifStmt LeanModels.Sv.Loop2.Stmt2.frag_guard
  LeanModels.Sv.Loop2.Stmt2.frag_writes LeanModels.Sv.Loop2.listStep_range
  LeanModels.Sv.Loop2.vrows_step_set LeanModels.Sv.Loop2.initLoop_step
  LeanModels.Sv.Loop2.width_initLoop_row LeanModels.Sv.Loop2.initLoop_idem LeanModels.Sv.Loop2.loop1_rows
  LeanModels.Sv.Loop2.loop1_single LeanModels.Sv.Loop2.loop1_admits
  LeanModels.Sv.Loop2.loop1_writes LeanModels.Sv.Loop2.rows_nest LeanModels.Sv.Loop2.forValues2_up LeanModels.Sv.Loop2.forValues2_slt
  LeanModels.Sv.Loop2.forValues2_sle LeanModels.Sv.Loop2.toNat_add_natCast LeanModels.Sv.Loop2.le_add_natCast
