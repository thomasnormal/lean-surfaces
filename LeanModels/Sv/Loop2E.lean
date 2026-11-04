import LeanModels.Sv.Loop2Frag
import LeanModels.Sv.Kernel.Core0Proc

/-!
# The loop seam over E-core-0 (WS3) — *derived from E*; `Denotes.toE` is a *transport theorem*

`DenotesE` is the sibling of `run2`'s `Denotes` over E-core-0's `always_comb` execution
(`Kernel.execBody`, `Core0.lean`, fuel-free): from every typed store whose view satisfies `I`, one
`execBody` of the statement succeeds and ends in a typed store whose view is `g` of the view. It does
not replace `Denotes`; the two are related by `Denotes.toE`.

* **The five seam primitives over E**, one `Stmt2` construct each, proved from E's own arms (the
  owed arm lemmas `execBody_block`, `execBodyList_nil`, `execBodyList_cons` are named here):
  `DenotesE.block`, `DenotesLE.nil`/`cons`, `DenotesE.assignSliceE`, `DenotesE.assignE`,
  `DenotesE.ite`. E-core-0's write is the static in-range window (`Lhs2.staticWin`, LRM 10.4.1), so
  the two assignment primitives take the target's declared width, and the slice one `lo + w ≤ W`;
  the condition of an `if` is E's `condTrue`, as in `run2` (an x condition takes the else branch).
  Every primitive needs `AllFour E` (E-core-0's 4-state clause, for `Elab.view_writeWin`).
* **The recognizer over E** (`Stmt2.frag_denE`): `frag_rec`'s soundness, re-stated over `DenotesE` and
  proved from the five E primitives only (no `run2`), for the in-range instance of `fragOk`.
* **The whole-seam corollary** (`Denotes.toE`, a *transport theorem*): any `run2` `Denotes` fact of a
  static body (`Stmt2.staticB`) holds over E, through A's `execBody_of_execStmt2`; every fragment
  statement in range is static (`Stmt2.frag_static`).
-/

namespace LeanModels.Sv.Loop2

open Kernel

/-! ## `Denotes` over E-core-0 -/

/-- **`s` denotes `g` on E-core-0** on the views satisfying `I`. -/
def DenotesE (E : Elab) (I : SvState → Prop) (s : Stmt2) (g : SvState → SvState) : Prop :=
  ∀ σ, E.Typed σ → I (E.view σ) →
    ∃ σ', execBody E s σ = .ok (.ok (), σ') ∧ E.Typed σ' ∧ E.view σ' = g (E.view σ)

/-- `DenotesE` for a statement sequence (`execBodyList`). -/
def DenotesLE (E : Elab) (I : SvState → Prop) (ss : List Stmt2) (g : SvState → SvState) : Prop :=
  ∀ σ, E.Typed σ → I (E.view σ) →
    ∃ σ', execBodyList E ss σ = .ok (.ok (), σ') ∧ E.Typed σ' ∧ E.view σ' = g (E.view σ)

theorem DenotesE.congr {E : Elab} {I : SvState → Prop} {s : Stmt2} {g g' : SvState → SvState}
    (h : DenotesE E I s g) (he : ∀ st, I st → g st = g' st) : DenotesE E I s g' := fun σ hT hI =>
  let ⟨σ', h1, h2, h3⟩ := h σ hT hI
  ⟨σ', h1, h2, h3.trans (he _ hI)⟩

theorem DenotesLE.congr {E : Elab} {I : SvState → Prop} {ss : List Stmt2} {g g' : SvState → SvState}
    (h : DenotesLE E I ss g) (he : ∀ st, I st → g st = g' st) : DenotesLE E I ss g' := fun σ hT hI =>
  let ⟨σ', h1, h2, h3⟩ := h σ hT hI
  ⟨σ', h1, h2, h3.trans (he _ hI)⟩

/-! ## E's arms, named (owed in LOOP-NOTE §9.6's seam table) -/

theorem execBody_block (E : Elab) (arr : Array Stmt2) :
    execBody E (.block arr) = execBodyList E arr.toList := by
  simp only [execBody]

theorem execBodyList_nil (E : Elab) (σ : Store) : execBodyList E [] σ = .ok (.ok (), σ) := by
  simp only [execBodyList]; rfl

theorem execBodyList_cons (E : Elab) (s : Stmt2) (ss : List Stmt2) :
    execBodyList E (s :: ss) = (execBody E s >>= fun _ => execBodyList E ss) := by
  simp only [execBodyList]

theorem execBodyOpt_none (E : Elab) (σ : Store) : execBodyOpt E none σ = .ok (.ok (), σ) := by
  simp only [execBodyOpt]; rfl

theorem execBodyOpt_some (E : Elab) (s : Stmt2) : execBodyOpt E (some s) = execBody E s := by
  simp only [execBodyOpt]

/-! ## The seam primitives over E -/

theorem DenotesE.block {E : Elab} {I : SvState → Prop} {arr : Array Stmt2} {g : SvState → SvState}
    (h : DenotesLE E I arr.toList g) : DenotesE E I (.block arr) g := fun σ hT hI => by
  rw [execBody_block]; exact h σ hT hI

theorem DenotesLE.nil (E : Elab) (I : SvState → Prop) : DenotesLE E I [] id :=
  fun σ hT _ => ⟨σ, execBodyList_nil E σ, hT, rfl⟩

theorem DenotesLE.cons {E : Elab} {I : SvState → Prop} {s : Stmt2} {ss : List Stmt2}
    {g h : SvState → SvState} (hs : DenotesE E I s g) (hI : ∀ st, I st → I (g st))
    (hss : DenotesLE E I ss h) : DenotesLE E I (s :: ss) fun st => h (g st) := fun σ hT hIσ => by
  obtain ⟨σ1, h1, hT1, hv1⟩ := hs σ hT hIσ
  obtain ⟨σ2, h2, hT2, hv2⟩ := hss σ1 hT1 (by rw [hv1]; exact hI _ hIσ)
  exact ⟨σ2, by rw [execBodyList_cons, SemMWith.run_bind_ok h1, h2], hT2, by rw [hv2, hv1]⟩

theorem staticWin_ident {d : Design2} {n : String} {W : Nat} (hW : d.declWidth n = some W) :
    Lhs2.staticWin d (.ident n) = some (n, 0, W) := by
  simp [Lhs2.staticWin, Lhs2.window?, hW]

theorem staticWin_slice {d : Design2} {n : String} {lo w W : Nat} (hW : d.declWidth n = some W)
    (h : lo + w ≤ W) : Lhs2.staticWin d (.slice n lo w) = some (n, lo, w) := by
  simp [Lhs2.staticWin, Lhs2.window?, hW, h]

/-- E's write into a declared signal, on the view. -/
theorem view_writeWin_decl {E : Elab} {σ : Store} (hT : E.Typed σ) (h4 : AllFour E) {n : String}
    {W : Nat} (hW : E.toDesign2.declWidth n = some W) (lo : Nat) (p : LVec) :
    E.view (E.writeWin σ n lo p) = SvState.set (E.view σ) n ((sig (E.view σ) n).insertAt lo p) ∧
      (sig (E.view σ) n).width = W := by
  obtain ⟨old, hold, hw⟩ := Elab.lookup_declared hT hW
  rw [Elab.view_writeWin hT h4, hold]
  simp [sig, hold, hw]

/-- **A slice write** `n[lo +: w] = e` over E (seam primitive 3), the window in range. -/
theorem DenotesE.assignSliceE {E : Elab} (h4 : AllFour E) {I : SvState → Prop} {n : String}
    {lo w W : Nat} {e : Expr2} (hW : E.toDesign2.declWidth n = some W) (hlo : lo + w ≤ W)
    (hs : simpleExpr e = true) (hb : ∀ st, I st → ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v) :
    DenotesE E I (.blockingAssign (.slice n lo w) e) fun st =>
      SvState.set st n ((sig st n).insertAt lo ((valE st e).resizeU w)) := fun σ hT hI =>
  ⟨_, execBody_assign_run (staticWin_slice hW hlo) (evalPure2_valE hs (hb _ hI)),
    hT.writeWin _ _ _, (view_writeWin_decl hT h4 hW _ _).1⟩

/-- **A whole-signal write** `n = e` over E (seam primitive 4). -/
theorem DenotesE.assignE {E : Elab} (h4 : AllFour E) {I : SvState → Prop} {n : String} {W : Nat}
    {e : Expr2} (hW : E.toDesign2.declWidth n = some W) (hs : simpleExpr e = true)
    (hb : ∀ st, I st → ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v) :
    DenotesE E I (.blockingAssign (.ident n) e) fun st =>
      SvState.set st n ((valE st e).resizeU (sig st n).width) := fun σ hT hI => by
  refine ⟨_, execBody_assign_run (staticWin_ident hW) (evalPure2_valE hs (hb _ hI)),
    hT.writeWin _ _ _, ?_⟩
  obtain ⟨h1, h2⟩ := view_writeWin_decl hT h4 hW 0 ((valE (E.view σ) e).resizeU W)
  rw [h1, LVec.insertAt_zero_of_width_eq (by rw [width_resizeU, h2])]
  simp only [h2]

/-- **An `if`, with or without `else`**, over E (seam primitive 5). -/
theorem DenotesE.ite {E : Elab} {I : SvState → Prop} {c : Expr2} {a : Stmt2} {b : Option Stmt2}
    {ga gb : SvState → SvState} (hs : simpleExpr c = true)
    (hc : ∀ st, I st → ∀ x ∈ c.idents, ∃ v, SvState.lookup st x = some v) (ha : DenotesE E I a ga)
    (hb : match b with | none => gb = id | some e => DenotesE E I e gb) :
    DenotesE E I (.ifStmt c a b) fun st => if (valE st c).condTrue then ga st else gb st :=
  fun σ hT hI => by
    rw [execBody_if_run (evalPure2_valE hs (hc _ hI))]
    by_cases hC : (valE (E.view σ) c).condTrue = true
    · simp only [hC, ↓reduceIte]; exact ha σ hT hI
    · simp only [hC]
      cases b with
      | none => subst hb; exact ⟨σ, execBodyOpt_none E σ, hT, rfl⟩
      | some e => rw [execBodyOpt_some]; exact hb σ hT hI

/-! ## The recognizer over E -/

/-- **Every fragment statement in range runs to its `step` over E-core-0** (`frag_rec`'s soundness
over `DenotesE`, from the E primitives only). -/
theorem Stmt2.frag_denE {E : Elab} (h4 : AllFour E) {n : String} {ns : List String} {W : Nat}
    (hn : n ∈ ns) (hW : E.toDesign2.declWidth n = some W) :
    ∀ s : Stmt2, s.fragOk n (fun lo w => decide (lo + w ≤ W)) (fun x => decide (x ∈ ns)) = true →
      DenotesE E (BoundAll ns) s fun st => SvState.set st n (s.step n st (sig st n)) := by
  have hself : ∀ st, BoundAll ns st → SvState.set st n (sig st n) = st := fun st h => by
    obtain ⟨v, hv⟩ := h n hn
    rw [show sig st n = v by simp [sig, hv]]; exact set_self hv
  refine Stmt2.frag_rec _ (fun e he => ?_) (fun lo w e hl he => ?_) (fun c a b hc ha hb => ?_)
    (fun arr h => ?_)
  · exact (DenotesE.assignE h4 hW (exprOk_mem he).1 (exprOk_mem he).2).congr fun st h => by
      simp only [Stmt2.step, hself st h]
  · exact (DenotesE.assignSliceE h4 hW (by simpa using hl) (exprOk_mem he).1
      (exprOk_mem he).2).congr fun st h => by simp only [Stmt2.step, hself st h]
  · obtain ⟨hcs, hcb⟩ := exprOk_mem hc
    cases b with
    | none =>
        exact (DenotesE.ite (b := none) (gb := id) hcs hcb ha rfl).congr fun st h => by
          by_cases hC : (valE st c).condTrue = true <;> simp [Stmt2.step, Stmt2.optStep, hself st h, hC]
    | some e =>
        exact (DenotesE.ite (b := some e) hcs hcb ha (hb e rfl)).congr fun st h => by
          by_cases hC : (valE st c).condTrue = true <;> simp [Stmt2.step, Stmt2.optStep, hself st h, hC]
  · have key : ∀ l : List Stmt2, (∀ s ∈ l, DenotesE E (BoundAll ns) s
        fun st => SvState.set st n (s.step n st (sig st n))) →
        DenotesLE E (BoundAll ns) l fun st => SvState.set st n (Stmt2.listStep n st l (sig st n)) := by
      intro l
      induction l with
      | nil => exact fun _ => (DenotesLE.nil _ _).congr fun st h => by simp [Stmt2.listStep, hself st h]
      | cons s ss ih =>
          intro hl
          exact (DenotesLE.cons (hl s (List.mem_cons_self ..)) (fun st h => h.set n _)
            (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))).congr fun st _ => by
              simp only [Stmt2.listStep, sig_set_self, set_set, Stmt2.listStep_set]
    exact (DenotesE.block (key arr.toList h)).congr fun st _ => by simp only [Stmt2.step]

/-! ## The whole-seam corollary -/

/-- **Transport theorem (statement level)**: a `run2` `Denotes` fact of a static body holds over
E-core-0 (A's `execBody_of_execStmt2` at the `Denotes` fuel bound). -/
theorem Denotes.toE {E : Elab} (h4 : AllFour E) {I : SvState → Prop} {s : Stmt2}
    {g : SvState → SvState} (h : Denotes I s g) (hs : s.staticB E.toDesign2 = true) :
    DenotesE E I s g := fun σ hT hI => by
  obtain ⟨F, hF⟩ := h
  obtain ⟨-, σ', h1, h2, h3⟩ :=
    (execBody_of_execStmt2 h4 F).1 s σ [] _ [] hT hs (hF _ hI F (Nat.le_refl F))
  exact ⟨σ', h1, h3, h2⟩

theorem listStaticB_of {d : Design2} :
    ∀ {l : List Stmt2}, (∀ s ∈ l, s.staticB d = true) → Stmt2.listStaticB d l = true
  | [], _ => by simp only [Stmt2.listStaticB]
  | s :: ss, h => by
      simp only [Stmt2.listStaticB, h s (List.mem_cons_self ..), Bool.true_and]
      exact listStaticB_of fun t ht => h t (List.mem_cons_of_mem _ ht)

/-- **Every fragment statement in range is static** (what `Denotes.toE` asks of a loop body). -/
theorem Stmt2.frag_static {d : Design2} {n : String} {W : Nat} {rd : String → Bool}
    (hW : d.declWidth n = some W) :
    ∀ s : Stmt2, s.fragOk n (fun lo w => decide (lo + w ≤ W)) rd = true → s.staticB d = true := by
  refine Stmt2.frag_rec _ (fun e _ => ?_) (fun lo w e hl _ => ?_) (fun c a b _ ha hb => ?_)
    (fun arr h => ?_)
  · simp [Stmt2.staticB, staticWin_ident hW]
  · simp [Stmt2.staticB, staticWin_slice hW (by simpa using hl)]
  · simp only [Stmt2.staticB, ha, Bool.true_and]
    cases b with
    | none => rfl
    | some e => exact hb e rfl
  · simp only [Stmt2.staticB]; exact listStaticB_of h

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.DenotesE.congr LeanModels.Sv.Loop2.DenotesLE.congr
  LeanModels.Sv.Loop2.execBody_block LeanModels.Sv.Loop2.execBodyList_nil
  LeanModels.Sv.Loop2.execBodyList_cons LeanModels.Sv.Loop2.execBodyOpt_none
  LeanModels.Sv.Loop2.execBodyOpt_some LeanModels.Sv.Loop2.DenotesE.block
  LeanModels.Sv.Loop2.DenotesLE.nil LeanModels.Sv.Loop2.DenotesLE.cons
  LeanModels.Sv.Loop2.staticWin_ident LeanModels.Sv.Loop2.staticWin_slice
  LeanModels.Sv.Loop2.view_writeWin_decl LeanModels.Sv.Loop2.DenotesE.assignSliceE
  LeanModels.Sv.Loop2.DenotesE.assignE LeanModels.Sv.Loop2.DenotesE.ite
  LeanModels.Sv.Loop2.Stmt2.frag_denE LeanModels.Sv.Loop2.Denotes.toE
  LeanModels.Sv.Loop2.listStaticB_of LeanModels.Sv.Loop2.Stmt2.frag_static
