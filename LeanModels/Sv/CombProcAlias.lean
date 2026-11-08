import LeanModels.Sv.CombProcLower
import LeanModels.Sv.CombAliasInert

/-!
# The `always_comb` alias guard admits a recognized design with procedural AND continuous sites

`X.sem N` is the alias-guarded family `PDesign.instantiateGDAlias2 X.pdesign [↑N]` (ls-sv 7c9b7ac59,
`CombAlias2.lean`): an `always_comb` body that reads a bit downstream, through the design's continuous
assignments, of a bit it writes at that statement or later becomes a loud `AlwaysComb:alias-read` process. The comb
theorems are stated for the unguarded family `PDesign.instantiateGD2`. `CombAliasInert.lean` shows the guard inert for
a design with no `always_comb` or no continuous assignment; this module covers a design the proc-aware recognizer
(`PDesign.summaryP`) reads that has BOTH, at every parameter point where the summary's obligations hold, from a
static check on the summary's NAMES (decided once by the kernel; nothing is assumed):

* `Summary.aliasOk s`: for every procedural site, the names `S` reached from the names it writes (`tgt :: more`)
  through at least one continuous site (`Summary.aliasEdges`: the names a plain site reads, to the name it drives)
  are closed under those edges (`aliasClosedB`, CHECKED, so the closure computation `aliasFan` needs no proof), and
  the site reads no name of `S`;
* `Summary.aliasGuard_eq`: the summary's obligations (those of `comb_viewL`) and `s.aliasOk = true` give
  `d.instantiateGDAlias2 args = d.instantiateGD2 args`.

## Why the names suffice

The guard's walk (`Stmt2.aliasViol`) compares every read window `R` of a body with `fanOut fl X`, the windows reached
from windows `X` the body may write through the flows `fl` of the continuous assignments
(`CombAliasCore.lean`). Every window of `fanOut fl X` is a write window of a flow that READS a window of the same
name as one of `X` or one already reached (`touches` needs a common bit, so a common name): its name is in any name
set `S` closed under the flows from the names of `X` (`fanOut_names`), and a read window of a name outside `S` meets
it in no bit (`aliasChk_none_names`). The walk itself is generic (`Stmt2.aliasViol_names`): it needs the names of the
body's may-writes in `WN` and every read window disjoint from `S` (`Stmt2.allRdW`).

At the parameter point the summary's soundness (`Summary.soundL`, `sound_prefix`, `pairs_ctx`) says what every
process of `d.instantiateGD2 args` is: a plain site's process is a continuous `assign` of its target access reading
only the windows of its read accesses (`Desc`), so its flow reads names of its reads and writes its target's name
(`Expr2.rdW_names`); a procedural site's process is the guarded tree statement (`proc_site_eq`) or body of segments
(`proc_body_eq`) over its target accesses, every expression of which reads only windows of its read accesses
(`low_noRead`, `noRdW_of_noRead` at every window of a name outside the reads). No process is anything else.

Axioms: `propext`, `Classical.choice`, `Quot.sound` (pinned at the end).
-/

namespace LeanModels.Sv

open CombGuard

mutual
/-- Every read window list the guard's walk compares (`Stmt2.aliasViol`) satisfies `Q`. -/
def Stmt2.allRdW (wd : String → Option Nat) (Q : BWin → Prop) : Stmt2 → Prop
  | .blockingAssign t e => ∀ r ∈ e.rdW wd ++ t.rdW wd, Q r
  | .nbaAssign t e => ∀ r ∈ e.rdW wd ++ t.rdW wd, Q r
  | .ifStmt c a b => (∀ r ∈ c.rdW wd, Q r) ∧ a.allRdW wd Q ∧ Stmt2.optAllRdW wd Q b
  | .block ss => Stmt2.listAllRdW wd Q ss.toList
  | .caseStmt subj its d _ _ =>
      (∀ r ∈ subj.rdW wd, Q r) ∧ CaseItem2.listAllRdW wd Q its.toList ∧ Stmt2.optAllRdW wd Q d
  | .unsupported _ _ => True
termination_by structural s => s

/-- `Stmt2.allRdW` of an optional statement. -/
def Stmt2.optAllRdW (wd : String → Option Nat) (Q : BWin → Prop) : Option Stmt2 → Prop
  | none => True
  | some s => s.allRdW wd Q
termination_by structural o => o

/-- `Stmt2.allRdW` of a statement list. -/
def Stmt2.listAllRdW (wd : String → Option Nat) (Q : BWin → Prop) : List Stmt2 → Prop
  | [] => True
  | s :: ss => s.allRdW wd Q ∧ Stmt2.listAllRdW wd Q ss
termination_by structural ss => ss

/-- `Stmt2.allRdW` of the arms of a `case` (patterns and bodies). -/
def CaseItem2.listAllRdW (wd : String → Option Nat) (Q : BWin → Prop) : List CaseItem2 → Prop
  | [] => True
  | .mk pats body :: rest =>
      (∀ r ∈ Expr2.listRdW wd pats.toList, Q r) ∧ body.allRdW wd Q ∧ CaseItem2.listAllRdW wd Q rest
termination_by structural its => its
end

namespace CombView
open CombEq CombProc CombGuard

/-! ## Names of the fan-out -/

/-- The name set `S` is closed under the flows `fl` from the names `WN`: a flow that reads a window of a name in
`WN` or in `S` writes only windows of names in `S`. -/
def AliasNamesClosed (fl : List AFlow) (WN S : String → Prop) : Prop :=
  ∀ x ∈ fl, (∃ r ∈ x.1, WN r.1 ∨ S r.1) → ∀ w ∈ x.2, S w.1

theorem inter_name_of_ne {a b : BWin} (h : (a.inter b).2.2 ≠ 0) : a.1 = b.1 := by
  unfold BWin.inter at h
  split at h
  · assumption
  · exact absurd rfl h

theorem inter_zero_of_name {a b : BWin} (h : a.1 ≠ b.1) : (a.inter b).2.2 = 0 :=
  Classical.byContradiction fun h' => h (inter_name_of_ne h')

theorem touches_name {F R : List BWin} (h : touches F R = true) : ∃ r ∈ R, ∃ f ∈ F, r.1 = f.1 := by
  unfold touches at h
  obtain ⟨r, hr, h⟩ := List.any_eq_true.mp h
  obtain ⟨f, hf, h⟩ := List.any_eq_true.mp h
  exact ⟨r, hr, f, hf, inter_name_of_ne (by simpa using h)⟩

theorem fanAux_names {fl : List AFlow} {A : List BWin} {WN S : String → Prop}
    (hcl : AliasNamesClosed fl WN S) (hA : ∀ a ∈ A, WN a.1) :
    ∀ (n : Nat) (rem : List AFlow) (acc : List BWin), (∀ x ∈ rem, x ∈ fl) → (∀ a ∈ acc, S a.1) →
      ∀ y ∈ fanAux n rem A acc, S y.1 := by
  intro n
  induction n with
  | zero => intro rem acc _ hacc y hy; exact hacc y (by simpa [fanAux] using hy)
  | succ n ih =>
    intro rem acc hsub hacc
    simp only [fanAux]
    split
    · exact hacc
    · apply ih
      · intro x hx
        simp only [missOf, List.mem_filter] at hx
        exact hsub x hx.1
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hacc a ha
        · obtain ⟨x, hx, hax⟩ := List.mem_flatMap.mp ha
          simp only [hitsOf, List.mem_filter] at hx
          obtain ⟨r, hr, f, hf, hrf⟩ := touches_name hx.2
          refine hcl x (hsub x hx.1) ⟨r, hr, ?_⟩ a hax
          rw [hrf]
          rcases List.mem_append.mp hf with hf | hf
          · exact Or.inl (hA f hf)
          · exact Or.inr (hacc f hf)

/-- **Every window of the fan-out has a name in a closed name set.** -/
theorem fanOut_names {fl : List AFlow} {A : List BWin} {WN S : String → Prop}
    (hcl : AliasNamesClosed fl WN S) (hA : ∀ a ∈ A, WN a.1) : ∀ y ∈ fanOut fl A, S y.1 :=
  fanAux_names hcl hA fl.length fl [] (fun _ h => h) (by simp)

/-- **The alias check by names**: the may-writes `X` have names in `WN`, and no read window meets a window of a name
of the closed set `S`. -/
theorem aliasChk_none_names {fl : List AFlow} {WN S : String → Prop} (hcl : AliasNamesClosed fl WN S)
    {X R : List BWin} (hX : ∀ x ∈ X, WN x.1) (hR : ∀ r ∈ R, ∀ V : BWin, S V.1 → (r.inter V).2.2 = 0) :
    aliasChk fl X R = none :=
  readsViol_none_ws [] (fanOut fl X) R (fanOut fl X) (fun _ hx => hx)
    (fun r hr V hV => hR r hr V (fanOut_names hcl hX V hV))

/-! ## The walk by names -/


/-- The read predicate of the walk: no read window meets a window of a name of `S`. -/
def AliasRdOk (S : String → Prop) (r : BWin) : Prop := ∀ V : BWin, S V.1 → (r.inter V).2.2 = 0

theorem orElse_none_left {α : Type} {x : Option α} (y : Option α) (h : x = none) : (x <|> y) = y := by
  subst h; rfl

section walk
variable {wd : String → Option Nat} {fl : List AFlow} {WN S : String → Prop}

mutual
/-- **The guard's walk finds nothing** when every may-write of the body (and every window written after it, `A`)
has a name in `WN`, `S` is closed under the flows from `WN`, and no read window meets a window of a name of `S`. -/
theorem Stmt2.aliasViol_names (hcl : AliasNamesClosed fl WN S) :
    ∀ (s : Stmt2) (A : List BWin), (∀ x ∈ A, WN x.1) → (∀ x ∈ s.mayW wd, WN x.1) →
      s.allRdW wd (AliasRdOk S) → s.aliasViol wd fl A = none
  | .blockingAssign t e, A, hA, hW, hR => by
      simp only [Stmt2.aliasViol]
      refine aliasChk_none_names hcl ?_ hR
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hW x (by simpa [Stmt2.mayW] using hx)
      · exact hA x hx
  | .nbaAssign t e, A, hA, _, hR => by
      simp only [Stmt2.aliasViol]
      exact aliasChk_none_names hcl hA hR
  | .ifStmt c a b, A, hA, hW, hR => by
      simp only [Stmt2.allRdW] at hR
      obtain ⟨hc, ha, hb⟩ := hR
      simp only [Stmt2.mayW] at hW
      have hWa : ∀ x ∈ a.mayW wd, WN x.1 := fun x hx => hW x (List.mem_append_left _ hx)
      have hWb : ∀ x ∈ Stmt2.optMayW wd b, WN x.1 := fun x hx => hW x (List.mem_append_right _ hx)
      have h1 : aliasChk fl (a.mayW wd ++ Stmt2.optMayW wd b ++ A) (c.rdW wd) = none := by
        refine aliasChk_none_names hcl ?_ hc
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hW x hx
        · exact hA x hx
      simp only [Stmt2.aliasViol]
      rw [orElse_none_left _ h1, orElse_none_left _ (Stmt2.aliasViol_names hcl a A hA hWa ha)]
      exact Stmt2.optAliasViol_names hcl b A hA hWb hb
  | .block ss, A, hA, hW, hR => by
      simp only [Stmt2.aliasViol]
      simp only [Stmt2.allRdW] at hR
      simp only [Stmt2.mayW] at hW
      exact Stmt2.listAliasViol_names hcl ss.toList A hA hW hR
  | .caseStmt subj its d _ _, A, hA, hW, hR => by
      simp only [Stmt2.allRdW] at hR
      obtain ⟨hs, hi, hd⟩ := hR
      simp only [Stmt2.mayW] at hW
      have hWi : ∀ x ∈ CaseItem2.listMayW wd its.toList, WN x.1 :=
        fun x hx => hW x (List.mem_append_left _ hx)
      have hWd : ∀ x ∈ Stmt2.optMayW wd d, WN x.1 := fun x hx => hW x (List.mem_append_right _ hx)
      have h1 : aliasChk fl (CaseItem2.listMayW wd its.toList ++ Stmt2.optMayW wd d ++ A) (subj.rdW wd) = none := by
        refine aliasChk_none_names hcl ?_ hs
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hW x hx
        · exact hA x hx
      simp only [Stmt2.aliasViol]
      rw [orElse_none_left _ h1]
      exact CaseItem2.listAliasViol_names hcl A (Stmt2.optMayW wd d) (Stmt2.optAliasViol wd fl A d)
        (Stmt2.optAliasViol_names hcl d A hA hWd hd) hWd its.toList hA hWi hi
  | .unsupported _ _, _, _, _, _ => by simp only [Stmt2.aliasViol]
termination_by structural s => s

theorem Stmt2.optAliasViol_names (hcl : AliasNamesClosed fl WN S) :
    ∀ (o : Option Stmt2) (A : List BWin), (∀ x ∈ A, WN x.1) → (∀ x ∈ Stmt2.optMayW wd o, WN x.1) →
      Stmt2.optAllRdW wd (AliasRdOk S) o → Stmt2.optAliasViol wd fl A o = none
  | none, _, _, _, _ => rfl
  | some s, A, hA, hW, hR => by
      simp only [Stmt2.optMayW] at hW
      simp only [Stmt2.optAllRdW] at hR
      exact Stmt2.aliasViol_names hcl s A hA hW hR
termination_by structural o => o

theorem Stmt2.listAliasViol_names (hcl : AliasNamesClosed fl WN S) :
    ∀ (ss : List Stmt2) (A : List BWin), (∀ x ∈ A, WN x.1) → (∀ x ∈ Stmt2.listMayW wd ss, WN x.1) →
      Stmt2.listAllRdW wd (AliasRdOk S) ss → Stmt2.listAliasViol wd fl A ss = none
  | [], _, _, _, _ => rfl
  | s :: ss, A, hA, hW, hR => by
      simp only [Stmt2.listAllRdW] at hR
      simp only [Stmt2.listMayW] at hW
      have hWs : ∀ x ∈ Stmt2.listMayW wd ss, WN x.1 := fun x hx => hW x (List.mem_append_right _ hx)
      have hA' : ∀ x ∈ Stmt2.listMayW wd ss ++ A, WN x.1 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hWs x hx
        · exact hA x hx
      simp only [Stmt2.listAliasViol]
      rw [orElse_none_left _ (Stmt2.aliasViol_names hcl s _ hA'
        (fun x hx => hW x (List.mem_append_left _ hx)) hR.1)]
      exact Stmt2.listAliasViol_names hcl ss A hA hWs hR.2
termination_by structural ss => ss

theorem CaseItem2.listAliasViol_names (hcl : AliasNamesClosed fl WN S) (A dA : List BWin)
    (dV : Option BWin) (hdV : dV = none) (hdA : ∀ x ∈ dA, WN x.1) :
    ∀ (its : List CaseItem2), (∀ x ∈ A, WN x.1) → (∀ x ∈ CaseItem2.listMayW wd its, WN x.1) →
      CaseItem2.listAllRdW wd (AliasRdOk S) its → CaseItem2.listAliasViol wd fl A dA dV its = none
  | [], _, _, _ => hdV
  | .mk pats body :: rest, hA, hW, hR => by
      simp only [CaseItem2.listAllRdW] at hR
      obtain ⟨hp, hb, hr⟩ := hR
      simp only [CaseItem2.listMayW, CaseItem2.mayW] at hW
      have hWb : ∀ x ∈ body.mayW wd, WN x.1 := fun x hx => hW x (List.mem_append_left _ hx)
      have hWr : ∀ x ∈ CaseItem2.listMayW wd rest, WN x.1 := fun x hx => hW x (List.mem_append_right _ hx)
      have h1 : aliasChk fl (body.mayW wd ++ CaseItem2.listMayW wd rest ++ dA ++ A)
          (Expr2.listRdW wd pats.toList) = none := by
        refine aliasChk_none_names hcl ?_ hp
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with ((hx | hx) | hx) | hx
        · exact hWb x hx
        · exact hWr x hx
        · exact hdA x hx
        · exact hA x hx
      simp only [CaseItem2.listAliasViol]
      rw [orElse_none_left _ h1, orElse_none_left _ (Stmt2.aliasViol_names hcl body A hA hWb hb)]
      exact CaseItem2.listAliasViol_names hcl A dA dV hdV hdA rest hA hWr hr
termination_by structural its => its
end

end walk

/-! ## The reads of a recognized body -/

theorem listRdAll_append (wd : String → Option Nat) (Q : BWin → Prop) :
    ∀ (l1 l2 : List Stmt2), Stmt2.listAllRdW wd Q l1 → Stmt2.listAllRdW wd Q l2 →
      Stmt2.listAllRdW wd Q (l1 ++ l2)
  | [], _, _, h2 => h2
  | s :: r, l2, h1, h2 => by
      simp only [Stmt2.listAllRdW] at h1
      simp only [List.cons_append, Stmt2.listAllRdW]
      exact ⟨h1.1, listRdAll_append wd Q r l2 h1.2 h2⟩

theorem listAllRdW_baseL (wd : String → Option Nat) (Q : BWin → Prop) (tgt : Lhs2) (b : PTree)
    (h : (b.toStmt tgt).allRdW wd Q) : Stmt2.listAllRdW wd Q (b.baseL (b.toStmt tgt)) := by
  unfold PTree.baseL
  split
  · rename_i ho
    cases b <;> simp [PTree.isOvr] at ho
    simp only [PTree.toStmt, Stmt2.unblock]
    simpa only [PTree.toStmt, Stmt2.allRdW] using h
  · simp only [Stmt2.listAllRdW]
    exact ⟨h, trivial⟩

theorem caseItems_rdAll (wd : String → Option Nat) (P : BWin → Prop) (tgt : Lhs2) (hr : tgt.rdW wd = []) :
    ∀ its : List (List Expr2 × Expr2), (∀ V, P V → CasesNoRdW wd V its) →
      CaseItem2.listAllRdW wd (fun r => ∀ V, P V → (r.inter V).2.2 = 0) (caseItems tgt its)
  | [], _ => by simp [caseItems, CaseItem2.listAllRdW]
  | (ps, e) :: rest, h => by
      simp only [caseItems, CaseItem2.listAllRdW, Stmt2.allRdW, hr, List.append_nil]
      refine ⟨fun r hr' V hV => ((h V hV) (ps, e) (List.mem_cons_self ..)).1 r hr',
        fun r hr' V hV => ((h V hV) (ps, e) (List.mem_cons_self ..)).2 r hr',
        caseItems_rdAll wd P tgt hr rest (fun V hV x hx => h V hV x (List.mem_cons_of_mem _ hx))⟩

/-- **The reads of a tree statement**: every read window meets every window of the family `P` in no bit, when the
tree does (`PTree.noRdW`) and its target reads nothing. -/
theorem tree_rdAll (wd : String → Option Nat) (P : BWin → Prop) (tgt : Lhs2) (hr : tgt.rdW wd = []) :
    ∀ t : PTree, (∀ V, P V → t.noRdW wd V) →
      (t.toStmt tgt).allRdW wd (fun r => ∀ V, P V → (r.inter V).2.2 = 0) := by
  intro t
  induction t with
  | leaf e =>
      intro h
      simp only [PTree.toStmt, Stmt2.allRdW, hr, List.append_nil]
      exact fun r hr' V hV => h V hV r hr'
  | ite c a b iha ihb =>
      intro h
      simp only [PTree.toStmt, Stmt2.allRdW, Stmt2.optAllRdW]
      exact ⟨fun r hr' V hV => (h V hV).1 r hr', iha (fun V hV => (h V hV).2.1),
        ihb (fun V hV => (h V hV).2.2)⟩
  | blk t iht =>
      intro h
      simp only [PTree.toStmt, Stmt2.allRdW, Stmt2.listAllRdW]
      exact ⟨iht h, trivial⟩
  | cases s its dd =>
      intro h
      simp only [PTree.toStmt, Stmt2.allRdW, Stmt2.optAllRdW, hr, List.append_nil]
      exact ⟨fun r hr' V hV => (h V hV).1 r hr', caseItems_rdAll wd P tgt hr its (fun V hV => (h V hV).2.1),
        fun r hr' V hV => (h V hV).2.2 r hr'⟩
  | ovr c a b iha ihb =>
      intro h
      simp only [PTree.toStmt, Stmt2.allRdW]
      refine listRdAll_append wd _ _ _ (listAllRdW_baseL wd _ tgt b (ihb (fun V hV => (h V hV).2.2))) ?_
      simp only [Stmt2.listAllRdW, Stmt2.allRdW, Stmt2.optAllRdW]
      exact ⟨⟨fun r hr' V hV => (h V hV).1 r hr', iha (fun V hV => (h V hV).2.1), trivial⟩, trivial⟩

/-- … and of a body of segments. -/
theorem bodyStmts_rdAll (wd : String → Option Nat) (P : BWin → Prop) :
    ∀ segs : List Seg, (∀ sg ∈ segs, sg.tgt.rdW wd = [] ∧ ∀ V, P V → sg.t.noRdW wd V) →
      Stmt2.listAllRdW wd (fun r => ∀ V, P V → (r.inter V).2.2 = 0) (bodyStmts segs)
  | [], _ => by simp [bodyStmts, Stmt2.listAllRdW]
  | sg :: rest, h => by
      have hsg := h sg (List.mem_cons_self ..)
      simp only [bodyStmts]
      exact listRdAll_append wd _ _ _
        (listAllRdW_baseL wd _ sg.tgt sg.t (tree_rdAll wd P sg.tgt hsg.1 sg.t hsg.2))
        (bodyStmts_rdAll wd P rest (fun s hs => h s (List.mem_cons_of_mem _ hs)))

/-- The may-writes of a body of segments have the names of the segments' targets. -/
theorem bodyStmts_mayW_names (wd : String → Option Nat) (N : String → Prop) :
    ∀ segs : List Seg, (∀ sg ∈ segs, ∃ W, sg.tgt.mayW wd = [W] ∧ N W.1) →
      ∀ x ∈ Stmt2.listMayW wd (bodyStmts segs), N x.1
  | [], _ => by intro x hx; simp [bodyStmts, Stmt2.listMayW] at hx
  | sg :: rest, h => by
      intro x hx
      simp only [bodyStmts, listMayW_append, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨W, hm, hn⟩ := h sg (List.mem_cons_self ..)
        simp only [Seg.stmts, listMayW_baseL] at hx
        rw [mayW_tree wd sg.tgt W hm sg.t x hx]
        exact hn
      · exact bodyStmts_mayW_names wd N rest (fun s hs => h s (List.mem_cons_of_mem _ hs)) x hx

/-! ## The flows and bodies of a recognized design -/

/-- The lowered target of an access may write exactly one window, of the access's name, in every design. -/
theorem Acc.lhs_mayW (σ : String → Int) (wd : String → Option Nat) (a : Acc) :
    ∃ W, (a.lhs σ).mayW wd = [W] ∧ W.1 = a.name := by
  cases a <;> simp [Acc.lhs, Lhs2.mayW, CombGuard.whole, Acc.name]

/-- … and reads nothing. -/
theorem Acc.lhs_rdW (σ : String → Int) (wd : String → Option Nat) (a : Acc) : (a.lhs σ).rdW wd = [] := by
  cases a <;> rfl

/-- A read window overlaps no window of another name. -/
theorem ReadWin.overlaps_of_name_ne {r : ReadWin} {V : Win} (h : r.name ≠ V.1) : r.overlaps V = false := by
  obtain ⟨m, lo, w⟩ := V
  cases r with
  | whole n =>
      simp only [ReadWin.name] at h
      simp [ReadWin.overlaps, h]
  | win n lo' w' =>
      simp only [ReadWin.name] at h
      simp [ReadWin.overlaps, Win.overlaps, h]

/-- The reads of a select keep the names of its operands' reads. -/
theorem indexReads_cover (a i : Expr2) (ew : Nat) :
    ∀ q ∈ a.reads ++ i.reads, ∃ q' ∈ Expr2.indexReads a i ew (a.reads ++ i.reads), q'.name = q.name := by
  intro q hq
  unfold Expr2.indexReads
  split
  · split
    · simp [Expr2.reads] at hq
      subst hq
      exact ⟨_, List.mem_singleton_self _, rfl⟩
    · exact ⟨q, hq, rfl⟩
  · exact ⟨q, hq, rfl⟩

set_option linter.unnecessarySimpa false in
theorem rdW_names_aux (wd : String → Option Nat) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → ∀ x ∈ e.rdW wd, ∃ q ∈ e.reads, q.name = x.1) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → ∀ x ∈ Expr2.listRdW wd l, ∃ q ∈ Expr2.listReads l, q.name = x.1) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h => by omega, fun l h => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he x hx => ?_, fun l hl x hx => ?_⟩
    · cases e with
      | lit v => simp [Expr2.rdW] at hx
      | unsupported k t => simp [Expr2.rdW] at hx
      | ident m =>
          simp only [Expr2.rdW, List.mem_singleton] at hx; subst hx
          exact ⟨.whole m, by simp [Expr2.reads], rfl⟩
      | unary op a =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihe a (by omega) x (by simpa [Expr2.rdW] using hx)
      | resizeSigned w a =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihe a (by omega) x (by simpa [Expr2.rdW] using hx)
      | squash2 a =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihe a (by omega) x (by simpa [Expr2.rdW] using hx)
      | repl k a =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihe a (by omega) x (by simpa [Expr2.rdW] using hx)
      | reduce op a =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihe a (by omega) x (by simpa [Expr2.rdW] using hx)
      | resize w a =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihe a (by omega) x (by simpa [Expr2.rdW] using hx)
      | binary op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.rdW, List.mem_append] at hx
          simp only [Expr2.reads, List.mem_append]
          rcases hx with hx | hx
          · obtain ⟨q, hq, h⟩ := ihe l (by omega) x hx; exact ⟨q, Or.inl hq, h⟩
          · obtain ⟨q, hq, h⟩ := ihe r (by omega) x hx; exact ⟨q, Or.inr hq, h⟩
      | scmp op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.rdW, List.mem_append] at hx
          simp only [Expr2.reads, List.mem_append]
          rcases hx with hx | hx
          · obtain ⟨q, hq, h⟩ := ihe l (by omega) x hx; exact ⟨q, Or.inl hq, h⟩
          · obtain ⟨q, hq, h⟩ := ihe r (by omega) x hx; exact ⟨q, Or.inr hq, h⟩
      | logical b l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.rdW, List.mem_append] at hx
          simp only [Expr2.reads, List.mem_append]
          rcases hx with hx | hx
          · obtain ⟨q, hq, h⟩ := ihe l (by omega) x hx; exact ⟨q, Or.inl hq, h⟩
          · obtain ⟨q, hq, h⟩ := ihe r (by omega) x hx; exact ⟨q, Or.inr hq, h⟩
      | ternary c t f =>
          simp only [Expr2.size] at he
          simp only [Expr2.rdW, List.mem_append] at hx
          simp only [Expr2.reads, List.mem_append]
          rcases hx with hx | hx | hx
          · obtain ⟨q, hq, h⟩ := ihe c (by omega) x hx; exact ⟨q, Or.inl (Or.inl hq), h⟩
          · obtain ⟨q, hq, h⟩ := ihe t (by omega) x hx; exact ⟨q, Or.inl (Or.inr hq), h⟩
          · obtain ⟨q, hq, h⟩ := ihe f (by omega) x hx; exact ⟨q, Or.inr hq, h⟩
      | slice a lo w =>
          simp only [Expr2.size] at he
          have ih := ihe a (by omega)
          cases a with
          | ident m =>
              simp only [Expr2.rdW, sliceRd, List.mem_singleton] at hx; subst hx
              exact ⟨.win m lo w, by simp [Expr2.reads, Expr2.sliceReads], rfl⟩
          | _ =>
              first
              | (simpa [Expr2.reads, Expr2.sliceReads] using
                  ih x (by simpa only [Expr2.rdW, sliceRd] using hx))
      | index a i ew =>
          simp only [Expr2.size] at he
          simp only [Expr2.rdW, List.mem_append] at hx
          have hdflt : ∃ q ∈ a.reads ++ i.reads, q.name = x.1 := by
            rcases hx with hx | hx
            · obtain ⟨q, hq, h⟩ := ihe a (by omega) x hx; exact ⟨q, List.mem_append_left _ hq, h⟩
            · obtain ⟨q, hq, h⟩ := ihe i (by omega) x hx; exact ⟨q, List.mem_append_right _ hq, h⟩
          obtain ⟨q, hq, h⟩ := hdflt
          obtain ⟨q', hq', h'⟩ := indexReads_cover a i ew q hq
          exact ⟨q', by simpa [Expr2.reads] using hq', h'.trans h⟩
      | concat parts =>
          simp only [Expr2.size] at he
          simpa [Expr2.reads] using ihl parts.toList (by omega) x (by simpa [Expr2.rdW] using hx)
    · cases l with
      | nil => simp [Expr2.listRdW] at hx
      | cons e es =>
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listRdW, List.mem_append] at hx
          simp only [Expr2.listReads, List.mem_append]
          rcases hx with hx | hx
          · obtain ⟨q, hq, h⟩ := ihe e (by omega) x hx; exact ⟨q, Or.inl hq, h⟩
          · obtain ⟨q, hq, h⟩ := ihl es (by omega) x hx; exact ⟨q, Or.inr hq, h⟩

/-- **Every window an expression may read is of the name of one of its reads.** -/
theorem Expr2.rdW_names (wd : String → Option Nat) (e : Expr2) :
    ∀ x ∈ e.rdW wd, ∃ q ∈ e.reads, q.name = x.1 :=
  (rdW_names_aux wd (e.size + 1)).1 e (Nat.lt_succ_self _)

/-- The guard on a procedural body leaves no continuous flow. -/
theorem combGuardProc_aflow (wd wd' : String → Option Nat) (b : Stmt2) :
    Process2.aflow wd (combGuardProc wd' b) = [] := by
  unfold combGuardProc
  split
  · rfl
  · split <;> rfl

/-! ## The static check on the summary's names -/

/-- The name graph of the continuous (plain) sites: the names a site reads, to the name it drives. -/
def Summary.aliasEdges (s : Summary) : List (List String × String) :=
  s.lsites.filterMap fun ls =>
    if isCombProc ls.site.proc then none else some (ls.site.rds.map Acc.name, ls.site.tgt.name)

/-- The names reached from `W` through at least one edge (`acc` so far; each round adds the targets of the edges
that read a name of `W` or of `acc`). Not trusted: its result is checked by `aliasClosedB`. -/
def aliasFan : Nat → List (List String × String) → List String → List String → List String
  | 0, _, _, acc => acc
  | n + 1, es, W, acc =>
      let new := (es.filter fun e => e.1.any (fun r => W.contains r || acc.contains r) && !acc.contains e.2).map
        Prod.snd
      if new.isEmpty then acc else aliasFan n es W (acc ++ new)

/-- `S` is closed under the edges from `W`: an edge that reads a name of `W` or of `S` drives a name of `S`. -/
def aliasClosedB (es : List (List String × String)) (W S : List String) : Bool :=
  es.all fun e => !(e.1.any fun r => W.contains r || S.contains r) || S.contains e.2

/-- The names reached from the names a procedural site writes. -/
def Summary.aliasReach (s : Summary) (ls : LSite) : List String :=
  aliasFan (s.aliasEdges.length + 1) s.aliasEdges ((ls.site.tgt :: ls.site.more).map Acc.name) []

/-- One procedural site passes: the reached names are closed, and the site reads none of them. -/
def Summary.aliasSiteOk (s : Summary) (ls : LSite) : Bool :=
  aliasClosedB s.aliasEdges ((ls.site.tgt :: ls.site.more).map Acc.name) (s.aliasReach ls) &&
    ls.site.rds.all fun r => !(s.aliasReach ls).contains r.name

/-- **The static check**: every procedural site passes. -/
def Summary.aliasOk (s : Summary) : Bool :=
  s.lsites.all fun ls => !isCombProc ls.site.proc || s.aliasSiteOk ls

/-- The first procedural site that fails the check, and the name it reads that is downstream of one it writes (for
the tactic's message; not trusted). -/
def Summary.aliasFailure (s : Summary) : Option (String × String) :=
  s.lsites.findSome? fun ls =>
    if isCombProc ls.site.proc && !s.aliasSiteOk ls then
      some (ls.site.tgt.name,
        ((ls.site.rds.find? fun r => (s.aliasReach ls).contains r.name).map Acc.name).getD "?")
    else none

theorem aliasClosedB_spec {es : List (List String × String)} {W S : List String} (h : aliasClosedB es W S = true)
    {e : List String × String} (he : e ∈ es) {r : String} (hr : r ∈ e.1) (hrs : r ∈ W ∨ r ∈ S) : e.2 ∈ S := by
  unfold aliasClosedB at h
  have h2 := List.all_eq_true.mp h e he
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exfalso
    have hany : (e.1.any fun r => W.contains r || S.contains r) = true :=
      List.any_eq_true.mpr ⟨r, hr, by rcases hrs with h | h <;> simp [h]⟩
    rw [hany] at h2
    cases h2
  · simpa using h2

/-! ## The guard admits the design -/

section admits
variable {s : Summary} {args : List Int} {σ : String → Int} {envD : IEnv} {elems : List (String × Nat)}
  {M : Design2}

/-- **Every continuous flow of the instantiated design is a plain site's**: it reads names of the site's reads and
writes the site's target name. -/
theorem flows_of_pairs (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site)
    (hMp : M.processes.toList = (s.pairs σ envD elems).map Prod.snd) (wd : String → Option Nat) :
    ∀ x ∈ aliasFlows wd M.processes.toList, ∃ e ∈ s.aliasEdges,
      (∀ r ∈ x.1, r.1 ∈ e.1) ∧ ∀ w ∈ x.2, w.1 = e.2 := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
  rw [hMp] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨ls, hls, σ', E', rfl, hc⟩ := pairs_ctx C hok hauto hin q hq
  obtain ⟨pos, p0, hp0⟩ := hsites ls hls
  rcases siteOfP?_cases hp0 with hp0 | ⟨b, tg, ptr, rfl, -, hst⟩ | ⟨b, segs, rfl, -, hms⟩
  · -- a plain site: its process is the assign of its target
    obtain ⟨e, hpe, hrd, -, -, -⟩ := id (pairs_desc_site hc hp0)
    have hcp : isCombProc ls.site.proc = false := by
      cases hcase : ls.site.proc with
      | alwaysComb b0 =>
          rw [hcase] at hpe
          simp only [instProcess2] at hpe
          unfold combGuardProc at hpe
          split at hpe
          · cases hpe
          · split at hpe <;> cases hpe
      | _ => rfl
    refine ⟨(ls.site.rds.map Acc.name, ls.site.tgt.name), ?_, ?_, ?_⟩
    · unfold Summary.aliasEdges
      exact List.mem_filterMap.mpr ⟨ls, hls, by simp [hcp]⟩
    · rw [hpe] at hxp
      simp only [Process2.aflow, List.mem_singleton] at hxp
      subst hxp
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨q', hq', hn⟩ := Expr2.rdW_names wd e r hr
        have := hrd q' hq'
        simp only [LSite.inst, List.mem_map] at this
        obtain ⟨a, ha, rfl⟩ := this
        rw [← hn, Acc.rd_name]
        exact List.mem_map_of_mem ha
      · simp [LSite.inst, Acc.lhs_rdW] at hr
    · rw [hpe] at hxp
      simp only [Process2.aflow, List.mem_singleton] at hxp
      subst hxp
      intro w hw
      obtain ⟨W, hW, hWn⟩ := Acc.lhs_mayW σ' wd ls.site.tgt
      simp only [LSite.inst] at hw
      rw [hW, List.mem_singleton] at hw
      subst hw
      exact hWn
  · -- a procedural site has no continuous flow
    have hproc : ls.site.proc = .alwaysComb b := congrArg TSite.proc hst
    rw [hproc] at hxp
    simp [instProcess2, combGuardProc_aflow] at hxp
  · obtain ⟨hproc, -, -, -⟩ := multiSite_shape hms
    rw [hproc] at hxp
    simp [instProcess2, combGuardProc_aflow] at hxp

/-- The check gives, for a procedural site, the closed set of the flows and its disjointness from the reads. -/
theorem aliasSite_facts (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site)
    (hMp : M.processes.toList = (s.pairs σ envD elems).map Prod.snd)
    {ls : LSite} (hls : ls ∈ s.lsites) (hcp : isCombProc ls.site.proc = true) (halias : s.aliasOk = true) :
    AliasNamesClosed (aliasFlows M.combWd M.processes.toList)
        (fun n => n ∈ (ls.site.tgt :: ls.site.more).map Acc.name) (fun n => n ∈ s.aliasReach ls) ∧
      ∀ r ∈ ls.site.rds, r.name ∉ s.aliasReach ls := by
  have hok' : s.aliasSiteOk ls = true := by
    have := List.all_eq_true.mp halias ls hls
    simpa [hcp] using this
  unfold Summary.aliasSiteOk at hok'
  rw [Bool.and_eq_true] at hok'
  obtain ⟨hcl, hrd⟩ := hok'
  refine ⟨?_, ?_⟩
  · intro x hx ⟨r, hr, hrn⟩ w hw
    obtain ⟨e, he, hre, hwe⟩ := flows_of_pairs C hok hauto hin hsites hMp M.combWd x hx
    rw [hwe w hw]
    exact aliasClosedB_spec hcl he (hre r hr) hrn
  · intro r hr hrs
    have := List.all_eq_true.mp hrd r hr
    simp [hrs] at this

/-- **Every `always_comb` body of the instantiated design passes the alias walk.** -/
theorem aliasAdmits_pairs (hdecl : M.decls.toList = s.decls.map (DeclT.toDecl σ))
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hwithin : s.DisjWithin σ) (hself : s.NoSelfRead σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site)
    (hMp : M.processes.toList = (s.pairs σ envD elems).map Prod.snd) (halias : s.aliasOk = true) :
    ∀ b, .alwaysComb b ∈ M.processes.toList →
      b.aliasViol M.combWd (aliasFlows M.combWd M.processes.toList) [] = none := by
  intro body hb
  have hb' := hb
  rw [hMp] at hb'
  obtain ⟨q, hq, hqb0⟩ := List.mem_map.mp hb'
  obtain ⟨ls, hls, σ', E', rfl, hc⟩ := pairs_ctx C hok hauto hin q hq
  have hqb : instProcess2 E' elems ls.site.proc = .alwaysComb body := hqb0
  obtain ⟨pos, p0, hp0⟩ := hsites ls hls
  have hok0 := hok
  obtain ⟨-, hnames, -, -, -, hdecl', hacc, -⟩ := hok0
  have hauto0 := hauto
  obtain ⟨-, hauto2, -⟩ := hauto0
  have hdw : ∀ n, (s.DW σ n).isSome = true → s.DW σ n = some (s.dw σ n) := fun n h => dw_some n h
  rcases siteOfP?_cases hp0 with hp0 | ⟨b, tg, ptr, rfl, htree, hst⟩ | ⟨b, segs, rfl, hbs, hms⟩
  · -- a plain site is an assign, not an `always_comb`
    obtain ⟨e, hpe, -⟩ := id (pairs_desc_site hc hp0)
    rw [hpe] at hqb
    cases hqb
  · -- one tree over one window
    have hproc : ls.site.proc = .alwaysComb b := congrArg TSite.proc hst
    have htg : ls.site.tgt = tg := congrArg TSite.tgt hst
    have hrds : ls.site.rds = ptr.rds := congrArg TSite.rds hst
    have hmore : ls.site.more = [] := congrArg TSite.more hst
    have hcp : isCombProc ls.site.proc = true := by rw [hproc]; rfl
    obtain ⟨hcl, hS⟩ := aliasSite_facts C hok hauto hin hsites hMp hls hcp halias
    obtain ⟨hb0, hpok⟩ := treeStmt?_spec s.decls b tg ptr htree
    have hproc2 : instProcess2 E' elems ls.site.proc = instProcess2 E' elems ptr.pt.toProc := by
      rw [hproc, PT.toProc, hb0]
    have hatg := hc.so ls.site.tgt (List.mem_cons_self ..)
    have haccP : ∀ a ∈ ptr.rds,
        AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a :=
      fun a ha => hc.so a (TSite.mem_accs (List.mem_cons_of_mem _ (by rw [hrds]; exact ha)))
    have hg : AccGeom σ' (s.DG σ) (s.EW σ) ls.site.tgt :=
      accGeom_of hc.par hdecl' (hacc ls hls _ (List.mem_cons_self ..)) hc.inw.1
        (hauto2 ls hls _ (List.mem_cons_self ..))
    have hdn : (s.find ls.site.tgt.name).isSome = true :=
      find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
    obtain ⟨-, hle⟩ := acc_win_facts (σd := σ) hdn hg
      (fun n x h => by have := hc.inw.2; rw [h] at this; exact this)
    have hself1 := (Loops.all_iff _ _ _).mp (hself.all ls hls hcp) σ' hc.reach
    have hself' : ∀ a ∈ ptr.rds, (a.rd σ').overlaps (ls.site.tgt.win σ' (s.dw σ)) = false :=
      fun a ha => hself1 a (by rw [hrds]; exact ha) ls.site.tgt (List.mem_cons_self ..)
    have hpok' : ptr.Ok s.decls ls.site.tgt := by rw [htg]; exact hpok
    have hP := proc_site_eq hc.ctx (dw := s.dw σ) hdw (declWidth_eq hdecl) hatg hle
      ptr hpok' haccP hself'
    rw [hproc2, hP] at hqb
    simp only [Process2.alwaysComb.injEq] at hqb
    subst hqb
    have hlhs := Acc.lhs_mayW σ' M.combWd ls.site.tgt
    obtain ⟨W, hW, hWn⟩ := hlhs
    refine Stmt2.aliasViol_names hcl _ [] (by simp) ?_ ?_
    · intro x hx
      rw [mayW_tree M.combWd _ W hW _ x hx, hWn]
      exact List.mem_map_of_mem (List.mem_cons_self ..)
    · refine tree_rdAll M.combWd (fun V => V.1 ∈ s.aliasReach ls) _ (Acc.lhs_rdW σ' M.combWd _) _ ?_
      intro V hV
      refine noRdW_of_noRead M.combWd V _ (low_idxFree hc.ctx hdw ptr hpok' haccP _)
        (low_noRead hc.ctx V ptr hpok' haccP ?_ _)
      intro a ha
      apply ReadWin.overlaps_of_name_ne
      rw [Acc.rd_name]
      intro hn
      exact hS a (by rw [hrds]; exact ha) (hn ▸ hV)
  · -- a body of several windows
    obtain ⟨hproc, hrds, haccs, -⟩ := multiSite_shape hms
    have hcp : isCombProc ls.site.proc = true := by rw [hproc]; rfl
    obtain ⟨hcl, hS⟩ := aliasSite_facts C hok hauto hin hsites hMp hls hcp halias
    obtain ⟨ss, hbss, hbody, hsok, -⟩ := multiSegs?_spec s.decls b segs hbs
    have hmemA : ∀ t ∈ segs, t.1 ∈ ls.site.tgt :: ls.site.more := fun t ht => by
      rw [haccs]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
    have hmemR : ∀ t ∈ segs, ∀ a ∈ t.2.rds, a ∈ ls.site.rds := fun t ht a ha => by
      rw [hrds]; exact List.mem_flatMap.mpr ⟨t, ht, ha⟩
    have hfacts := hc.win_facts hls hok hauto
    have hso' : ∀ a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds),
        AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a := hc.so
    have hatg : ∀ t ∈ segs, AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) t.1 :=
      fun t ht => hso' _ (by
        rcases List.mem_cons.mp (hmemA t ht) with h | h
        · rw [h]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h))
    have haccP : ∀ t ∈ segs, ∀ a ∈ t.2.rds,
        AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a :=
      fun t ht a ha => hso' a (List.mem_cons_of_mem _ (List.mem_append_right _ (hmemR t ht a ha)))
    have hinw : ∀ t ∈ segs, (t.1.win σ' (s.dw σ)).2.1 + (t.1.win σ' (s.dw σ)).2.2 ≤ s.dw σ t.1.name :=
      fun t ht => (hfacts t.1 (hmemA t ht)).2.2.2
    have hpos : ∀ t ∈ segs, 0 < (t.1.win σ' (s.dw σ)).2.2 := fun t ht => (hfacts t.1 (hmemA t ht)).2.2.1
    have hself1 := (Loops.all_iff _ _ _).mp (hself.all ls hls hcp) σ' hc.reach
    have hself' : ∀ t ∈ segs, ∀ a ∈ t.2.rds, ∀ t' ∈ segs,
        (a.rd σ').overlaps (t'.1.win σ' (s.dw σ)) = false :=
      fun t ht a ha t' ht' => hself1 a (hmemR t ht a ha) t'.1 (hmemA t' ht')
    have hdisj : Win.allDisjoint (segs.map fun t => t.1.win σ' (s.dw σ)) = true := by
      rw [Win.allDisjoint_iff]
      have := (Loops.all_iff _ _ _).mp (hwithin ls hls) σ' hc.reach
      rw [haccs, List.pairwise_map] at this
      rw [List.pairwise_map]
      exact this
    have hP := proc_body_eq hc.ctx (dw := s.dw σ) hdw (declWidth_eq hdecl) segs hatg hinw hsok haccP
      hself' hpos hdisj
    have hproc2 : instProcess2 E' elems ls.site.proc = instProcess2 E' elems (.alwaysComb (bodyP2 segs)) := by
      rw [hproc, hbody, hbss]
    rw [hproc2, hP] at hqb
    simp only [Process2.alwaysComb.injEq] at hqb
    subst hqb
    refine Stmt2.aliasViol_names hcl _ [] (by simp) ?_ ?_
    · simp only [bodyStmt, Stmt2.mayW]
      refine bodyStmts_mayW_names M.combWd (fun n => n ∈ (ls.site.tgt :: ls.site.more).map Acc.name) _ ?_
      intro sg hsg
      simp only [segsOf, List.mem_map] at hsg
      obtain ⟨t, ht, rfl⟩ := hsg
      obtain ⟨W, hW, hWn⟩ := Acc.lhs_mayW σ' M.combWd t.1
      refine ⟨W, hW, ?_⟩
      rw [hWn]
      exact List.mem_map_of_mem (hmemA t ht)
    · simp only [bodyStmt, Stmt2.allRdW]
      refine bodyStmts_rdAll M.combWd (fun V => V.1 ∈ s.aliasReach ls) _ ?_
      intro sg hsg
      simp only [segsOf, List.mem_map] at hsg
      obtain ⟨t, ht, rfl⟩ := hsg
      refine ⟨Acc.lhs_rdW σ' M.combWd _, fun V hV => ?_⟩
      refine noRdW_of_noRead M.combWd V _ (low_idxFree hc.ctx hdw t.2 (hsok t ht) (haccP t ht) _)
        (low_noRead hc.ctx V t.2 (hsok t ht) (haccP t ht) ?_ _)
      intro a ha
      apply ReadWin.overlaps_of_name_ne
      rw [Acc.rd_name]
      intro hn
      exact hS a (hmemR t ht a ha) (hn ▸ hV)

end admits

/-- **The alias guard keeps every process** of a design the proc-aware summary reads, at a parameter point where
the summary's obligations hold and the names pass `Summary.aliasOk`. -/
theorem Summary.aliasGuard_eq {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) (hself : s.NoSelfRead σ)
    (halias : s.aliasOk = true) :
    d.instantiateGDAlias2 args = d.instantiateGD2 args := by
  obtain ⟨m, d', -, -, hm, hl, hdm, hdd, hrel, hR, -⟩ :=
    Summary.soundL hs harity h1 hag hok hauto hin hdisj.within_all hself
  obtain ⟨hc, hpos⟩ := realizedL_comb hR hok hauto hin hdisj
  have hGD : d.instantiateGD2 args = m := PDesign.instantiateGD2_of_lowered hm hdd hc hpos hrel
  obtain ⟨-, -, hoth, -, hsd, hsts, hgen, hspec⟩ := summaryP_spec hs
  obtain ⟨hproc, hsites0⟩ := sitesOfP?_spec hsts
  have hsites := lsitesP_spec hsites0 hspec
  obtain ⟨C, M, hMi, hMd, hMp⟩ :=
    sound_prefix harity h1 hag hok hauto hoth hsd hproc hgen (fun f hf => (hspec f hf).1)
  have hmM : m = M := by
    rw [hm] at hMi
    injection hMi
  subst hmM
  unfold PDesign.instantiateGDAlias2
  rw [hGD]
  exact Design2.aliasGuard_of_admits
    (aliasAdmits_pairs hMd C hok hauto hin hdisj.within_all hself hsites hMp halias)

/-! ## The forms the tactic uses: `comb_viewL` and friends at the guarded family -/

theorem comb_viewLA {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (hself : s.NoSelfRead (s.val args)) (halias : s.aliasOk = true) :
    ∃ d', (d.instantiateGDAlias2 args).lowerComb = some d' ∧ CombDesign d' := by
  rw [Summary.aliasGuard_eq hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hself halias]
  exact comb_viewL hs harity h1 hag hok hauto hin hdisj hself

theorem struct_viewLA {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (hself : s.NoSelfRead (s.val args)) (halias : s.aliasOk = true)
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    ∃ d', (d.instantiateGDAlias2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  rw [Summary.aliasGuard_eq hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hself halias]
  exact struct_viewL hs harity h1 hag hok hauto hin hdisj hself ρ hrank

theorem struct_lex_viewLA {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (hself : s.NoSelfRead (s.val args)) (halias : s.aliasOk = true)
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    ∃ d', (d.instantiateGDAlias2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  rw [Summary.aliasGuard_eq hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hself halias]
  exact struct_lex_viewL hs harity h1 hag hok hauto hin hdisj hself κ hrank

/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombView.Summary.aliasGuard_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Summary.aliasGuard_eq

/-- info: 'LeanModels.Sv.CombView.comb_viewLA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comb_viewLA

/-- info: 'LeanModels.Sv.CombView.struct_viewLA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_viewLA

/-- info: 'LeanModels.Sv.CombView.struct_lex_viewLA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_lex_viewLA

end CombView
end LeanModels.Sv
