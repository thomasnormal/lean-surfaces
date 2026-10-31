import LeanModels.Sv.CombProcStmt
import LeanModels.Sv.CombEqShape

/-!
# `always_comb` bodies in the `sv_comb` fragment, stage 2: the template side (WP-G, G2.1)

`CombProcStmt.lean` proves what the lowering `Design2.lowerComb` does to a body of the shape `PTree`, with the
expressions as hypotheses. This file connects it to the SUMMARY of `sv_structure`/`sv_equations`
(`CombView.lean`, `CombEqShape.lean`): a template body (`PStmt`) of the first fragment is recognized
(`treeStmt?`), its instantiation `instProcess2` is shown to be the `PTree` statement under the self-read
guard (`instProcess2_tree`), and every hypothesis of the lowering is derived from the facts the summary
already provides about reads and targets (`Ctx`, `AccOK`, `RdOK`, `leaf_eq`, `instLhs_acc_w`):

| lowering hypothesis | source | theorem |
|---|---|---|
| `tgt.symWin d = some W`, `mayW`, `rdW` of the lowered target; the width of the target window | the access `tg` is in range (`AccOK`, `hin`), `d` declares the summary's widths | `tgt_facts`, `CombEq.instLhs_acc_w` |
| every expression `wfB` (no loud node, only declared names) | `RdOK` of the fitted right-hand sides and of the conditions (`rhs_ok`, `inst_rd`) | `low_wf` |
| no `index` node (so the bit-level read windows of the guard are the summary's) | `leaf_eq`: a leaf instantiates to `accExpr` | `low_idxFree` |
| no read window overlaps the written window | the obligation `∀ a ∈ reads, (a.rd σ).overlaps (tg.win σ dw) = false` (the summary's `noSelfRead_k`, closed by `omega`) | `low_noRead` |
| **the process lowers to `assign {W} = {low}`** | all of the above | `lower_site` |

Nothing here needs the operand WIDTHS (the leaves are fitted to the target); the equations (`sv_equations`) add
`Sk.WidthOk` in the next stage. The recognizer `treeStmt?` returns, for every refused body, the message the
tactic prints (`site `g_bit#1`: …`); `treeStmt?_spec` is its inversion. No axiom is added.
-/

namespace LeanModels.Sv
namespace CombProc
open CombView CombEq

/-! ## The template tree and its instantiation -/

/-- The template of an S1 body: a tree of `if/else` over right-hand sides, every leaf assigning one target
(`leafL`: `t = v;` with a select target; `leafW`: `n = v;`, the whole-signal statement form). `blk` is a
`begin t end` around one tree. -/
inductive PT where
  | leafL (t : PLhs) (v : PExpr)
  | leafW (n : String) (v : PExpr)
  | ite (c : PExpr) (a b : PT)
  | blk (a : PT)

/-- The statement a template tree stands for. -/
def PT.toPStmt : PT → PStmt
  | .leafL t v => .blockingAssignL t v
  | .leafW n v => .blockingAssign n v
  | .ite c a b => .ifStmt c a.toPStmt (some b.toPStmt)
  | .blk a => .block [a.toPStmt]

/-- The template process: `always_comb <tree>` (the top node is a `blk` for `begin ... end`). -/
def PT.toProc (pt : PT) : PProcess := .alwaysComb pt.toPStmt

/-- Its instantiation as a `PTree`: leaves fitted to the target width `w`, conditions self-determined. -/
def PT.low (E : IEnv) (elems : List (String × Nat)) (w : Nat) : PT → PTree
  | .leafL _ v => .leaf (fitExpr2 E elems (some w) v)
  | .leafW _ v => .leaf (fitExpr2 E elems (some w) v)
  | .ite c a b => .ite (instExpr2 E elems none c) (a.low E elems w) (b.low E elems w)
  | .blk a => .blk (a.low E elems w)

/-- Every leaf target instantiates to the target `tgt` of width `w`. -/
def PT.Tgt (E : IEnv) (elems : List (String × Nat)) (tgt : Lhs2) (w : Nat) : PT → Prop
  | .leafL t _ => instLhs2 E elems t = .ok (tgt, w)
  | .leafW n _ => instLhs2 E elems (.ident n) = .ok (tgt, w)
  | .ite _ a b => a.Tgt E elems tgt w ∧ b.Tgt E elems tgt w
  | .blk a => a.Tgt E elems tgt w

theorem instStmt2_tree {E : IEnv} {elems : List (String × Nat)} {tgt : Lhs2} {w : Nat} :
    ∀ pt : PT, pt.Tgt E elems tgt w →
      instStmt2 E elems pt.toPStmt = (pt.low E elems w).toStmt tgt := by
  intro pt
  induction pt with
  | leafL t v =>
      intro h
      simp only [PT.Tgt] at h
      simp [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, h]
  | leafW n v =>
      intro h
      simp only [PT.Tgt, instLhs2, instLhsLeaf2] at h
      split at h
      · rename_i w' hw'
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, hw']
      · simp at h
  | ite c a b iha ihb =>
      intro ⟨h1, h2⟩
      simp [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, iha h1, ihb h2]
  | blk a iha =>
      intro h
      simp [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, instStmts2, iha h]

/-- **The instantiation of a template tree IS the `PTree` statement, under the self-read guard.** -/
theorem instProcess2_tree {E : IEnv} {elems : List (String × Nat)} {tgt : Lhs2} {w : Nat}
    (pt : PT) (h : pt.Tgt E elems tgt w) :
    instProcess2 E elems pt.toProc =
      combGuardProc (fun n => E.widths.lookup n) ((pt.low E elems w).toStmt tgt) := by
  simp [PT.toProc, instProcess2, instStmt2_tree pt h]

/-! ## The annotated tree: each expression with the reads the recognizer found -/

/-- A template tree with, at every node, the read accesses `rdsOf?`/`rhsRds?` computed for it. -/
inductive PTR where
  | leafL (t : PLhs) (v : PExpr) (rs : List Acc)
  | leafW (n : String) (v : PExpr) (rs : List Acc)
  | ite (c : PExpr) (rc : List Acc) (a b : PTR)
  | blk (a : PTR)

/-- The template tree underneath. -/
def PTR.pt : PTR → PT
  | .leafL t v _ => .leafL t v
  | .leafW n v _ => .leafW n v
  | .ite c _ a b => .ite c a.pt b.pt
  | .blk a => .blk a.pt

/-- All the read accesses of the tree, condition first (the site's read list). -/
def PTR.rds : PTR → List Acc
  | .leafL _ _ rs => rs
  | .leafW _ _ rs => rs
  | .ite _ rc a b => rc ++ a.rds ++ b.rds
  | .blk a => a.rds

/-- The recognizer's verdict on every node, for the target access `tg`: each leaf target is `tg`
(`tgtOf?`), right-hand sides are in the fragment of `sv_equations` (`rhsRds?`, `fragOk`), conditions are
gate trees (`rdsOf?`, `fragG`). -/
def PTR.Ok (ds : List DeclT) (tg : Acc) : PTR → Prop
  | .leafL t v rs => tgtOf? ds t = .ok tg ∧ rhsRds? ds v = .ok rs ∧ fragOk v = true
  | .leafW n v rs => tgtOf? ds (.ident n) = .ok tg ∧ rhsRds? ds v = .ok rs ∧ fragOk v = true
  | .ite c rc a b => (rdsOf? ds c = .ok rc ∧ fragG c = true) ∧ a.Ok ds tg ∧ b.Ok ds tg
  | .blk a => a.Ok ds tg

/-! ## Reads, names and index nodes of the instantiated tree (no widths needed) -/

section site
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- A leaf access instantiates to a slice or an identifier: no `index` node. -/
theorem inst_leaf_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) (ctx : Option Nat) :
    (instExpr2 E elems ctx e).idxFree = true := by
  rw [(leaf_eq C hdw h ha).2.1 ctx]
  cases a <;> simp [accExpr, Expr2.idxFree]

theorem inst_rdsLeaf_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr}
    {rs : List Acc} (h : rdsLeaf? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a)
    (ctx : Option Nat) : (instExpr2 E elems ctx e).idxFree = true := by
  obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases h
  exact inst_leaf_idxFree C hdw hl (hacc a (by simp)) ctx

theorem inst_parts_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRd? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      Expr2.listIdxFree (instParts2 E elems ps) = true
  | [], rs, h, _ => by simp [Expr2.listIdxFree]
  | p :: ps, rs, h, hacc => by
      simp only [partsRd?] at h
      rcases hp : partRd? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRd? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          have h1 : (instExpr2 E elems (selfWidth2 E elems p) p).idxFree = true := by
            unfold partRd? at hp
            cases p with
            | lit v => simp [Expr2.idxFree]
            | _ =>
                obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
                exact inst_leaf_idxFree C hdw hl (hacc a (List.mem_append_left _ (by simp))) _
          have h2 := inst_parts_idxFree C hdw ps rb hq (fun a ha => hacc a (List.mem_append_right _ ha))
          rw [instParts2_cons]
          simp [Expr2.listIdxFree, h1, h2]

/-- A fit of an `index`-free instantiation has no `index` node. -/
theorem fit_idxFree {e : PExpr} (hs : e.signedCast = false)
    (h : ∀ c, (instExpr2 E elems c e).idxFree = true) (ctx : Option Nat) :
    (fitExpr2 E elems ctx e).idxFree = true := by
  rcases fitExpr2_cases E elems ctx e hs with ⟨c', hc⟩ | ⟨w, c', hc⟩
  · rw [hc]; exact h c'
  · rw [hc]; simpa [Expr2.idxFree] using h c'

/-- An expression of the fragment instantiates to an expression with no `index` node, at any context. -/
theorem inst_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (e : PExpr) (rs : List Acc), rdsOf? ds e = .ok rs → (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      ∀ ctx, (instExpr2 E elems ctx e).idxFree = true
  | .lit v, rs, h, _, ctx => by simp [Expr2.idxFree]
  | .binary op l r, rs, h, hacc, ctx => by
      obtain ⟨hb, ra, rb, hl, hr', rfl⟩ := rdsOf?_binary h
      have ihl := inst_idxFree C hdw l ra hl (fun a ha => hacc a (List.mem_append_left _ ha))
      have ihr := inst_idxFree C hdw r rb hr' (fun a ha => hacc a (List.mem_append_right _ ha))
      have hfl := fit_idxFree (E := E) (elems := elems) (signedCast_of_rds hl) ihl
      have hfr := fit_idxFree (E := E) (elems := elems) (signedCast_of_rds hr') ihr
      have gate : ∀ g : BinOp, (g = .and ∨ g = .or ∨ g = .xor) →
          (instExpr2 E elems ctx (.binary (.m0 g) l r)).idxFree = true := by
        intro g hg
        obtain ⟨c, hc⟩ := instExpr2_gate E elems ctx g hg l r
        rw [hc]
        simp [Expr2.idxFree, hfl c, hfr c]
      rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact gate .and (Or.inl rfl)
      · exact gate .or (Or.inr (Or.inl rfl))
      · exact gate .xor (Or.inr (Or.inr rfl))
      · rw [ie_land]; simp [Expr2.idxFree, ihl, ihr]
      · rw [ie_lor]; simp [Expr2.idxFree, ihl, ihr]
      · obtain ⟨c, hc⟩ := ie_eq_cases (env := E) (elems := elems) ctx l r
        rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
      · obtain ⟨c, hc⟩ := ie_ne_cases (env := E) (elems := elems) ctx l r
        rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
  | .unary op a, rs, h, hacc, ctx => by
      obtain ⟨hop, ha⟩ := rdsOf?_unary h
      have iha := inst_idxFree C hdw a rs ha hacc
      have hfa := fit_idxFree (E := E) (elems := elems) (signedCast_of_rds ha) iha
      rcases hop with rfl | rfl
      · rcases ie_bnot_cases (env := E) (elems := elems) ctx a with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨w, c, hc⟩
        · rw [hc]; simpa [Expr2.idxFree] using iha c
        · rw [hc]; simpa [Expr2.idxFree] using hfa c
        · rw [hc]; simpa [Expr2.idxFree] using hfa c
      · rw [ie_lnot]; simpa [Expr2.idxFree] using iha none
  | .ternary c t f, rs, h, hacc, ctx => by
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := rdsOf?_ternary h
      have ihc := inst_idxFree C hdw c rc hc
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_left _ ha)))
      have iht := inst_idxFree C hdw t rt ht
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_right _ ha)))
      have ihf := inst_idxFree C hdw f rf hfe (fun a ha => hacc a (List.mem_append_right _ ha))
      obtain ⟨a0, ha0⟩ := ie_ternary_cases (env := E) (elems := elems) ctx c t f
      rw [ha0]
      simp [Expr2.idxFree, ihc none, fit_idxFree (signedCast_of_rds ht) iht a0,
        fit_idxFree (signedCast_of_rds hfe) ihf a0]
  | .reduce op a, rs, h, hacc, ctx => by
      have iha := inst_idxFree C hdw a rs (rdsOf?_reduce h) hacc
      rw [ie_reduce]; simpa [Expr2.idxFree] using iha _
  | .concat ps, rs, h, hacc, ctx => by
      simp only [rdsOf?] at h
      rw [instExpr2_concat]
      simpa [Expr2.idxFree] using inst_parts_idxFree C hdw ps rs h hacc
  | .ident n, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .bitSel b i, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .arrayElem n is, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .arrayPart n is m a b, rs, h, hacc, ctx =>
      inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .partSel .., rs, h, _, _ | .repl .., rs, h, _, _
  | .paramRef .., rs, h, _, _
  | .genvarRef .., rs, h, _, _ | .enumRef .., rs, h, _, _
  | .int .., rs, h, _, _ | .fill .., rs, h, _, _
  | .resize .., rs, h, _, _ | .signedResize .., rs, h, _, _
  | .squash2 .., rs, h, _, _ | .sysCall .., rs, h, _, _
  | .cast .., rs, h, _, _ | .unsupported .., rs, h, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-- A whole right-hand side, fitted to the target width: no `index` node. -/
theorem rhs_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (h : rhsRds? ds v = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (w : Nat) :
    (fitExpr2 E elems (some w) v).idxFree = true := by
  by_cases hf : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hf
    rw [fitExpr2_of_not_rigid w rfl]
    simp [instExpr2, Expr2.idxFree]
  · have hr : rhsRds? ds v = rdsOf? ds v := by
      cases v <;> first | rfl | (exfalso; exact hf ⟨_, rfl⟩)
    rw [hr] at h
    rcases fitExpr2_cases E elems (some w) v (signedCast_of_rds h) with ⟨c, hc⟩ | ⟨w', c, hc⟩
    · rw [hc]; exact inst_idxFree C hdw v rs h hacc c
    · rw [hc]; simpa [Expr2.idxFree] using inst_idxFree C hdw v rs h hacc c

/-! ## The three facts the lowering reads about the instantiated tree -/

/-- No `index` node anywhere in the tree. -/
theorem low_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) → ∀ tw,
      (ptr.pt.low E elems tw).idxFree
  | .leafL t v rs, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.idxFree] using rhs_idxFree C hdw (ds := ds) hok.2.1 hacc tw
  | .leafW n v rs, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.idxFree] using rhs_idxFree C hdw (ds := ds) hok.2.1 hacc tw
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw => by
      refine ⟨?_, low_idxFree C hdw a ha (fun x hx => hacc x (by simp [PTR.rds, hx])) tw,
        low_idxFree C hdw b hb (fun x hx => hacc x (by simp [PTR.rds, hx])) tw⟩
      exact inst_idxFree C hdw c rc hc (fun x hx => hacc x (by simp [PTR.rds, hx])) none
  | .blk a, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.idxFree] using low_idxFree C hdw a hok hacc tw

/-- Every expression of the tree is well formed for the design `d` whose widths are the summary's
(`hd`): no loud node, only declared names. -/
theorem low_wf (C : Ctx σ E elems DW DG EW ns) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) → ∀ tw,
      (ptr.pt.low E elems tw).wf d
  | .leafL t v rs, hok, hacc, tw => by
      have hr := rhs_ok C hok.2.1 hacc tw
      refine (wfB_iff d _).2 ⟨hr.1, fun i hi => ?_⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.2 i hi)
      have := (hacc a (by simpa [PTR.rds] using ha)).1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      exact Design2.mem_names_of_declWidth (w := w) (by rw [hd]; exact hw)
  | .leafW n v rs, hok, hacc, tw => by
      have hr := rhs_ok C hok.2.1 hacc tw
      refine (wfB_iff d _).2 ⟨hr.1, fun i hi => ?_⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.2 i hi)
      have := (hacc a (by simpa [PTR.rds] using ha)).1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      exact Design2.mem_names_of_declWidth (w := w) (by rw [hd]; exact hw)
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw => by
      refine ⟨?_, low_wf C hd a ha (fun x hx => hacc x (by simp [PTR.rds, hx])) tw,
        low_wf C hd b hb (fun x hx => hacc x (by simp [PTR.rds, hx])) tw⟩
      have hr := inst_rd C c rc hc (fun x hx => hacc x (by simp [PTR.rds, hx])) none
      refine (wfB_iff d _).2 ⟨hr.1, fun i hi => ?_⟩
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp (hr.2.2 i hi)
      have := (hacc a' (by simp [PTR.rds, ha'])).1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      exact Design2.mem_names_of_declWidth (w := w) (by rw [hd]; exact hw)
  | .blk a, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.wf] using low_wf C hd a hok hacc tw

/-- No read of the tree overlaps the window `W`, given that no read ACCESS does (the summary's
`noSelfRead` obligation). -/
theorem low_noRead (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {tg : Acc} (W : Win) :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) →
      (∀ a ∈ ptr.rds, (a.rd σ).overlaps W = false) → ∀ tw, (ptr.pt.low E elems tw).noRead W
  | .leafL t v rs, hok, hacc, hself, tw => by
      have hr := rhs_ok C hok.2.1 hacc tw
      intro r hr'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.1 r hr')
      exact hself a (by simpa [PTR.rds] using ha)
  | .leafW n v rs, hok, hacc, hself, tw => by
      have hr := rhs_ok C hok.2.1 hacc tw
      intro r hr'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.1 r hr')
      exact hself a (by simpa [PTR.rds] using ha)
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, hself, tw => by
      refine ⟨?_, low_noRead C W a ha (fun x hx => hacc x (by simp [PTR.rds, hx]))
          (fun x hx => hself x (by simp [PTR.rds, hx])) tw,
        low_noRead C W b hb (fun x hx => hacc x (by simp [PTR.rds, hx]))
          (fun x hx => hself x (by simp [PTR.rds, hx])) tw⟩
      have hr := inst_rd C c rc hc (fun x hx => hacc x (by simp [PTR.rds, hx])) none
      intro r hr'
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp (hr.2.1 r hr')
      exact hself a' (by simp [PTR.rds, ha'])
  | .blk a, hok, hacc, hself, tw => by
      simpa [PTR.pt, PT.low, PTree.noRead] using low_noRead C W a hok hacc hself tw

/-! ## The target -/

/-- Every non-`whole` access lowers to the slice of its window. -/
theorem lhs_eq_win_lhs (σ : String → Int) (dw : String → Nat) :
    ∀ a : Acc, (∀ n, a ≠ .whole n) → a.lhs σ = Win.lhs (a.win σ dw)
  | .whole n, h => absurd rfl (h n)
  | .bit .., _ => rfl
  | .cell1 .., _ => rfl
  | .row .., _ => rfl
  | .cell2 .., _ => rfl
  | .part1 .., _ => rfl
  | .part2 .., _ => rfl

/-- The facts about the lowered target `tg.lhs σ` that the lowering and the self-read guard read:
its symbolic window is the access's window, it may write exactly that window and reads nothing.
(`hin`: the window lies inside the declared signal, the summary's `InRangeObl`.) -/
theorem tgt_facts (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {tg : Acc} (hatg : AccOK σ DW DG EW ns tg)
    (hin : (tg.win σ dw).2.1 + (tg.win σ dw).2.2 ≤ dw tg.name) :
    (tg.lhs σ).symWin d = some (tg.win σ dw) ∧
      (tg.lhs σ).mayW (fun n => E.widths.lookup n) = [tg.win σ dw] ∧
      (tg.lhs σ).rdW (fun n => E.widths.lookup n) = [] := by
  by_cases hwh : ∃ n, tg = .whole n
  · obtain ⟨n, rfl⟩ := hwh
    have hn' : d.declWidth n = some (dw n) := by rw [hd]; exact hdw n hatg.1
    have hw : E.widths.lookup n = some (dw n) := by rw [C.widths n]; exact hdw n hatg.1
    simp [Acc.lhs, Acc.win, Lhs2.symWin, Lhs2.window?, Lhs2.mayW, Lhs2.rdW, CombGuard.whole, hn', hw]
  · have hwh' : ∀ n, tg ≠ .whole n := fun n h => hwh ⟨n, h⟩
    rw [lhs_eq_win_lhs σ dw tg hwh']
    have hname := Acc.win_name σ dw tg
    have hn : d.declWidth (tg.win σ dw).1 = some (dw tg.name) := by
      rw [hname, hd]; exact hdw _ hatg.1
    refine ⟨?_, ?_, ?_⟩
    · simp [Lhs2.symWin, Win.lhs, Lhs2.window?, hn, hin]
    · simp [Win.lhs, Lhs2.mayW]
    · simp [Win.lhs, Lhs2.rdW]

/-- Every leaf target of a recognized tree instantiates to the lowered target, at the width of its window
(`instLhs_acc_w`). -/
theorem tree_tgt (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc}
    (hatg : AccOK σ DW DG EW ns tg) :
    ∀ ptr : PTR, ptr.Ok ds tg → ptr.pt.Tgt E elems (tg.lhs σ) (tg.win σ dw).2.2
  | .leafL _ _ _, hok => instLhs_acc_w C hdw hok.1 hatg
  | .leafW _ _ _, hok => instLhs_acc_w C hdw hok.1 hatg
  | .ite _ _ a b, ⟨_, ha, hb⟩ => ⟨tree_tgt C hdw hatg a ha, tree_tgt C hdw hatg b hb⟩
  | .blk a, hok => tree_tgt C hdw hatg a hok

/-! ## The lowering of an instantiated site -/

/-- **A recognized `always_comb` site lowers to the single equation it promises.**

For a template tree `ptr` whose leaves all assign the access `tg` (recognized and in range: `hok`, `hatg`,
`hin`), every read access in range and declared (`hacc`), reading no window it writes (`hself`, the
summary's `noSelfRead` obligation), `Design2.lowerComb` of the instantiated process is the continuous assign
`{W} = {low}` of the tree's `PTree.low`. No width obligation is needed: the leaves are fitted to the target
width by `instLhs_acc_w`, whatever their own width (the equation theorem adds `WidthOk`). `hd`: the design `d`
declares exactly the summary's widths (`CombView.declWidth_eq`); `hdw`, `hin`: as in `Summary.sound`. -/
theorem lower_site (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} {tg : Acc}
    (hatg : AccOK σ DW DG EW ns tg)
    (hin : (tg.win σ dw).2.1 + (tg.win σ dw).2.2 ≤ dw tg.name)
    (ptr : PTR) (hok : ptr.Ok ds tg) (hacc : ∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a)
    (hself : ∀ a ∈ ptr.rds, (a.rd σ).overlaps (tg.win σ dw) = false) :
    Process2.lowerComb d (instProcess2 E elems ptr.pt.toProc) =
      some (.assign (.concat [(tg.win σ dw).lhs])
        (.concat #[(ptr.pt.low E elems (tg.win σ dw).2.2).low (tg.win σ dw).2.2])) := by
  rw [instProcess2_tree ptr.pt (tree_tgt C hdw hatg ptr hok)]
  obtain ⟨hsw, hm, hr⟩ := tgt_facts C hdw hd hatg hin
  exact lower_tree' d _ (tg.lhs σ) (tg.win σ dw) hsw hm hr _ (low_wf C hd ptr hok hacc _)
    (low_idxFree C hdw ptr hok hacc _) (low_noRead C (tg.win σ dw) ptr hok hacc hself _)

end site

/-! ## The recognizer: which `always_comb` bodies are in the fragment, and why not -/

/-- A select-target leaf `t = v;`. -/
def leafL? (ds : List DeclT) (t : PLhs) (v : PExpr) : Except String (Acc × PTR) :=
  match tgtOf? ds t with
  | .error e => .error e
  | .ok tg =>
      match rhsRds? ds v with
      | .error e => .error e
      | .ok rs =>
          if fragOk v then .ok (tg, .leafL t v rs)
          else .error "right-hand side outside the v1 fragment (a gate tree, a concatenation or a fill)"

/-- A whole-signal leaf `n = v;`. -/
def leafW? (ds : List DeclT) (n : String) (v : PExpr) : Except String (Acc × PTR) :=
  match tgtOf? ds (.ident n) with
  | .error e => .error e
  | .ok tg =>
      match rhsRds? ds v with
      | .error e => .error e
      | .ok rs =>
          if fragOk v then .ok (tg, .leafW n v rs)
          else .error "right-hand side outside the v1 fragment (a gate tree, a concatenation or a fill)"

mutual
/-- **Recognize a statement as a tree of the first fragment** (module docstring of `CombProcStmt.lean`),
returning the access every leaf assigns and the annotated tree. The messages are what the tactic prints. -/
def treeStmt? (ds : List DeclT) : PStmt → Except String (Acc × PTR)
  | .blockingAssignL t v => leafL? ds t v
  | .blockingAssign n v => leafW? ds n v
  | .ifStmt c th (some el) =>
      match rdsOf? ds c with
      | .error e => .error e
      | .ok rc =>
          if fragG c then
            match treeStmt? ds th with
            | .error e => .error e
            | .ok (t1, a) =>
                match treeStmt? ds el with
                | .error e => .error e
                | .ok (t2, b) =>
                    if t1 = t2 then .ok (t1, .ite c rc a b)
                    else .error "always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)"
          else .error "`if` condition outside the v1 fragment (a one-bit expression of accesses and literals built from `& | ^`, `~ !`, reductions, `&& ||`, `== !=` and `?:`)"
  | .ifStmt _ _ none =>
      .error "always_comb does not assign its target on every path (an `if` without `else` is a latch)"
  | .block ss => treeStmts? ds ss
  | .nbaAssign .. | .nbaAssignL .. =>
      .error "nonblocking assignment in always_comb (outside the v1 fragment)"
  | .caseStmt .. => .error "always_comb statement `case` (outside the first fragment)"
  | .unsupported k _ => .error s!"always_comb statement `{k}` (unsupported)"
termination_by structural s => s

/-- A block: exactly one statement (a tree). -/
def treeStmts? (ds : List DeclT) : List PStmt → Except String (Acc × PTR)
  | [] => .error "empty always_comb block"
  | [s] =>
      match treeStmt? ds s with
      | .error e => .error e
      | .ok (t, a) => .ok (t, .blk a)
  | _ :: _ :: _ =>
      .error "always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)"
termination_by structural ss => ss
end

/-- The recognizer on a process: an `always_comb`, nothing else. -/
def procTree? (ds : List DeclT) : PProcess → Except String (Acc × PTR)
  | .alwaysComb b => treeStmt? ds b
  | _ => .error "not an always_comb process"

mutual
/-- **Inversion**: a recognized statement is the statement of the annotated tree, and every node
passed its checks. -/
theorem treeStmt?_spec (ds : List DeclT) : ∀ (s : PStmt) (tg : Acc) (ptr : PTR),
    treeStmt? ds s = .ok (tg, ptr) → ptr.pt.toPStmt = s ∧ ptr.Ok ds tg
  | .blockingAssignL t v, tg, ptr, h => by
      unfold treeStmt? leafL? at h
      split at h
      · simp at h
      · rename_i tg' htg
        split at h
        · simp at h
        · rename_i rs hrs
          split at h
          · rename_i hf
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, htg, hrs, hf⟩
          · simp at h
  | .blockingAssign n v, tg, ptr, h => by
      unfold treeStmt? leafW? at h
      split at h
      · simp at h
      · rename_i tg' htg
        split at h
        · simp at h
        · rename_i rs hrs
          split at h
          · rename_i hf
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, htg, hrs, hf⟩
          · simp at h
  | .ifStmt c th (some el), tg, ptr, h => by
      unfold treeStmt? at h
      split at h
      · simp at h
      · rename_i rc hrc
        split at h
        · rename_i hg
          split at h
          · simp at h
          · rename_i t1 a h1
            split at h
            · simp at h
            · rename_i t2 b h2
              split at h
              · rename_i heq
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨e1, o1⟩ := treeStmt?_spec ds th t1 a h1
                obtain ⟨e2, o2⟩ := treeStmt?_spec ds el t2 b h2
                subst heq
                exact ⟨by simp [PTR.pt, PT.toPStmt, e1, e2], ⟨hrc, hg⟩, o1, o2⟩
              · simp at h
        · simp at h
  | .ifStmt c th none, tg, ptr, h => by simp [treeStmt?] at h
  | .block ss, tg, ptr, h => by
      unfold treeStmt? at h
      exact treeStmts?_spec ds ss tg ptr h
  | .nbaAssign t v, tg, ptr, h => by simp [treeStmt?] at h
  | .nbaAssignL t v, tg, ptr, h => by simp [treeStmt?] at h
  | .caseStmt .., tg, ptr, h => by simp [treeStmt?] at h
  | .unsupported k t, tg, ptr, h => by simp [treeStmt?] at h
termination_by structural s => s

theorem treeStmts?_spec (ds : List DeclT) : ∀ (ss : List PStmt) (tg : Acc) (ptr : PTR),
    treeStmts? ds ss = .ok (tg, ptr) → ptr.pt.toPStmt = .block ss ∧ ptr.Ok ds tg
  | [], tg, ptr, h => by simp [treeStmts?] at h
  | [s], tg, ptr, h => by
      unfold treeStmts? at h
      split at h
      · simp at h
      · rename_i t a h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e1, o1⟩ := treeStmt?_spec ds s t a h1
        exact ⟨by simp [PTR.pt, PT.toPStmt, e1], o1⟩
  | _ :: _ :: _, tg, ptr, h => by simp [treeStmts?] at h
termination_by structural ss => ss
end

/-! ## Non-vacuity: the `add_proc` carry cell

`always_comb begin if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i]; end` in a generate loop, exactly the process the
extractor's envelope of `svgolf/design/always-comb/fixtures/add_proc.sv` ingests (`Examples/system-verilog/comb_proc`
checks the equality against `load_design_sv2`). First the recognizer on hand-built declarations (symbolic `N`),
then the lowering at a symbolic `N` and an arbitrary bit `k < N`. -/

/-- `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];` as a template. -/
def carryLhs : PLhs := .bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1))

def carryBody : PStmt :=
  .block [.ifStmt (.bitSel (.ident "p") (.genvarRef "i"))
    (.blockingAssignL carryLhs (.bitSel (.ident "c") (.genvarRef "i")))
    (some (.blockingAssignL carryLhs (.bitSel (.ident "a") (.genvarRef "i"))))]

def carryPT : PT :=
  .blk (.ite (.bitSel (.ident "p") (.genvarRef "i"))
    (.leafL carryLhs (.bitSel (.ident "c") (.genvarRef "i")))
    (.leafL carryLhs (.bitSel (.ident "a") (.genvarRef "i"))))

/-- The declarations of the design: `a`, `b`, `p`, `s` are `[N-1:0]`, `c` is `[N:0]`, as `PDesign.summary` reads them. -/
def apDecls : List DeclT :=
  let nm1 : Aff := ⟨[("N", 1)], -1⟩
  let dm1 : PDim := ⟨.binary (.m0 .sub) (.paramRef "N" none) (.int 1), .int 0⟩
  [⟨"a", true, false, [(dm1, nm1, Aff.const 0)]⟩, ⟨"b", true, false, [(dm1, nm1, Aff.const 0)]⟩,
   ⟨"cin", true, false, []⟩, ⟨"s", false, true, [(dm1, nm1, Aff.const 0)]⟩, ⟨"cout", false, true, []⟩,
   ⟨"c", false, false, [(⟨.paramRef "N" none, .int 0⟩, ⟨[("N", 1)], 0⟩, Aff.const 0)]⟩,
   ⟨"p", false, false, [(dm1, nm1, Aff.const 0)]⟩]

-- The recognizer accepts the carry cell, reads the access `c[i+1]` as its target and finds the three reads
-- (the condition `p[i]`, then `c[i]`, then `a[i]`).
#guard match procTree? apDecls (carryPT.toProc) with
  | .ok (tg, ptr) =>
      tg == .bit "c" ⟨[("i", 1)], 1⟩ &&
        ptr.rds == [.bit "p" ⟨[("i", 1)], 0⟩, .bit "c" ⟨[("i", 1)], 0⟩, .bit "a" ⟨[("i", 1)], 0⟩]
  | .error _ => false

#guard match procTree? apDecls (carryPT.toProc) with
  | .ok (_, ptr) => ptr.pt.toProc == carryPT.toProc && carryPT.toProc == .alwaysComb carryBody
  | .error _ => false

/-- The refusals, with their messages. -/
private def refusal (p : PProcess) : String :=
  match procTree? apDecls p with
  | .ok _ => "accepted"
  | .error m => m

private def cc : PExpr := .bitSel (.ident "c") (.genvarRef "i")
private def aa : PExpr := .bitSel (.ident "a") (.genvarRef "i")
private def pp : PExpr := .bitSel (.ident "p") (.genvarRef "i")

#guard refusal (.alwaysComb (.block [.ifStmt pp (.blockingAssignL carryLhs cc) none])) ==
  "always_comb does not assign its target on every path (an `if` without `else` is a latch)"
#guard refusal (.alwaysComb (.block [.ifStmt pp (.blockingAssignL carryLhs cc)
    (some (.blockingAssignL (.bitSel "s" (.genvarRef "i")) aa))])) ==
  "always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)"
#guard refusal (.alwaysComb (.block [.blockingAssignL carryLhs cc, .blockingAssignL carryLhs aa])) ==
  "always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)"
#guard refusal (.alwaysComb (.block [.caseStmt pp [] none false .none])) ==
  "always_comb statement `case` (outside the first fragment)"
#guard refusal (.alwaysComb (.block [.nbaAssignL carryLhs cc])) ==
  "nonblocking assignment in always_comb (outside the v1 fragment)"
-- a whole-signal statement and an `else if` chain are accepted
#guard refusal (.alwaysComb (.block [.ifStmt pp (.blockingAssign "cout" cc)
    (some (.ifStmt aa (.blockingAssign "cout" cc) (some (.blockingAssign "cout" aa))))])) == "accepted"

-- WP-G S2: `!`, `~`, `&&`, `||`, `==`, reductions and `?:` are in the fragment, as conditions and in leaves
#guard refusal (.alwaysComb (.block [.ifStmt (.unary (.m0 .lnot) pp) (.blockingAssignL carryLhs cc)
    (some (.blockingAssignL carryLhs aa))])) == "accepted"
#guard refusal (.alwaysComb (.block [.ifStmt (.binary .land pp (.binary .lor aa cc))
    (.blockingAssignL carryLhs (.unary (.m0 .bnot) cc))
    (some (.blockingAssignL carryLhs (.ternary pp cc aa)))])) == "accepted"
#guard refusal (.alwaysComb (.block [.ifStmt (.reduce .or (.ident "a"))
    (.blockingAssignL carryLhs (.binary (.m0 .eq) cc aa))
    (some (.blockingAssignL carryLhs aa))])) == "accepted"
-- the leaves of such a body, condition first, in the order of the skeleton
#guard match procTree? apDecls (.alwaysComb (.block [.ifStmt (.unary (.m0 .lnot) pp)
    (.blockingAssignL carryLhs (.ternary pp cc aa)) (some (.blockingAssignL carryLhs aa))])) with
  | .ok (_, ptr) =>
      ptr.rds == [.bit "p" ⟨[("i", 1)], 0⟩, .bit "p" ⟨[("i", 1)], 0⟩, .bit "c" ⟨[("i", 1)], 0⟩,
        .bit "a" ⟨[("i", 1)], 0⟩, .bit "a" ⟨[("i", 1)], 0⟩]
  | .error _ => false
-- arithmetic and ordering operators stay outside the fragment
#guard (refusal (.alwaysComb (.block [.ifStmt (.binary (.m0 .add) pp aa) (.blockingAssignL carryLhs cc)
    (some (.blockingAssignL carryLhs aa))]))).startsWith "operator `+` is outside the v1 fragment"
#guard (refusal (.alwaysComb (.block [.ifStmt (.unary (.m0 .neg) pp) (.blockingAssignL carryLhs cc)
    (some (.blockingAssignL carryLhs aa))]))).startsWith "unary operator `-` or `+`"

/-- The declarations of the lowering, at a symbolic width (the lowering reads names and widths only). -/
def apDesign (N : Nat) : Design2 where
  name := "add_proc"
  decls := #[
    { name := "a", width := N, isInput := true },
    { name := "b", width := N, isInput := true },
    { name := "cin", width := 1, isInput := true },
    { name := "s", width := N, isOutput := true },
    { name := "cout", width := 1, isOutput := true },
    { name := "c", width := N + 1 },
    { name := "p", width := N }]
  processes := #[]

theorem ap_symNames (N : Nat) : (apDesign N).symNames = ["a", "b", "cin", "s", "cout", "c", "p"] := rfl

theorem ap_declWidth_c (N : Nat) : (apDesign N).declWidth "c" = some (N + 1) := by
  simp [Design2.declWidth, apDesign]

/-- **The carry cell lowers, at a symbolic `N` and an arbitrary bit `k < N`**, in any instantiation
environment that binds `i` to `k` and knows the one-bit elements: to `assign {c[k+1]} = {ifGuard(p[k]) ? c[k] : a[k]}`
(each leaf under the `resize` to the target width). -/
theorem carry_lowers (N k : Nat) (hk : k < N) (E : IEnv) (elems : List (String × Nat))
    (hc : elems.lookup "c" = some 1) (ha : elems.lookup "a" = some 1) (hp : elems.lookup "p" = some 1)
    (hi : E.vals.lookup "i" = some (k : Int)) :
    Process2.lowerComb (apDesign N) (instProcess2 E elems carryPT.toProc) =
      some (.assign (.concat [.slice "c" (k + 1) 1])
        (.concat #[Expr2.ternary
          (Expr2.ifGuard (.slice (.ident "p") k 1))
          (.resize 1 (.slice (.ident "c") k 1)) (.resize 1 (.slice (.ident "a") k 1))])) := by
  have hev1 : evalInt E (.binary (.m0 .add) (.genvarRef "i") (.int 1)) = .ok ((k : Int) + 1) := by
    have := (affOf?_sound (E := E) (σ := fun n => if n = "i" then (k : Int) else 0)
      (.binary (.m0 .add) (.genvarRef "i") (.int 1)) ⟨[("i", 1)], 1⟩
      (by simp [affOf?, affBin, Aff.add, Aff.var, Aff.const])
      (by intro n hn; simp [Aff.names] at hn; subst hn; simpa using hi)).2
    simpa [Aff.eval, Aff.evalTerms, Int.add_comm] using this
  have hev0 : evalInt E (.genvarRef "i") = .ok (k : Int) := evalInt_genvarRef_of hi
  have hlhs : instLhs2 E elems carryLhs = .ok (Win.lhs ("c", k + 1, 1), 1) := by
    have := instLhs2_bitSel (env := E) (elems := elems) hc hev1 (by omega)
    simpa [carryLhs, Win.lhs] using this
  have htg : carryPT.Tgt E elems (Win.lhs ("c", k + 1, 1)) 1 := by
    simp only [carryPT, PT.Tgt]
    exact ⟨hlhs, hlhs⟩
  rw [instProcess2_tree carryPT htg]
  have hlow : carryPT.low E elems 1 =
      .blk (.ite (.slice (.ident "p") k 1) (.leaf (.slice (.ident "c") k 1))
        (.leaf (.slice (.ident "a") k 1))) := by
    simp [carryPT, PT.low, instExpr2_bitSel_ident _ hp hev0 (by omega),
      fitExpr2_bitSel_ident hc hev0 (by omega), fitExpr2_bitSel_ident ha hev0 (by omega)]
  have hsw : (Win.lhs ("c", k + 1, 1)).symWin (apDesign N) = some ("c", k + 1, 1) := by
    simp [Lhs2.symWin, Win.lhs, Lhs2.window?, ap_declWidth_c N]; omega
  rw [hlow, lower_tree' (apDesign N) _ (Win.lhs ("c", k + 1, 1)) ("c", k + 1, 1) hsw
    (by simp [Win.lhs, Lhs2.mayW]) (by simp [Win.lhs, Lhs2.rdW])]
  · simp [PTree.low, Expr2.joinIte, Expr2.same, Win.lhs]
  · simp [PTree.wf, Expr2.wfB, Expr2.unsupportedFree, Expr2.idents, ap_symNames]
  · simp [PTree.idxFree, Expr2.idxFree]
  · simp [PTree.noRead, Expr2.reads, Expr2.sliceReads, ReadWin.overlaps, Win.overlaps]


/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombProc.instStmt2_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instStmt2_tree

/-- info: 'LeanModels.Sv.CombProc.instProcess2_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instProcess2_tree

/-- info: 'LeanModels.Sv.CombProc.inst_leaf_idxFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_leaf_idxFree

/-- info: 'LeanModels.Sv.CombProc.inst_rdsLeaf_idxFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_rdsLeaf_idxFree

/-- info: 'LeanModels.Sv.CombProc.inst_parts_idxFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_parts_idxFree

/-- info: 'LeanModels.Sv.CombProc.inst_idxFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_idxFree

/-- info: 'LeanModels.Sv.CombProc.rhs_idxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhs_idxFree

/-- info: 'LeanModels.Sv.CombProc.low_idxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_idxFree

/-- info: 'LeanModels.Sv.CombProc.low_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_wf

/-- info: 'LeanModels.Sv.CombProc.low_noRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_noRead

/-- info: 'LeanModels.Sv.CombProc.lhs_eq_win_lhs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms lhs_eq_win_lhs

/-- info: 'LeanModels.Sv.CombProc.tgt_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tgt_facts

/-- info: 'LeanModels.Sv.CombProc.tree_tgt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_tgt

/-- info: 'LeanModels.Sv.CombProc.lower_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_site

/-- info: 'LeanModels.Sv.CombProc.treeStmt?_spec' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStmt?_spec

/-- info: 'LeanModels.Sv.CombProc.treeStmts?_spec' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStmts?_spec

/-- info: 'LeanModels.Sv.CombProc.ap_symNames' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ap_symNames

/-- info: 'LeanModels.Sv.CombProc.ap_declWidth_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ap_declWidth_c

/-- info: 'LeanModels.Sv.CombProc.carry_lowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms carry_lowers

end CombProc
end LeanModels.Sv
