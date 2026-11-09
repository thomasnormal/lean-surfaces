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

/-- A `case` arm of the first fragment (WP-G S3a): one assignment of the target, `t = v;` or `n = v;`
(no `begin … end`, no nested statement). -/
inductive PLf where
  | leafL (t : PLhs) (v : PExpr)
  | leafW (n : String) (v : PExpr)

/-- The right-hand side of an arm. -/
def PLf.val : PLf → PExpr
  | .leafL _ v => v
  | .leafW _ v => v

/-- The statement an arm stands for. -/
def PLf.toPStmt : PLf → PStmt
  | .leafL t v => .blockingAssignL t v
  | .leafW n v => .blockingAssign n v

/-- The arms as the items of a `case` statement. -/
def PLf.items : List (List PExpr × PLf) → List (List PExpr × PStmt)
  | [] => []
  | (ps, a) :: rest => (ps, a.toPStmt) :: PLf.items rest

/-- An arm's value fitted to the target width `w`. -/
def PLf.low (E : IEnv) (elems : List (String × Nat)) (w : Nat) (a : PLf) : Expr2 :=
  fitExpr2 E elems (some w) a.val

/-- The instantiated arms: patterns at the comparison width `sctx`, values fitted to `w`. -/
def PLf.lowArms (E : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) (w : Nat) :
    List (List PExpr × PLf) → List (List Expr2 × Expr2)
  | [] => []
  | (ps, a) :: rest => (instPats2 E elems sctx ps, a.low E elems w) :: PLf.lowArms E elems sctx w rest

/-- The arm's target instantiates to `tgt` at width `w`. -/
def PLf.Tgt (E : IEnv) (elems : List (String × Nat)) (tgt : Lhs2) (w : Nat) : PLf → Prop
  | .leafL t _ => instLhs2 E elems t = .ok (tgt, w)
  | .leafW n _ => instLhs2 E elems (.ident n) = .ok (tgt, w)

/-- The template of an S1 body: a tree of `if/else` over right-hand sides, every leaf assigning one target
(`leafL`: `t = v;` with a select target; `leafW`: `n = v;`, the whole-signal statement form). `blk` is a
`begin t end` around one tree. -/
inductive PT where
  | leafL (t : PLhs) (v : PExpr)
  | leafW (n : String) (v : PExpr)
  | ite (c : PExpr) (a b : PT)
  | blk (a : PT)
  /-- A plain `case` with a `default` whose arms are single assignments (WP-G S3a). -/
  | cases (s : PExpr) (its : List (List PExpr × PLf)) (d : PLf)
  /-- Default-then-override (WP-G S3b): `b; if (c) a;`, the statements of `b` then an `if` without `else`. -/
  | ovr (c : PExpr) (a b : PT)

/-- The statements of a block, or the statement itself. -/
def PStmt.unblock : PStmt → List PStmt
  | .block ss => ss
  | s => [s]

/-- The template is an override. -/
def PT.isOvr : PT → Bool
  | .ovr .. => true
  | _ => false

/-- The statement a template tree stands for. -/
def PT.toPStmt : PT → PStmt
  | .leafL t v => .blockingAssignL t v
  | .leafW n v => .blockingAssign n v
  | .ite c a b => .ifStmt c a.toPStmt (some b.toPStmt)
  | .blk a => .block [a.toPStmt]
  | .cases s its d => .caseStmt s (PLf.items its) (some d.toPStmt) .normal .none
  | .ovr c a b =>
      .block ((if b.isOvr then PStmt.unblock b.toPStmt else [b.toPStmt]) ++ [PStmt.ifStmt c a.toPStmt none])

/-- The statements a template tree stands for: the block of an override, else the one statement. -/
def PT.stmtsP (b : PT) : List PStmt := if b.isOvr then PStmt.unblock b.toPStmt else [b.toPStmt]

/-- The template process: `always_comb <tree>` (the top node is a `blk` for `begin ... end`). -/
def PT.toProc (pt : PT) : PProcess := .alwaysComb pt.toPStmt

/-- Its instantiation as a `PTree`: leaves fitted to the target width `w`, conditions self-determined. -/
def PT.low (E : IEnv) (elems : List (String × Nat)) (w : Nat) : PT → PTree
  | .leafL _ v => .leaf (fitExpr2 E elems (some w) v)
  | .leafW _ v => .leaf (fitExpr2 E elems (some w) v)
  | .ite c a b => .ite (instExpr2 E elems none c) (a.low E elems w) (b.low E elems w)
  | .blk a => .blk (a.low E elems w)
  | .cases s its d =>
      .cases (fitExpr2 E elems (caseWidth2 E elems s (PLf.items its)) s)
        (PLf.lowArms E elems (caseWidth2 E elems s (PLf.items its)) w its) (d.low E elems w)
  | .ovr c a b => .ovr (instExpr2 E elems none c) (a.low E elems w) (b.low E elems w)

/-- Every leaf target instantiates to the target `tgt` of width `w`. -/
def PT.Tgt (E : IEnv) (elems : List (String × Nat)) (tgt : Lhs2) (w : Nat) : PT → Prop
  | .leafL t _ => instLhs2 E elems t = .ok (tgt, w)
  | .leafW n _ => instLhs2 E elems (.ident n) = .ok (tgt, w)
  | .ite _ a b => a.Tgt E elems tgt w ∧ b.Tgt E elems tgt w
  | .blk a => a.Tgt E elems tgt w
  | .cases _ its d => (∀ it ∈ its, it.2.Tgt E elems tgt w) ∧ d.Tgt E elems tgt w
  | .ovr _ a b => a.Tgt E elems tgt w ∧ b.Tgt E elems tgt w

theorem instStmt2_plf {E : IEnv} {elems : List (String × Nat)} {tgt : Lhs2} {w : Nat} :
    ∀ a : PLf, a.Tgt E elems tgt w → instStmt2 E elems a.toPStmt = .blockingAssign tgt (a.low E elems w)
  | .leafL t v, h => by
      simp only [PLf.Tgt] at h
      simp [PLf.toPStmt, PLf.low, PLf.val, instStmt2, h]
  | .leafW n v, h => by
      simp only [PLf.Tgt, instLhs2, instLhsLeaf2] at h
      split at h
      · rename_i w' hw'
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [PLf.toPStmt, PLf.low, PLf.val, instStmt2, hw']
      · simp at h

theorem instItems2_arms {E : IEnv} {elems : List (String × Nat)} {tgt : Lhs2} {w : Nat}
    (sctx : Option Nat) :
    ∀ its : List (List PExpr × PLf), (∀ it ∈ its, it.2.Tgt E elems tgt w) →
      instItems2 E elems sctx (PLf.items its) = caseItems tgt (PLf.lowArms E elems sctx w its)
  | [], _ => by simp [PLf.items, PLf.lowArms, instItems2, caseItems]
  | (ps, a) :: rest, h => by
      simp only [PLf.items, PLf.lowArms, instItems2, caseItems]
      rw [instStmt2_plf a (h (ps, a) (List.mem_cons_self ..)),
        instItems2_arms sctx rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem instStmts2_append (E : IEnv) (elems : List (String × Nat)) :
    ∀ l1 l2 : List PStmt, instStmts2 E elems (l1 ++ l2) = instStmts2 E elems l1 ++ instStmts2 E elems l2
  | [], l2 => by simp [instStmts2]
  | s :: r, l2 => by simp [instStmts2, instStmts2_append E elems r l2]

theorem low_isOvr (E : IEnv) (elems : List (String × Nat)) (w : Nat) (b : PT) :
    (b.low E elems w).isOvr = b.isOvr := by
  cases b <;> rfl

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
  | cases s its d =>
      intro ⟨h1, h2⟩
      simp only [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, CaseMode.isInside,
        Bool.false_and, Bool.false_eq_true, if_false]
      rw [instItems2_arms _ its h1, instStmt2_plf d h2]
  | ovr c a b iha ihb =>
      intro ⟨h1, h2⟩
      have hb := ihb h2
      have hbase : instStmts2 E elems (if b.isOvr then PStmt.unblock b.toPStmt else [b.toPStmt]) =
          (b.low E elems w).baseL ((b.low E elems w).toStmt tgt) := by
        unfold PTree.baseL
        rw [low_isOvr]
        split
        · rename_i ho
          cases b <;> simp [PT.isOvr] at ho
          have := congrArg Stmt2.unblock hb
          simpa [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, PStmt.unblock, Stmt2.unblock] using this
        · simp [instStmts2, hb]
      simp only [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, instStmts2_append, hbase]
      simp [instStmts2, instStmt2, iha h1]

/-- **The instantiation of a template tree IS the `PTree` statement, under the self-read guard.** -/
theorem instProcess2_tree {E : IEnv} {elems : List (String × Nat)} {tgt : Lhs2} {w : Nat}
    (pt : PT) (h : pt.Tgt E elems tgt w) :
    instProcess2 E elems pt.toProc =
      combGuardProc (fun n => E.widths.lookup n) ((pt.low E elems w).toStmt tgt) := by
  simp [PT.toProc, instProcess2, instStmt2_tree pt h]

/-! ## The annotated tree: each expression with the reads the recognizer found -/

/-- An arm with the read accesses `rhsRds?` computed for its value. -/
inductive PLfR where
  | leafL (t : PLhs) (v : PExpr) (rs : List Acc)
  | leafW (n : String) (v : PExpr) (rs : List Acc)

/-- The arm underneath. -/
def PLfR.pl : PLfR → PLf
  | .leafL t v _ => .leafL t v
  | .leafW n v _ => .leafW n v

/-- The reads of the arm's value. -/
def PLfR.rds : PLfR → List Acc
  | .leafL _ _ rs => rs
  | .leafW _ _ rs => rs

/-- The arm passed the recognizer's checks for the target access `tg`. -/
def PLfR.Ok (ds : List DeclT) (tg : Acc) : PLfR → Prop
  | .leafL t v rs => tgtOf? ds t = .ok tg ∧ rhsRds? ds v = .ok rs ∧ fragOkL v = true
  | .leafW n v rs => tgtOf? ds (.ident n) = .ok tg ∧ rhsRds? ds v = .ok rs ∧ fragOkL v = true

/-- The arms underneath. -/
def PLfR.arms : List (List PExpr × PLfR) → List (List PExpr × PLf)
  | [] => []
  | (ps, a) :: rest => (ps, a.pl) :: PLfR.arms rest

/-- The reads of the arms' values, in source order. -/
def PLfR.armRds : List (List PExpr × PLfR) → List Acc
  | [] => []
  | (_, a) :: rest => a.rds ++ PLfR.armRds rest

/-- Every pattern is a literal and every arm passed. -/
def PLfR.ArmsOk (ds : List DeclT) (tg : Acc) (its : List (List PExpr × PLfR)) : Prop :=
  ∀ it ∈ its, (∀ p ∈ it.1, ∃ v, p = PExpr.lit v) ∧ it.2.Ok ds tg

/-- A template tree with, at every node, the read accesses `rdsOf?`/`rhsRds?` computed for it. -/
inductive PTR where
  | leafL (t : PLhs) (v : PExpr) (rs : List Acc)
  | leafW (n : String) (v : PExpr) (rs : List Acc)
  | ite (c : PExpr) (rc : List Acc) (a b : PTR)
  | blk (a : PTR)
  /-- A `case` (WP-G S3a): the subject and its reads, the arms, the default. -/
  | cases (s : PExpr) (rc : List Acc) (its : List (List PExpr × PLfR)) (d : PLfR)
  /-- Default-then-override (WP-G S3b): the condition and its reads, the branch, the statements before. -/
  | ovr (c : PExpr) (rc : List Acc) (a b : PTR)

/-- The template tree underneath. -/
def PTR.pt : PTR → PT
  | .leafL t v _ => .leafL t v
  | .leafW n v _ => .leafW n v
  | .ite c _ a b => .ite c a.pt b.pt
  | .blk a => .blk a.pt
  | .cases s _ its d => .cases s (PLfR.arms its) d.pl
  | .ovr c _ a b => .ovr c a.pt b.pt

/-- All the read accesses of the tree, condition first (the site's read list). -/
def PTR.rds : PTR → List Acc
  | .leafL _ _ rs => rs
  | .leafW _ _ rs => rs
  | .ite _ rc a b => rc ++ a.rds ++ b.rds
  | .blk a => a.rds
  | .cases _ rc its d => rc ++ PLfR.armRds its ++ d.rds
  | .ovr _ rc a b => b.rds ++ rc ++ a.rds

/-- The recognizer's verdict on every node, for the target access `tg`: each leaf target is `tg`
(`tgtOf?`), right-hand sides are in the fragment of `sv_equations` (`rhsRds?`, `fragOk`), conditions are
gate trees (`rdsOf?`, `fragG`). -/
def PTR.Ok (ds : List DeclT) (tg : Acc) : PTR → Prop
  | .leafL t v rs => tgtOf? ds t = .ok tg ∧ rhsRds? ds v = .ok rs ∧ fragOkL v = true
  | .leafW n v rs => tgtOf? ds (.ident n) = .ok tg ∧ rhsRds? ds v = .ok rs ∧ fragOkL v = true
  | .ite c rc a b => (rdsOf? ds c = .ok rc ∧ fragG c = true) ∧ a.Ok ds tg ∧ b.Ok ds tg
  | .blk a => a.Ok ds tg
  | .cases s rc its d => (rdsOf? ds s = .ok rc ∧ fragG s = true) ∧ PLfR.ArmsOk ds tg its ∧ d.Ok ds tg
  | .ovr c rc a b => (rdsOf? ds c = .ok rc ∧ fragG c = true) ∧ a.Ok ds tg ∧ b.Ok ds tg

theorem mem_armRds {a : Acc} : ∀ {its : List (List PExpr × PLfR)} {it : List PExpr × PLfR},
    it ∈ its → a ∈ it.2.rds → a ∈ PLfR.armRds its
  | (ps, b) :: rest, it, hit, ha => by
      simp only [PLfR.armRds, List.mem_append]
      rcases List.mem_cons.mp hit with rfl | hit
      · exact Or.inl ha
      · exact Or.inr (mem_armRds hit ha)

theorem mem_arms : ∀ {its : List (List PExpr × PLfR)} {x : List PExpr × PLf},
    x ∈ PLfR.arms its → ∃ it ∈ its, x = (it.1, it.2.pl)
  | (ps, a) :: rest, x, h => by
      simp only [PLfR.arms, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨(ps, a), List.mem_cons_self .., rfl⟩
      · obtain ⟨it, hit, rfl⟩ := mem_arms h
        exact ⟨it, List.mem_cons_of_mem _ hit, rfl⟩

/-- The instantiated arms are exactly the arms' instantiations. -/
theorem mem_lowArms (E : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) (tw : Nat) :
    ∀ (its : List (List PExpr × PLfR)) (x : List Expr2 × Expr2),
      x ∈ PLf.lowArms E elems sctx tw (PLfR.arms its) ↔
        ∃ it ∈ its, x = (instPats2 E elems sctx it.1, it.2.pl.low E elems tw)
  | [], x => by simp [PLfR.arms, PLf.lowArms]
  | (ps, a) :: rest, x => by
      have ih := mem_lowArms E elems sctx tw rest x
      simp only [PLfR.arms, PLf.lowArms]
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨(ps, a), List.mem_cons_self .., h⟩
        · obtain ⟨it, hit, h⟩ := ih.1 h
          exact ⟨it, List.mem_cons_of_mem _ hit, h⟩
      · rintro ⟨it, hit, h⟩
        rcases List.mem_cons.mp hit with rfl | hit
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons.mpr (Or.inr (ih.2 ⟨it, hit, h⟩))

/-- Literal patterns instantiate to literals (possibly resized): no reads, names, `index` or loud nodes. -/
theorem instPats2_simple (E : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) :
    ∀ ps : List PExpr, (∀ p ∈ ps, ∃ v, p = PExpr.lit v) →
      Expr2.listIdxFree (instPats2 E elems sctx ps) = true ∧
        Expr2.listUnsupportedFree (instPats2 E elems sctx ps) = true ∧
        Expr2.listIdents (instPats2 E elems sctx ps) = [] ∧
        Expr2.listReads (instPats2 E elems sctx ps) = []
  | [], _ => by
      simp [instPats2, Expr2.listIdxFree, Expr2.listUnsupportedFree, Expr2.listIdents,
        Expr2.listReads]
  | p :: ps, h => by
      obtain ⟨v, rfl⟩ := h p (List.mem_cons_self ..)
      have ih := instPats2_simple E elems sctx ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have hf : fitExpr2 E elems sctx (.lit v) = .lit v ∨
          ∃ w, fitExpr2 E elems sctx (.lit v) = .resize w (.lit v) := by
        cases sctx with
        | none => left; simp [fitExpr2, instExpr2]
        | some w => rw [fitExpr2_lit]; split <;> simp
      rcases hf with hf | ⟨w, hf⟩ <;>
        simp [instPats2, hf, Expr2.listIdxFree, Expr2.listUnsupportedFree, Expr2.listIdents,
          Expr2.listReads, Expr2.idxFree, Expr2.unsupportedFree, Expr2.idents, Expr2.reads, ih]

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

/-- A replication of an `index`-free operand has no `index` node (the count is evaluated, or the node is
`unsupported`). -/
theorem inst_repl_idxFree {c a : PExpr} (ha : ∀ ctx, (instExpr2 E elems ctx a).idxFree = true)
    (ctx : Option Nat) : (instExpr2 E elems ctx (.repl c a)).idxFree = true := by
  simp only [instExpr2]
  cases hc : evalInt E c with
  | error e => simp [Expr2.idxFree]
  | ok n =>
      by_cases h0 : 0 ≤ n
      · simp [h0, Expr2.idxFree, ha]
      · simp [h0, Expr2.idxFree]

/-- A word-level replication (a literal or one access) has no `index` node, at any context. -/
theorem inst_repRd_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {c a : PExpr} {rs : List Acc}
    (h : repRd? ds c a = .ok rs) (hacc : ∀ x ∈ rs, AccOK σ DW DG EW ns x) (ctx : Option Nat) :
    (instExpr2 E elems ctx (.repl c a)).idxFree = true := by
  obtain ⟨k, hk, harg⟩ := repRd?_cases h
  apply inst_repl_idxFree
  intro ctx'
  rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, -, -⟩
  · simp [instExpr2_concat, instParts2_cons, Expr2.idxFree, Expr2.listIdxFree]
  · have := inst_rdsLeaf_idxFree C hdw hl hacc (selfWidth2 E elems e)
    simp [instExpr2_concat, instParts2_cons, Expr2.idxFree, Expr2.listIdxFree, this]

/-- The parts of a word-level concatenation have no `index` node. -/
theorem inst_parts_idxFreeW (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      Expr2.listIdxFree (instParts2 E elems ps) = true
  | [], rs, h, _ => by simp [Expr2.listIdxFree]
  | p :: ps, rs, h, hacc => by
      simp only [partsRdW?] at h
      rcases hp : partRdW? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRdW? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          have h1 : (instExpr2 E elems (selfWidth2 E elems p) p).idxFree = true := by
            unfold partRdW? at hp
            cases p with
            | lit v => simp [Expr2.idxFree]
            | repl c a => exact inst_repRd_idxFree C hdw hp (fun x hx => hacc x (List.mem_append_left _ hx)) _
            | _ =>
                obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
                exact inst_leaf_idxFree C hdw hl (hacc a (List.mem_append_left _ (by simp))) _
          have h2 := inst_parts_idxFreeW C hdw ps rb hq (fun a ha => hacc a (List.mem_append_right _ ha))
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
  | .partSel b pm pl, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .arrayElem n is, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .arrayPart n is m a b, rs, h, hacc, ctx =>
      inst_rdsLeaf_idxFree C hdw (by simpa [rdsOf?] using h) hacc ctx
  | .repl .., rs, h, _, _
  | .paramRef .., rs, h, _, _
  | .genvarRef .., rs, h, _, _ | .enumRef .., rs, h, _, _
  | .int .., rs, h, _, _ | .fill .., rs, h, _, _
  | .resize .., rs, h, _, _ | .signedResize .., rs, h, _, _
  | .squash2 .., rs, h, _, _ | .sysCall .., rs, h, _, _
  | .cast .., rs, h, _, _ | .unsupported .., rs, h, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

theorem idxFree_fitDiv {x : Expr2} (h : x.idxFree = true) (s : Bool) (c w : Option Nat) :
    (fitDivOperand2 s c w x).idxFree = true := by
  cases c <;> cases w <;> simp only [fitDivOperand2]
  · exact h
  · exact h
  · exact h
  · split
    · exact h
    · cases s <;> simpa [Expr2.idxFree] using h

theorem idxFree_ctxTrunc {x : Expr2} (h : x.idxFree = true) (ctx ow : Option Nat) :
    (ctxTrunc2 ctx ow x).idxFree = true := by
  cases ctx <;> cases ow <;> simp only [ctxTrunc2]
  · exact h
  · exact h
  · exact h
  · split
    · exact h
    · simpa [Expr2.idxFree] using h

/-- A shift operand instantiates to an expression with no `index` node, at any context. -/
theorem idxFree_shOpd (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (h : shOpdRd? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (s : Bool) (c : Option Nat) :
    (instDivOperand2 E elems s c e).idxFree = true := by
  rw [instDiv_default s c e (shOpdKind h)]
  refine idxFree_fitDiv ?_ s _ _
  rcases shOpdRd?_cases h with ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨a, hl, rfl⟩
  · simp [instDivOperand2, divOperandWidth2, instExpr2, intLit2_eq, fitDivOperand2, Expr2.idxFree]
  · simp [instExpr2, Expr2.idxFree]
  · exact inst_leaf_idxFree C hdw hl (hacc a (by simp)) _

/-- The amount of a shift: a genvar lowers to a literal (or a loud node), never an `index`. -/
theorem idxFree_shAmt (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (h : shAmtRd? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (s : Bool) (c : Option Nat) :
    (instDivOperand2 E elems s c e).idxFree = true := by
  rcases shAmtRd?_cases h with ⟨g, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | h'
  · have e1 : instDivOperand2 E elems s c (.genvarRef g) = fitDivOperand2 s c (some 32)
        (instExpr2 E elems (some 32) (.genvarRef g)) := by
      simp [instDivOperand2, divOperandWidth2]
    rw [e1]
    refine idxFree_fitDiv ?_ s _ _
    rcases hb : E.vals.lookup g with _ | v <;> rcases hn : E.nvals.lookup g with _ | ⟨v', w, s'⟩ <;>
      simp [instExpr2, hb, hn, intLit2_eq, Expr2.idxFree] <;> first | done | rfl
  · unfold instDivOperand2
    cases hc : c <;>
      cases hv : E.vals.lookup n <;>
      cases hn : E.nvals.lookup n <;>
      by_cases hs : n ∈ E.stale <;>
      simp [hc, hv, hn, hs, divOperandWidth2, instExpr2, intLit2_eq, fitDivOperand2,
        Expr2.idxFree] <;> cases s <;> split <;> simp [Expr2.idxFree, *]
  · exact idxFree_shOpd C hdw h' hacc s c

theorem idxFree_shLeft (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {rs : List Acc}
    {s : Bool} (h : shLeftRd? ds s e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (c : Option Nat) :
    (instDivOperand2 E elems s c e).idxFree = true := by
  obtain ⟨x, hx, hxo⟩ := shLeftRd?_cases h
  rcases hx with rfl | ⟨rfl, m, rfl⟩ | ⟨rfl, m, rfl⟩
  · exact idxFree_shOpd C hdw hxo hacc s c
  · rw [instDiv_resize false c m x (shOpdKind hxo)]
    exact idxFree_shOpd C hdw hxo hacc false _
  · rw [instDiv_sresize true c m x]
    exact idxFree_shOpd C hdw hxo hacc true _

/-- **An expression of the word-level fragment** (WP-B2 gate 2: the context-determined positions through
`rdsOfW?`, the self-determined operands through the v1 theorem `inst_idxFree`) instantiates to an expression with
no `index` node, at any context. -/
theorem inst_idxFreeW (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (e : PExpr) (rs : List Acc), rdsOfW? ds e = .ok rs → (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      ∀ ctx, (instExpr2 E elems ctx e).idxFree = true
  | .lit v, rs, h, _, ctx => by simp [Expr2.idxFree]
  | .binary op l r, rs, h, hacc, ctx => by
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr', rfl⟩ | ⟨hb, ra, rb, hl, hr', rfl⟩ |
        ⟨hb, ra, rb, hl, hr', rfl⟩ | ⟨cm, a, b, hcm, rfl, rfl, -, -, rfl⟩
      rotate_left 3
      · -- a signed comparison of two signed signals: `scmp` of the two fitted reads
        have hsr : ∀ (n : String) (c : Option Nat), (fitExpr2 E elems c (.cast true (.ident n))).idxFree = true := by
          intro n c
          have hi : ∀ c', (instExpr2 E elems c' (.cast true (.ident n))).idxFree = true := by
            intro c'; simp [instExpr2, Expr2.idxFree]
          unfold fitExpr2
          split
          · exact hi _
          · split
            · split
              · split
                · exact hi _
                · split
                  · simp [Expr2.idxFree]
                  · simp [Expr2.idxFree, hi]
              · exact hi _
            · exact hi _
        cases op <;> simp [scmpOp?] at hcm <;> subst hcm <;> cases ctx <;>
          simp [instExpr2, Expr2.idxFree, hsr]
      · have ihl := inst_idxFreeW C hdw l ra hl (fun a ha => hacc a (List.mem_append_left _ ha))
        have ihr := inst_idxFreeW C hdw r rb hr' (fun a ha => hacc a (List.mem_append_right _ ha))
        have hfl := fit_idxFree (E := E) (elems := elems) (signedCast_of_rdsW hl) ihl
        have hfr := fit_idxFree (E := E) (elems := elems) (signedCast_of_rdsW hr') ihr
        have gate : ∀ g : BinOp, (g = .and ∨ g = .or ∨ g = .xor) →
            (instExpr2 E elems ctx (.binary (.m0 g) l r)).idxFree = true := by
          intro g hg
          obtain ⟨c, hc⟩ := instExpr2_gate E elems ctx g hg l r
          rw [hc]
          simp [Expr2.idxFree, hfl c, hfr c]
        have addsub : ∀ g : BinOp, (g = .add ∨ g = .sub) →
            (instExpr2 E elems ctx (.binary (.m0 g) l r)).idxFree = true := by
          intro g hg
          rcases ie_addsub_cases (env := E) (elems := elems) g hg ctx l r with ⟨c, hc⟩ | ⟨w, c, hc⟩
          · rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
          · rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
        rcases ctxOpW_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | ⟨cm, rfl⟩
        · exact gate .and (Or.inl rfl)
        · exact gate .or (Or.inr (Or.inl rfl))
        · exact gate .xor (Or.inr (Or.inr rfl))
        · exact addsub .add (Or.inl rfl)
        · exact addsub .sub (Or.inr rfl)
        · rcases ie_mul_cases (env := E) (elems := elems) (rdsOfW?_mul h) ctx with ⟨c, hc⟩ | ⟨w, c, hc⟩
          · rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
          · rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
        · obtain ⟨c, hc⟩ := ie_cmp_cases (env := E) (elems := elems) cm ctx l r
          rw [hc]; simp [Expr2.idxFree, hfl c, hfr c]
      · have ihl := inst_idxFree C hdw l ra hl (fun a ha => hacc a (List.mem_append_left _ ha))
        have ihr := inst_idxFree C hdw r rb hr' (fun a ha => hacc a (List.mem_append_right _ ha))
        rcases selfOpW_cases hb with rfl | rfl
        · rw [ie_land]; simp [Expr2.idxFree, ihl, ihr]
        · rw [ie_lor]; simp [Expr2.idxFree, ihl, ihr]
      · -- a run-time shift (WP-B2 gate 3)
        have hR := idxFree_shAmt C hdw hr' (fun a ha => hacc a (List.mem_append_right _ ha)) false
        rcases shOpW_cases hb with ⟨s, rfl⟩ | rfl
        · have hL : ∀ c, (instDivOperand2 E elems s c l).idxFree = true :=
            idxFree_shLeft C hdw hl (fun a ha => hacc a (List.mem_append_left _ ha))
          obtain ⟨lc, hlc⟩ := ie_shl_form (env := E) (elems := elems) s ctx l r
          rw [hlc]; exact idxFree_ctxTrunc (by simp [Expr2.idxFree, hL lc, hR _]) ctx lc
        · have hL : ∀ c, (instDivOperand2 E elems false c l).idxFree = true :=
            idxFree_shLeft C hdw hl (fun a ha => hacc a (List.mem_append_left _ ha))
          obtain ⟨lc, hlc⟩ := ie_shr_form (env := E) (elems := elems) ctx l r
          rw [hlc]; exact idxFree_ctxTrunc (by simp [Expr2.idxFree, hL lc, hR _]) ctx lc
  | .unary op a, rs, h, hacc, ctx => by
      rcases rdsOfW?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · have iha := inst_idxFreeW C hdw a rs ha hacc
        have hfa := fit_idxFree (E := E) (elems := elems) (signedCast_of_rdsW ha) iha
        rcases ie_bnot_cases (env := E) (elems := elems) ctx a with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨w, c, hc⟩
        · rw [hc]; simpa [Expr2.idxFree] using iha c
        · rw [hc]; simpa [Expr2.idxFree] using hfa c
        · rw [hc]; simpa [Expr2.idxFree] using hfa c
      · have iha := inst_idxFree C hdw a rs ha hacc
        rw [ie_lnot]; simpa [Expr2.idxFree] using iha none
  | .ternary c t f, rs, h, hacc, ctx => by
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := rdsOfW?_ternary h
      have ihc := inst_idxFree C hdw c rc hc
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_left _ ha)))
      have iht := inst_idxFreeW C hdw t rt ht
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_right _ ha)))
      have ihf := inst_idxFreeW C hdw f rf hfe (fun a ha => hacc a (List.mem_append_right _ ha))
      obtain ⟨a0, ha0⟩ := ie_ternary_cases (env := E) (elems := elems) ctx c t f
      rw [ha0]
      simp [Expr2.idxFree, ihc none, fit_idxFree (signedCast_of_rdsW ht) iht a0,
        fit_idxFree (signedCast_of_rdsW hfe) ihf a0]
  | .reduce op a, rs, h, hacc, ctx => by
      have iha := inst_idxFree C hdw a rs (rdsOfW?_reduce h) hacc
      rw [ie_reduce]; simpa [Expr2.idxFree] using iha _
  | .concat ps, rs, h, hacc, ctx => by
      simp only [rdsOfW?] at h
      rw [instExpr2_concat]
      simpa [Expr2.idxFree] using inst_parts_idxFreeW C hdw ps rs h hacc
  | .repl c a, rs, h, hacc, ctx =>
      inst_repRd_idxFree C hdw (by simpa [rdsOfW?] using h) hacc ctx
  | .resize m e, rs, h, hacc, ctx => by
      rcases rdsOfW?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, hl, rfl⟩ | ⟨hop, hr⟩
      · obtain ⟨x, c, hx⟩ := ie_resize_cases (env := E) (elems := elems) (e := .lit v)
          rfl rfl (fun _ _ _ => by simp [PExpr.negGenvarWidened]) ctx m
        rw [hx]
        simp [Expr2.idxFree, instExpr2]
      · obtain ⟨hcp, hcl, hng⟩ := leaf_flags hl
        obtain ⟨x, c, hx⟩ := ie_resize_cases (env := E) (elems := elems) hcp hcl hng ctx m
        rw [hx]
        have := inst_rdsLeaf_idxFree C hdw (ds := ds) (e := e) (rs := [a]) (by simp [rdsLeaf?, hl]) hacc c
        simpa [Expr2.idxFree] using this
      · have ih := inst_idxFreeW C hdw e rs hr hacc
        rcases ie_resize_op (env := E) (elems := elems) hop ctx m with ⟨x, c, hx⟩ | ⟨cw, hx⟩
        · rw [hx]; simpa [Expr2.idxFree] using ih c
        · rw [hx]; exact ih _
  | .int v, rs, h, _, ctx => by
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      rw [ie_int]
      simp [Expr2.idxFree]
  | .ident n, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOfW?] using h) hacc ctx
  | .bitSel b i, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOfW?] using h) hacc ctx
  | .partSel b pm pl, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOfW?] using h) hacc ctx
  | .arrayElem n is, rs, h, hacc, ctx => inst_rdsLeaf_idxFree C hdw (by simpa [rdsOfW?] using h) hacc ctx
  | .arrayPart n is m a b, rs, h, hacc, ctx =>
      inst_rdsLeaf_idxFree C hdw (by simpa [rdsOfW?] using h) hacc ctx
  | .paramRef .., rs, h, _, _
  | .genvarRef .., rs, h, _, _ | .enumRef .., rs, h, _, _
  | .fill .., rs, h, _, _
  | .signedResize .., rs, h, _, _
  | .squash2 .., rs, h, _, _ | .sysCall .., rs, h, _, _
  | .cast .., rs, h, _, _ | .unsupported .., rs, h, _, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h

/-- A whole right-hand side, fitted to the target width: no `index` node. -/
theorem rhs_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (h : rhsRds? ds v = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (w : Nat) :
    (fitExpr2 E elems (some w) v).idxFree = true := by
  by_cases hf : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hf
    rw [fitExpr2_of_not_rigid w rfl]
    simp [instExpr2, Expr2.idxFree]
  · have hr : rhsRds? ds v = rdsOfW? ds v := by
      cases v <;> first | rfl | (exfalso; exact hf ⟨_, rfl⟩)
    rw [hr] at h
    rcases fitExpr2_cases E elems (some w) v (signedCast_of_rdsW h) with ⟨c, hc⟩ | ⟨w', c, hc⟩
    · rw [hc]; exact inst_idxFreeW C hdw v rs h hacc c
    · rw [hc]; simpa [Expr2.idxFree] using inst_idxFreeW C hdw v rs h hacc c

/-- An expression that reads only declared accesses is well formed for a design with the summary's widths. -/
theorem wfB_of_rd (σ' : String → Int) {d : Design2} (hd : ∀ n, d.declWidth n = DW n) {rs : List Acc}
    {x : Expr2} (hr : RdOK σ' rs x) (hacc : ∀ a ∈ rs, AccOK σ' DW DG EW ns a) : x.wfB d = true := by
  refine (wfB_iff d _).2 ⟨hr.1, fun i hi => ?_⟩
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.2 i hi)
  have := (hacc a ha).1
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
  exact Design2.mem_names_of_declWidth (w := w) (by rw [hd]; exact hw)

/-- An arm's value is a right-hand side: `RdOK` of its fit. -/
theorem plfr_rdOK (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {tg : Acc} :
    ∀ (a : PLfR), a.Ok ds tg → (∀ x ∈ a.rds, AccOK σ DW DG EW ns x) → ∀ tw,
      RdOK σ a.rds (a.pl.low E elems tw)
  | .leafL t v rs, hok, hacc, tw => rhs_ok C hok.2.1 hacc (fragOkL_co hok.2.2) (fragOkL_weq hok.2.2) tw
  | .leafW n v rs, hok, hacc, tw => rhs_ok C hok.2.1 hacc (fragOkL_co hok.2.2) (fragOkL_weq hok.2.2) tw

theorem plfr_idxFree (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc} :
    ∀ (a : PLfR), a.Ok ds tg → (∀ x ∈ a.rds, AccOK σ DW DG EW ns x) → ∀ tw,
      (a.pl.low E elems tw).idxFree = true
  | .leafL t v rs, hok, hacc, tw => rhs_idxFree C hdw hok.2.1 hacc tw
  | .leafW n v rs, hok, hacc, tw => rhs_idxFree C hdw hok.2.1 hacc tw

theorem plfr_tgt (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc}
    (hatg : AccOK σ DW DG EW ns tg) :
    ∀ (a : PLfR), a.Ok ds tg → a.pl.Tgt E elems (tg.lhs σ) (tg.win σ dw).2.2
  | .leafL _ _ _, hok => instLhs_acc_w C hdw hok.1 hatg
  | .leafW _ _ _, hok => instLhs_acc_w C hdw hok.1 hatg

/-- The subject of a `case`: a gate tree, fitted to the comparison width. -/
theorem subj_rdOK (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {s : PExpr} {rc : List Acc}
    (h : rdsOf? ds s = .ok rc) (hacc : ∀ x ∈ rc, AccOK σ DW DG EW ns x) (sctx : Option Nat) :
    RdOK σ rc (fitExpr2 E elems sctx s) :=
  RdOK.fit (signedCast_of_rds h) (inst_rd C s rc h hacc) sctx

/-- The per-expression facts about the instantiated arms (patterns: no reads, names, `index`; values:
`RdOK` of their fit). -/
theorem arms_facts (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {tg : Acc}
    (sctx : Option Nat) (tw : Nat) (its : List (List PExpr × PLfR)) (harms : PLfR.ArmsOk ds tg its)
    (hacc : ∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x) :
    ∀ x ∈ PLf.lowArms E elems sctx tw (PLfR.arms its),
      ∃ it ∈ its, x = (instPats2 E elems sctx it.1, it.2.pl.low E elems tw) ∧
        Expr2.listIdxFree x.1 = true ∧ Expr2.listUnsupportedFree x.1 = true ∧
        Expr2.listIdents x.1 = [] ∧ Expr2.listReads x.1 = [] ∧ RdOK σ it.2.rds x.2 := by
  intro x hx
  obtain ⟨it, hit, rfl⟩ := (mem_lowArms E elems sctx tw its x).1 hx
  have hok := harms it hit
  have haccA : ∀ y ∈ it.2.rds, AccOK σ DW DG EW ns y := fun y hy => hacc y (mem_armRds hit hy)
  obtain ⟨h1, h2, h3, h4⟩ := instPats2_simple E elems sctx it.1 hok.1
  exact ⟨it, hit, rfl, h1, h2, h3, h4, plfr_rdOK C it.2 hok.2 haccA tw⟩

/-- … and no arm value has an `index` node. -/
theorem arms_idx (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc}
    (sctx : Option Nat) (tw : Nat) (its : List (List PExpr × PLfR)) (harms : PLfR.ArmsOk ds tg its)
    (hacc : ∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x) :
    CasesIdxFree (PLf.lowArms E elems sctx tw (PLfR.arms its)) := by
  intro x hx
  obtain ⟨it, hit, rfl⟩ := (mem_lowArms E elems sctx tw its x).1 hx
  have hok := harms it hit
  have haccA : ∀ y ∈ it.2.rds, AccOK σ DW DG EW ns y := fun y hy => hacc y (mem_armRds hit hy)
  exact ⟨(instPats2_simple E elems sctx it.1 hok.1).1, plfr_idxFree C hdw it.2 hok.2 haccA tw⟩

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
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw
  | .ovr c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw => by
      refine ⟨?_, low_idxFree C hdw a ha (fun x hx => hacc x (by simp [PTR.rds, hx])) tw,
        low_idxFree C hdw b hb (fun x hx => hacc x (by simp [PTR.rds, hx])) tw⟩
      exact inst_idxFree C hdw c rc hc (fun x hx => hacc x (by simp [PTR.rds, hx])) none
  | .blk a, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.idxFree] using low_idxFree C hdw a hok hacc tw
  | .cases s rc its d, ⟨⟨hs, hg⟩, harms, hd⟩, hacc, tw => by
      have haccS : ∀ x ∈ rc, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccA : ∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x :=
        fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccD : ∀ x ∈ d.rds, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      exact ⟨fit_idxFree (signedCast_of_rds hs) (inst_idxFree C hdw s rc hs haccS) _,
        arms_idx C hdw _ tw its harms haccA, plfr_idxFree C hdw d hd haccD tw⟩

/-- Every expression of the tree is well formed for the design `d` whose widths are the summary's
(`hd`): no loud node, only declared names. -/
theorem low_wf (C : Ctx σ E elems DW DG EW ns) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) → ∀ tw,
      (ptr.pt.low E elems tw).wf d
  | .leafL t v rs, hok, hacc, tw => by
      have hr := rhs_ok C hok.2.1 hacc (fragOkL_co hok.2.2) (fragOkL_weq hok.2.2) tw
      refine (wfB_iff d _).2 ⟨hr.1, fun i hi => ?_⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.2 i hi)
      have := (hacc a (by simpa [PTR.rds] using ha)).1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      exact Design2.mem_names_of_declWidth (w := w) (by rw [hd]; exact hw)
  | .leafW n v rs, hok, hacc, tw => by
      have hr := rhs_ok C hok.2.1 hacc (fragOkL_co hok.2.2) (fragOkL_weq hok.2.2) tw
      refine (wfB_iff d _).2 ⟨hr.1, fun i hi => ?_⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.2 i hi)
      have := (hacc a (by simpa [PTR.rds] using ha)).1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      exact Design2.mem_names_of_declWidth (w := w) (by rw [hd]; exact hw)
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw
  | .ovr c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw => by
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
  | .cases s rc its dd, ⟨⟨hs, hg⟩, harms, hdd⟩, hacc, tw => by
      have haccS : ∀ x ∈ rc, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccA : ∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x :=
        fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccD : ∀ x ∈ dd.rds, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      refine ⟨wfB_of_rd σ hd (subj_rdOK C hs haccS _) haccS, ?_,
        wfB_of_rd σ hd (plfr_rdOK C dd hdd haccD tw) haccD⟩
      intro x hx
      obtain ⟨it, hit, rfl, -, h2, h3, -, h5⟩ := arms_facts C _ tw its harms haccA x hx
      have haccI : ∀ y ∈ it.2.rds, AccOK σ DW DG EW ns y := fun y hy => haccA y (mem_armRds hit hy)
      exact ⟨(listWfB_iff d _).2 ⟨h2, by simp [h3]⟩, wfB_of_rd σ hd h5 haccI⟩

/-- Every access of the site is a non-empty read window. -/
theorem acc_rd_pos {σ : String → Int} {DW : String → Option Nat}
    {DG : String → Option (List (Int × Int))} {EW : String → Option Nat} {ns : List String}
    {a : Acc} (h : AccOK σ DW DG EW ns a) : (a.rd σ).pos := by
  obtain ⟨-, hg, -⟩ := h
  cases a with
  | whole n => trivial
  | bit n x => simp [Acc.rd, ReadWin.pos]
  | cell1 n x => simp [Acc.rd, ReadWin.pos]
  | row n w r =>
      obtain ⟨m1, m2, -, h0, hw, -⟩ := hg
      simp only [Acc.rd, ReadWin.pos, Acc.wid]
      omega
  | cell2 n w r c => simp [Acc.rd, ReadWin.pos]
  | part1 n hi lo =>
      obtain ⟨m, -, h0, hlh, -⟩ := hg
      simp only [Acc.rd, ReadWin.pos, Acc.wid]
      omega
  | part2 n w r hi lo =>
      obtain ⟨m1, m2, -, hw, -, -, h0, hlh, -⟩ := hg
      simp only [Acc.rd, ReadWin.pos, Acc.wid]
      omega

/-- No read of the tree is near the window `W` (overlapping it or empty), given that no read ACCESS
overlaps it (the summary's `noSelfRead` obligation) and every access is in range. -/
theorem low_noRead (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {tg : Acc} (W : Win) :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) →
      (∀ a ∈ ptr.rds, (a.rd σ).overlaps W = false) → ∀ tw, (ptr.pt.low E elems tw).noRead W
  | .leafL t v rs, hok, hacc, hself, tw => by
      have hr := rhs_ok C hok.2.1 hacc (fragOkL_co hok.2.2) (fragOkL_weq hok.2.2) tw
      intro r hr'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.1 r hr')
      have hm : a ∈ (PTR.leafL t v rs).rds := by simpa [PTR.rds] using ha
      exact ⟨hself a hm, acc_rd_pos (hacc a hm)⟩
  | .leafW n v rs, hok, hacc, hself, tw => by
      have hr := rhs_ok C hok.2.1 hacc (fragOkL_co hok.2.2) (fragOkL_weq hok.2.2) tw
      intro r hr'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hr.2.1 r hr')
      have hm : a ∈ (PTR.leafW n v rs).rds := by simpa [PTR.rds] using ha
      exact ⟨hself a hm, acc_rd_pos (hacc a hm)⟩
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, hself, tw
  | .ovr c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, hself, tw => by
      refine ⟨?_, low_noRead C W a ha (fun x hx => hacc x (by simp [PTR.rds, hx]))
          (fun x hx => hself x (by simp [PTR.rds, hx])) tw,
        low_noRead C W b hb (fun x hx => hacc x (by simp [PTR.rds, hx]))
          (fun x hx => hself x (by simp [PTR.rds, hx])) tw⟩
      have hr := inst_rd C c rc hc (fun x hx => hacc x (by simp [PTR.rds, hx])) none
      intro r hr'
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp (hr.2.1 r hr')
      exact ⟨hself a' (by simp [PTR.rds, ha']), acc_rd_pos (hacc a' (by simp [PTR.rds, ha']))⟩
  | .blk a, hok, hacc, hself, tw => by
      simpa [PTR.pt, PT.low, PTree.noRead] using low_noRead C W a hok hacc hself tw
  | .cases s rc its dd, ⟨⟨hs, hg⟩, harms, hdd⟩, hacc, hself, tw => by
      have haccS : ∀ x ∈ rc, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccA : ∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x :=
        fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccD : ∀ x ∈ dd.rds, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      refine ⟨?_, ?_, ?_⟩
      · intro r hr
        obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ((subj_rdOK C hs haccS _).2.1 r hr)
        exact ⟨hself a' (by simp [PTR.rds, ha']), acc_rd_pos (hacc a' (by simp [PTR.rds, ha']))⟩
      · intro x hx
        obtain ⟨it, hit, rfl, -, -, -, h4, h5⟩ := arms_facts C _ tw its harms haccA x hx
        refine ⟨fun r hr => by simp [h4] at hr, fun r hr => ?_⟩
        obtain ⟨a', ha', rfl⟩ := List.mem_map.mp (h5.2.1 r hr)
        have hm : a' ∈ (PTR.cases s rc its dd).rds := by
          simp only [PTR.rds, List.mem_append]; exact Or.inl (Or.inr (mem_armRds hit ha'))
        exact ⟨hself a' hm, acc_rd_pos (hacc a' hm)⟩
      · intro r hr
        obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ((plfr_rdOK C dd hdd haccD tw).2.1 r hr)
        exact ⟨hself a' (by simp [PTR.rds, ha']), acc_rd_pos (hacc a' (by simp [PTR.rds, ha']))⟩

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
  | .ite _ _ a b, ⟨_, ha, hb⟩
  | .ovr _ _ a b, ⟨_, ha, hb⟩ => ⟨tree_tgt C hdw hatg a ha, tree_tgt C hdw hatg b hb⟩
  | .blk a, hok => tree_tgt C hdw hatg a hok
  | .cases _ _ its d, ⟨_, harms, hd⟩ => by
      refine ⟨fun x hx => ?_, plfr_tgt C hdw hatg d hd⟩
      obtain ⟨it, hit, rfl⟩ := mem_arms hx
      exact plfr_tgt C hdw hatg it.2 (harms it hit).2

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

/-- The refusal of an `always_comb` leaf whose right-hand side `fragOkL` does not accept. -/
def leafRefusal (v : PExpr) : String :=
  if v.scmpPairs.isEmpty then "right-hand side outside the v1 fragment (a gate tree, a concatenation or a fill)"
  else "a signed comparison in an `always_comb` leaf (the procedural route does not read signed comparisons yet; the fragment reads them in a continuous assign)"

/-- A select-target leaf `t = v;`. -/
def leafL? (ds : List DeclT) (t : PLhs) (v : PExpr) : Except String (Acc × PTR) :=
  match tgtOf? ds t with
  | .error e => .error e
  | .ok tg =>
      match rhsRds? ds v with
      | .error e => .error e
      | .ok rs =>
          if fragOkL v then .ok (tg, .leafL t v rs)
          else .error (leafRefusal v)

/-- A whole-signal leaf `n = v;`. -/
def leafW? (ds : List DeclT) (n : String) (v : PExpr) : Except String (Acc × PTR) :=
  match tgtOf? ds (.ident n) with
  | .error e => .error e
  | .ok tg =>
      match rhsRds? ds v with
      | .error e => .error e
      | .ok rs =>
          if fragOkL v then .ok (tg, .leafW n v rs)
          else .error (leafRefusal v)

/-- A `case` arm: one assignment `t = v;` or `n = v;` of the target (WP-G S3a). -/
def armLeaf? (ds : List DeclT) : PStmt → Except String (Acc × PLfR)
  | .blockingAssignL t v =>
      match tgtOf? ds t with
      | .error e => .error e
      | .ok tg =>
          match rhsRds? ds v with
          | .error e => .error e
          | .ok rs =>
              if fragOkL v then .ok (tg, .leafL t v rs)
              else .error (leafRefusal v)
  | .blockingAssign n v =>
      match tgtOf? ds (.ident n) with
      | .error e => .error e
      | .ok tg =>
          match rhsRds? ds v with
          | .error e => .error e
          | .ok rs =>
              if fragOkL v then .ok (tg, .leafW n v rs)
              else .error (leafRefusal v)
  | .nbaAssign .. | .nbaAssignL .. =>
      .error "nonblocking assignment in always_comb (outside the v1 fragment)"
  | .ifStmt .. | .block .. | .caseStmt .. | .unsupported .. | .forLoop .. =>
      .error "`case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)"

/-- A literal pattern. -/
def isLitP : PExpr → Bool
  | .lit _ => true
  | _ => false

theorem isLitP_spec {p : PExpr} (h : isLitP p = true) : ∃ v, p = PExpr.lit v := by
  cases p <;> simp_all [isLitP]

/-- Every pattern of an item is a sized literal. -/
def casePats? (ps : List PExpr) : Except String Unit :=
  if ps.all isLitP then .ok ()
  else .error "`case` item is not a sized literal (write `8'd5`: an unsized or computed item is outside the v1 fragment)"

theorem casePats?_spec {ps : List PExpr} (h : casePats? ps = .ok ()) : ∀ p ∈ ps, ∃ v, p = PExpr.lit v := by
  unfold casePats? at h
  split at h
  · rename_i hall
    intro p hp
    exact isLitP_spec (List.all_eq_true.mp hall p hp)
  · simp at h

/-- The arms of a `case`, every arm assigning the access `tg`. -/
def caseArms? (ds : List DeclT) (tg : Acc) :
    List (List PExpr × PStmt) → Except String (List (List PExpr × PLfR))
  | [] => .ok []
  | (ps, body) :: rest =>
      match casePats? ps with
      | .error e => .error e
      | .ok _ =>
          match armLeaf? ds body with
          | .error e => .error e
          | .ok (t, a) =>
              if t = tg then
                match caseArms? ds tg rest with
                | .error e => .error e
                | .ok r => .ok ((ps, a) :: r)
              else .error "always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)"

/-- **A plain `case` with a `default` whose arms are single assignments** (WP-G S3a). -/
def caseTree? (ds : List DeclT) (subj : PExpr) (items : List (List PExpr × PStmt)) (dflt : PStmt) :
    Except String (Acc × PTR) :=
  match rdsOf? ds subj with
  | .error e => .error e
  | .ok rc =>
      if fragG subj then
        match armLeaf? ds dflt with
        | .error e => .error e
        | .ok (tg, d) =>
            match caseArms? ds tg items with
            | .error e => .error e
            | .ok its => .ok (tg, .cases subj rc its d)
      else .error "`case` subject outside the v1 fragment (an expression of accesses and literals built from `& | ^`, `~ !`, reductions, `&& ||`, `== !=` and `?:`)"

/-- The `case` statement: plain, with a `default`. -/
def caseStmt? (ds : List DeclT) (subj : PExpr) (items : List (List PExpr × PStmt))
    (dflt : Option PStmt) (mode : CaseMode) (check : CaseCheck) : Except String (Acc × PTR) :=
  if !mode.isNormal then .error "always_comb statement `case … inside` (outside the first fragment)"
  else
    match check with
    | .none =>
        match dflt with
        | some d => caseTree? ds subj items d
        | none => .error "always_comb `case` has no `default`: it does not assign its target on every path (a latch)"
    | _ => .error "always_comb statement `unique`/`priority case` (outside the first fragment)"

theorem armLeaf?_spec (ds : List DeclT) :
    ∀ (body : PStmt) (tg : Acc) (a : PLfR), armLeaf? ds body = .ok (tg, a) →
      a.pl.toPStmt = body ∧ a.Ok ds tg
  | .blockingAssignL t v, tg, a, h => by
      simp only [armLeaf?] at h
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
  | .blockingAssign n v, tg, a, h => by
      simp only [armLeaf?] at h
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
  | .nbaAssign .., tg, a, h => by simp [armLeaf?] at h
  | .nbaAssignL .., tg, a, h => by simp [armLeaf?] at h
  | .ifStmt .., tg, a, h => by simp [armLeaf?] at h
  | .block .., tg, a, h => by simp [armLeaf?] at h
  | .caseStmt .., tg, a, h => by simp [armLeaf?] at h
  | .forLoop .., tg, a, h => by simp [armLeaf?] at h
  | .unsupported .., tg, a, h => by simp [armLeaf?] at h

theorem caseArms?_spec (ds : List DeclT) (tg : Acc) :
    ∀ (items : List (List PExpr × PStmt)) (its : List (List PExpr × PLfR)),
      caseArms? ds tg items = .ok its → PLf.items (PLfR.arms its) = items ∧ PLfR.ArmsOk ds tg its
  | [], its, h => by
      simp only [caseArms?, Except.ok.injEq] at h
      subst h
      simp [PLfR.arms, PLf.items, PLfR.ArmsOk]
  | (ps, body) :: rest, its, h => by
      unfold caseArms? at h
      split at h
      · simp at h
      · rename_i u hp
        split at h
        · simp at h
        · rename_i t a ha
          split at h
          · rename_i ht
            split at h
            · simp at h
            · rename_i r hr
              simp only [Except.ok.injEq] at h
              subst h
              obtain ⟨e1, o1⟩ := armLeaf?_spec ds body t a ha
              obtain ⟨e2, o2⟩ := caseArms?_spec ds tg rest r hr
              subst ht
              refine ⟨by simp [PLfR.arms, PLf.items, e1, e2], ?_⟩
              intro it hit
              rcases List.mem_cons.mp hit with rfl | hit
              · exact ⟨casePats?_spec hp, o1⟩
              · exact o2 it hit
          · simp at h

theorem caseTree?_spec (ds : List DeclT) (subj : PExpr) (items : List (List PExpr × PStmt))
    (dflt : PStmt) (tg : Acc) (ptr : PTR) (h : caseTree? ds subj items dflt = .ok (tg, ptr)) :
    ptr.pt.toPStmt = .caseStmt subj items (some dflt) .normal .none ∧ ptr.Ok ds tg := by
  unfold caseTree? at h
  split at h
  · simp at h
  · rename_i rc hrc
    split at h
    · rename_i hg
      split at h
      · simp at h
      · rename_i tg' d hd
        split at h
        · simp at h
        · rename_i its hits
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨e1, o1⟩ := armLeaf?_spec ds dflt tg' d hd
          obtain ⟨e2, o2⟩ := caseArms?_spec ds tg' items its hits
          exact ⟨by simp [PTR.pt, PT.toPStmt, e1, e2], ⟨hrc, hg⟩, o2, o1⟩
    · simp at h

theorem caseStmt?_spec (ds : List DeclT) (subj : PExpr) (items : List (List PExpr × PStmt))
    (dflt : Option PStmt) (mode : CaseMode) (check : CaseCheck) (tg : Acc) (ptr : PTR)
    (h : caseStmt? ds subj items dflt mode check = .ok (tg, ptr)) :
    ptr.pt.toPStmt = .caseStmt subj items dflt mode check ∧ ptr.Ok ds tg := by
  unfold caseStmt? at h
  cases mode with
  | normal =>
      cases check
      · cases dflt
        · simp [CaseMode.isNormal] at h
        · exact caseTree?_spec ds subj items _ tg ptr h
      all_goals simp [CaseMode.isNormal] at h
  | inside | casez | casex => simp [CaseMode.isNormal] at h

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
  | .caseStmt subj items dflt mode check => caseStmt? ds subj items dflt mode check
  | .unsupported k _ => .error s!"always_comb statement `{k}` (unsupported)"
  | .forLoop .. => .error "always_comb statement `for` loop (a parameter-dependent loop: outside the supported fragment)"
termination_by structural s => s

/-- A block: one statement (a tree), or a tree followed by overrides `if (c) tree;` of the same target
(WP-G S3b: the last write wins). -/
def treeStmts? (ds : List DeclT) : List PStmt → Except String (Acc × PTR)
  | [] => .error "empty always_comb block"
  | [s] =>
      match treeStmt? ds s with
      | .error e => .error e
      | .ok (t, a) => .ok (t, .blk a)
  | s :: s2 :: rest =>
      match treeStmt? ds s with
      | .error e => .error e
      | .ok (t, b) =>
          if b.pt.isOvr then
            .error "a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)"
          else
            match ovrFold? ds t b (s2 :: rest) with
            | .error e => .error e
            | .ok p => .ok (t, p)
termination_by structural ss => ss

/-- One statement after the first of a block: an override `if (c) tree;` of the target `tg` (no `else`). -/
def ovrStmt? (ds : List DeclT) (tg : Acc) (base : PTR) : PStmt → Except String PTR
  | .ifStmt c th none =>
      match rdsOf? ds c with
      | .error e => .error e
      | .ok rc =>
          if fragG c then
            match treeStmt? ds th with
            | .error e => .error e
            | .ok (t1, a) =>
                if t1 = tg then .ok (.ovr c rc a base)
                else .error "always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)"
          else .error "`if` condition outside the v1 fragment (a one-bit expression of accesses and literals built from `& | ^`, `~ !`, reductions, `&& ||`, `== !=` and `?:`)"
  | .ifStmt _ _ (some _) =>
      .error "an `if … else` after the first statement of an always_comb block (outside the second fragment: only `if (c) …;` without `else` can follow, as a default-then-override body)"
  | .blockingAssignL t _ =>
      match tgtOf? ds t with
      | .error e => .error e
      | .ok t1 =>
          if t1 = tg then
            .error "a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)"
          else .error "always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)"
  | .blockingAssign n _ =>
      match tgtOf? ds (.ident n) with
      | .error e => .error e
      | .ok t1 =>
          if t1 = tg then
            .error "a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)"
          else .error "always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)"
  | .nbaAssign .. | .nbaAssignL .. =>
      .error "nonblocking assignment in always_comb (outside the v1 fragment)"
  | _ =>
      .error "after its first statement an always_comb block may only hold `if (c) …;` overrides of the same target (outside the second fragment)"
termination_by structural s => s

/-- The overrides of a block, in order, onto the statements read so far. -/
def ovrFold? (ds : List DeclT) (tg : Acc) (base : PTR) : List PStmt → Except String PTR
  | [] => .ok base
  | s :: rest =>
      match ovrStmt? ds tg base s with
      | .error e => .error e
      | .ok p => ovrFold? ds tg p rest
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
  | .caseStmt subj items dflt mode check, tg, ptr, h => by
      unfold treeStmt? at h
      exact caseStmt?_spec ds subj items dflt mode check tg ptr h
  | .forLoop .., tg, ptr, h => by simp [treeStmt?] at h
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
  | s :: s2 :: rest, tg, ptr, h => by
      unfold treeStmts? at h
      split at h
      · simp at h
      · rename_i t b h1
        split at h
        · simp at h
        · rename_i hno
          split at h
          · simp at h
          · rename_i p hp
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨e1, o1⟩ := treeStmt?_spec ds s t b h1
            obtain ⟨e2, e3, o2⟩ := ovrFold?_spec ds (s2 :: rest) t b p hp
            have hb : b.pt.stmtsP = [s] := by
              unfold PT.stmtsP
              rw [if_neg hno, e1]
            rw [hb] at e2
            have hov := e3 (by simp)
            refine ⟨?_, o2 o1⟩
            cases hp' : p.pt with
            | ovr c a b' =>
                rw [hp'] at e2
                simpa [PT.stmtsP, PT.isOvr, PT.toPStmt, PStmt.unblock] using e2
            | _ => rw [hp'] at hov; simp [PT.isOvr] at hov
termination_by structural ss => ss

theorem ovrStmt?_spec (ds : List DeclT) : ∀ (s : PStmt) (tg : Acc) (base p : PTR),
    ovrStmt? ds tg base s = .ok p →
      p.pt.stmtsP = base.pt.stmtsP ++ [s] ∧ p.pt.isOvr = true ∧
        (base.Ok ds tg → p.Ok ds tg)
  | .ifStmt c th none, tg, base, p, h => by
      unfold ovrStmt? at h
      split at h
      · simp at h
      · rename_i rc hrc
        split at h
        · rename_i hg
          split at h
          · simp at h
          · rename_i t1 a h1
            split at h
            · rename_i heq
              simp only [Except.ok.injEq] at h
              subst h
              obtain ⟨e1, o1⟩ := treeStmt?_spec ds th t1 a h1
              subst heq
              refine ⟨?_, rfl, fun hb => ⟨⟨hrc, hg⟩, o1, hb⟩⟩
              simp [PT.stmtsP, PT.isOvr, PT.toPStmt, PTR.pt, PStmt.unblock, e1]
            · simp at h
        · simp at h
  | .ifStmt _ _ (some _), tg, base, p, h => by simp [ovrStmt?] at h
  | .blockingAssignL t v, tg, base, p, h => by
      unfold ovrStmt? at h
      split at h
      · simp at h
      · split at h <;> simp at h
  | .blockingAssign n v, tg, base, p, h => by
      unfold ovrStmt? at h
      split at h
      · simp at h
      · split at h <;> simp at h
  | .nbaAssign .., tg, base, p, h => by simp [ovrStmt?] at h
  | .nbaAssignL .., tg, base, p, h => by simp [ovrStmt?] at h
  | .block .., tg, base, p, h => by simp [ovrStmt?] at h
  | .caseStmt .., tg, base, p, h => by simp [ovrStmt?] at h
  | .forLoop .., tg, base, p, h => by simp [ovrStmt?] at h
  | .unsupported .., tg, base, p, h => by simp [ovrStmt?] at h
termination_by structural s => s

theorem ovrFold?_spec (ds : List DeclT) : ∀ (rest : List PStmt) (tg : Acc) (base p : PTR),
    ovrFold? ds tg base rest = .ok p →
      p.pt.stmtsP = base.pt.stmtsP ++ rest ∧ (rest ≠ [] → p.pt.isOvr = true) ∧
        (base.Ok ds tg → p.Ok ds tg)
  | [], tg, base, p, h => by
      simp only [ovrFold?, Except.ok.injEq] at h
      subst h
      exact ⟨by simp, by simp, id⟩
  | s :: rest, tg, base, p, h => by
      unfold ovrFold? at h
      split at h
      · simp at h
      · rename_i q hq
        obtain ⟨e1, e2, o1⟩ := ovrStmt?_spec ds s tg base q hq
        obtain ⟨f1, f2, o2⟩ := ovrFold?_spec ds rest tg q p h
        refine ⟨by rw [f1, e1]; simp, fun _ => ?_, fun hb => o2 (o1 hb)⟩
        cases rest with
        | nil =>
            simp only [ovrFold?, Except.ok.injEq] at h
            subst h
            exact e2
        | cons r rs => exact f2 (by simp)
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

/-- The declarations of the design: `a`, `b`, `p`, `s` are `[N-1:0]`, `c` is `[N:0]`, as `PDesign.summary` reads them.
All seven are unsigned `logic` in `add_proc.sv` (variables, not nets), so `isNet` and `isSigned` are `false` in each. -/
def apDecls : List DeclT :=
  let nm1 : Aff := ⟨[("N", 1)], -1⟩
  let dm1 : PDim := ⟨.binary (.m0 .sub) (.paramRef "N" none) (.int 1), .int 0⟩
  [⟨"a", true, false, false, false, [(dm1, nm1, Aff.const 0)]⟩, ⟨"b", true, false, false, false, [(dm1, nm1, Aff.const 0)]⟩,
   ⟨"cin", true, false, false, false, []⟩, ⟨"s", false, true, false, false, [(dm1, nm1, Aff.const 0)]⟩,
   ⟨"cout", false, true, false, false, []⟩,
   ⟨"c", false, false, false, false, [(⟨.paramRef "N" none, .int 0⟩, ⟨[("N", 1)], 0⟩, Aff.const 0)]⟩,
   ⟨"p", false, false, false, false, [(dm1, nm1, Aff.const 0)]⟩]

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
  "a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)"
-- WP-G S3b: default-then-override is accepted, and so is an override with a tree branch
#guard refusal (.alwaysComb (.block [.blockingAssignL carryLhs aa, .ifStmt pp (.blockingAssignL carryLhs cc) none])) ==
  "accepted"
#guard refusal (.alwaysComb (.block [.blockingAssignL carryLhs aa, .ifStmt pp (.blockingAssignL carryLhs cc) none,
    .ifStmt aa (.block [.blockingAssignL carryLhs cc, .ifStmt pp (.blockingAssignL carryLhs aa) none]) none])) ==
  "accepted"
#guard refusal (.alwaysComb (.block [.blockingAssignL carryLhs aa,
    .blockingAssignL (.bitSel "s" (.genvarRef "i")) cc])) ==
  "always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)"
#guard refusal (.alwaysComb (.block [.blockingAssignL carryLhs aa,
    .ifStmt pp (.blockingAssignL (.bitSel "s" (.genvarRef "i")) cc) none])) ==
  "always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)"
#guard refusal (.alwaysComb (.block [.blockingAssignL carryLhs aa,
    .ifStmt pp (.blockingAssignL carryLhs cc) (some (.blockingAssignL carryLhs aa))])) ==
  "an `if … else` after the first statement of an always_comb block (outside the second fragment: only `if (c) …;` without `else` can follow, as a default-then-override body)"
#guard refusal (.alwaysComb (.block [.block [.blockingAssignL carryLhs aa, .ifStmt pp (.blockingAssignL carryLhs cc) none],
    .ifStmt pp (.blockingAssignL carryLhs cc) none])) ==
  "a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)"
#guard refusal (.alwaysComb (.block [.caseStmt pp [] none .normal .none])) ==
  "always_comb `case` has no `default`: it does not assign its target on every path (a latch)"
#guard refusal (.alwaysComb (.block [.caseStmt pp [] (some (.blockingAssignL carryLhs cc)) .inside .none])) ==
  "always_comb statement `case … inside` (outside the first fragment)"
#guard refusal (.alwaysComb (.block [.caseStmt pp [([.int 1], .blockingAssignL carryLhs cc)]
    (some (.blockingAssignL carryLhs aa)) .normal .none])) ==
  "`case` item is not a sized literal (write `8'd5`: an unsized or computed item is outside the v1 fragment)"
#guard refusal (.alwaysComb (.block [.caseStmt pp [([.lit (LVec.ofNat 1 0)], .block [.blockingAssignL carryLhs cc])]
    (some (.blockingAssignL carryLhs aa)) .normal .none])) ==
  "`case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)"
-- a plain `case` with a `default` and single-assignment arms is accepted (WP-G S3a)
#guard refusal (.alwaysComb (.block [.caseStmt pp [([.lit (LVec.ofNat 1 0)], .blockingAssignL carryLhs cc),
    ([.lit (LVec.ofNat 1 1)], .blockingAssignL carryLhs aa)]
    (some (.blockingAssignL carryLhs aa)) .normal .none])) == "accepted"
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
      (by intro n hn; simp [Aff.names] at hn; subst hn; simp [IEnv.intVal?, hi])).2
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
  · simp [PTree.noRead, Expr2.reads, Expr2.sliceReads, ReadWin.apart, ReadWin.pos, ReadWin.overlaps,
      Win.overlaps]


/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombProc.instStmt2_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instStmt2_tree

/-- info: 'LeanModels.Sv.CombProc.instProcess2_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instProcess2_tree

/-- info: 'LeanModels.Sv.CombProc.inst_leaf_idxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_leaf_idxFree

/-- info: 'LeanModels.Sv.CombProc.inst_rdsLeaf_idxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_rdsLeaf_idxFree

/-- info: 'LeanModels.Sv.CombProc.inst_parts_idxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_parts_idxFree

/-- info: 'LeanModels.Sv.CombProc.inst_idxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'LeanModels.Sv.CombProc.tree_tgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_tgt

/-- info: 'LeanModels.Sv.CombProc.lower_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_site

/-- info: 'LeanModels.Sv.CombProc.treeStmt?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStmt?_spec

/-- info: 'LeanModels.Sv.CombProc.treeStmts?_spec' depends on axioms: [propext, Quot.sound] -/
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
