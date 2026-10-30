import LeanModels.Sv.CombViewThm
import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.CombGuard2Sound
import LeanModels.Sv.CombKnownBits

/-!
# `always_comb` bodies in the `sv_comb` fragment, stage 1: the generic statement lemmas (WP-G, G2.1)

The combinational settle theorem (`Comb2Base` .. `Comb2`) and the knownness theorem (`CombKnownThm`) are stated
for designs whose processes are all continuous assigns. `Comb2Proc.lean` extends them to `always_comb` by the
LOWERING `Design2.lowerComb`: a body in its profile is run symbolically (`Stmt2.symExec`) and replaced by ONE
continuous assign `assign {w₀, …} = {E₀, …}` (`SymState.toAssign`); `Runs2.lowerComb_iff` and
`Models2.of_combProc*` transfer everything proved about the lowered design back. This file proves, for the
first fragment (S1 below), the facts a TACTIC needs to know about that lowering at a SYMBOLIC parameter, with
no window arithmetic: windows are abstract `(n, lo, w)` triples and every comparison between two windows is a
hypothesis, discharged one level up (`CombProc.lean`, from the summary's obligations, by `omega`).

## The fragment S1 (single window)

A body `begin T end` where `T` is a tree (`PTree`): a leaf `target = e;` or `if (c) T₁ else T₂` (an `else if`
is an `else` holding an `if`). Every leaf assigns the SAME target `tgt` (a whole signal or a constant slice,
whose window is `W`), so every path assigns the window (no latch). What the lowering needs of the tree:

| fact | hypothesis | theorem |
|---|---|---|
| the symbolic execution is the single equation `W = low T` | every expression `wfB` (no loud node, only declared names), `tgt.symWin d = some W` | `symExec_tree` |
| the equation reads no window it writes (`selfReadFree`) | `PTree.noRead W`: no read window of any expression overlaps `W` | `selfReadFree_tree` |
| the self-read guard of `CombGuard2` admits the body, so `combGuardProc` is the identity | `PTree.noRdW`: every read window meets `W` in zero bits (derived from `noRead` and `idxFree`: `noRdW_of_noRead`) | `combAdmits_tree` |
| the driven windows are the target's (the one-driver rule of `Hier2.driversOk`) | none | `drvWins_tree` |
| the lowered process | all of the above | `lower_tree'` |
| the Boolean value of the equation: `if c then a else b` at every level | every leaf `w` bits wide, every condition 1 bit, in the x-free fragment | `low_xfWidth`, `low_xfBits` |

`PTree.low` is `Expr2.joinIte (Expr2.ifGuard c) A B`: the `if` becomes a `?:` on the KNOWN guard `(|c) === 1'b1`,
which is why a condition that is `x` or `z` takes the ELSE branch (the `if` rule), unlike the conditional
expression `c ? a : b`, which merges (docs: `svgolf/design/always-comb/README.md`, section 1). The Boolean
equation `low_xfBits` is claimed only where `CombKnown.settled` applies, i.e. for known reads.

## Soundness story

Nothing here is trusted: every theorem is kernel-checked plain Lean; the only inputs are the definitions of
`Comb2Proc.lean` and `CombGuard2.lean`, which are unchanged. No axiom is added (`#print axioms` pins at the end:
`propext`, `Classical.choice`, `Quot.sound` at most). The self-read guard (`CombGuard2`) and `lowerComb` are
DIFFERENT checks (neither implies the other, see `Comb2Proc.lean`'s docstring); the fragment satisfies both,
`combAdmits_tree` and `selfReadFree_tree`.
-/

namespace LeanModels.Sv

mutual
/-- No dynamic or literal element select (`index` node): after instantiation every CONSTANT select is a slice. -/
def Expr2.idxFree : Expr2 → Bool
  | .index .. => false
  | .lit _ | .ident _ | .unsupported _ _ => true
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => a.idxFree
  | .binary _ l r | .scmp _ l r | .logical _ l r => l.idxFree && r.idxFree
  | .ternary c t f => c.idxFree && t.idxFree && f.idxFree
  | .concat parts => Expr2.listIdxFree parts.toList
termination_by structural e => e

def Expr2.listIdxFree : List Expr2 → Bool
  | [] => true
  | e :: es => e.idxFree && Expr2.listIdxFree es
termination_by structural es => es
end

namespace CombProc
open CombGuard

/-! A tree of `if/else` over leaf right-hand sides, all assigning ONE target `tgt` (a whole signal or a
constant slice; its window is `W`): the S1 body shape. `blk` is a `begin t end` around one tree (the body of
the process, and the arms of an `if` written with `begin ... end`). -/
inductive PTree where
  | leaf (e : Expr2)
  | ite (c : Expr2) (a b : PTree)
  | blk (t : PTree)

/-- The statement a tree stands for. -/
def PTree.toStmt (tgt : Lhs2) : PTree → Stmt2
  | .leaf e => .blockingAssign tgt e
  | .ite c a b => .ifStmt c (a.toStmt tgt) (some (b.toStmt tgt))
  | .blk t => .block #[t.toStmt tgt]

/-- The lowered right-hand side of the window. -/
def PTree.low (w : Nat) : PTree → Expr2
  | .leaf e => .resize w e
  | .ite c a b => Expr2.joinIte (Expr2.ifGuard c) (a.low w) (b.low w)
  | .blk t => t.low w

/-- Well-formedness of every expression of the tree. -/
def PTree.wf (d : Design2) : PTree → Prop
  | .leaf e => e.wfB d = true
  | .ite c a b => c.wfB d = true ∧ a.wf d ∧ b.wf d
  | .blk t => t.wf d

/-! ## Helper: substitution into the empty symbolic state is the identity -/

theorem wfB_iff (d : Design2) (e : Expr2) :
    e.wfB d = true ↔ e.unsupportedFree = true ∧ ∀ x ∈ e.idents, x ∈ d.symNames := by
  simp [Expr2.wfB, List.all_eq_true]

theorem listWfB_iff (d : Design2) (l : List Expr2) :
    Expr2.listWfB d l = true ↔ Expr2.listUnsupportedFree l = true ∧ ∀ x ∈ Expr2.listIdents l, x ∈ d.symNames := by
  simp [Expr2.listWfB, List.all_eq_true]

theorem symSubst_nil_aux (d : Design2) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.wfB d = true → e.symSubst d [] = some e) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → Expr2.listWfB d l = true →
      Expr2.listSymSubst d [] l = some l) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h => by omega, fun l h => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he hw => ?_, fun l hl hw => ?_⟩
    · rw [wfB_iff] at hw
      obtain ⟨hu, hi⟩ := hw
      have sub : ∀ a : Expr2, a.size < n → a.unsupportedFree = true → (∀ x ∈ a.idents, x ∈ d.symNames) →
          a.symSubst d [] = some a := fun a ha hu hi => ihe a ha ((wfB_iff d a).2 ⟨hu, hi⟩)
      cases e with
      | lit v => simp [Expr2.symSubst]
      | ident m =>
          have : m ∈ d.symNames := hi m (by simp [Expr2.idents])
          simp [Expr2.symSubst, this, SymState.readWhole, SymState.writesName]
      | unsupported k t => simp [Expr2.unsupportedFree] at hu
      | unary op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | resizeSigned w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | squash2 a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | repl k a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | reduce op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | resize w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | binary op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | scmp op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | logical b l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | index a i w =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub a (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub i (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | ternary c t f =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub c (by omega) hu.1.1 (fun x hx => hi x (Or.inl (Or.inl hx))),
            sub t (by omega) hu.1.2 (fun x hx => hi x (Or.inl (Or.inr hx))),
            sub f (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | slice a lo w =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idents] at hi
          by_cases hid : ∃ m, a = .ident m
          · obtain ⟨m, rfl⟩ := hid
            have : m ∈ d.symNames := hi m (by simp [Expr2.idents])
            simp [Expr2.symSubst, Expr2.sliceSubst, this, SymState.readWin, SymState.findCover,
              SymState.overlapsAny]
          · have hs : ∀ r, Expr2.sliceSubst d [] a lo w r = r.map fun b => Expr2.slice b lo w := by
              intro r; cases a <;> simp_all [Expr2.sliceSubst]
            have ih := sub a (by omega) hu hi
            simp [Expr2.symSubst, hs, ih]
      | concat parts =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idents] at hi
          have := ihl parts.toList (by omega) ((listWfB_iff d _).2 ⟨hu, hi⟩)
          simp [Expr2.symSubst, this]
    · cases l with
      | nil => simp [Expr2.listSymSubst]
      | cons e es =>
          rw [listWfB_iff] at hw
          obtain ⟨hu, hi⟩ := hw
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listUnsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.listIdents, List.mem_append] at hi
          have h1 := ihe e (by omega) ((wfB_iff d e).2 ⟨hu.1, fun x hx => hi x (Or.inl hx)⟩)
          have h2 := ihl es (by omega) ((listWfB_iff d es).2 ⟨hu.2, fun x hx => hi x (Or.inr hx)⟩)
          simp [Expr2.listSymSubst, h1, h2]

theorem symSubst_nil (d : Design2) (e : Expr2) (h : e.wfB d = true) : e.symSubst d [] = some e :=
  (symSubst_nil_aux d (e.size + 1)).1 e (Nat.lt_succ_self _) h



/-! ## A1: the symbolic execution -/

theorem symExec_tree (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W) :
    ∀ t : PTree, t.wf d → (t.toStmt tgt).symExec d [] = some [(W, t.low W.2.2)] := by
  intro t
  induction t with
  | leaf e =>
      intro (h1 : e.wfB d = true)
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, h1, symSubst_nil d e h1, hsw, SymState.write,
        SymState.findCover, SymState.overlapsAny]
  | ite c a b iha ihb =>
      intro ⟨h1, ha, hb⟩
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecOpt, h1, symSubst_nil d c h1, iha ha, ihb hb,
        SymState.join, SymState.joinWins, Win.allDisjoint, SymState.lookupOr, SymState.findWin]
  | blk t iht =>
      intro (ht : t.wf d)
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecList, iht ht]


/-! ## A2: no self-read of the lowered equation -/

/-- No read of any expression of the tree overlaps the window. -/
def PTree.noRead (W : Win) : PTree → Prop
  | .leaf e => ∀ r ∈ e.reads, r.overlaps W = false
  | .ite c a b => (∀ r ∈ c.reads, r.overlaps W = false) ∧ a.noRead W ∧ b.noRead W
  | .blk t => t.noRead W

theorem low_reads (W : Win) (w : Nat) :
    ∀ t : PTree, t.noRead W → ∀ r ∈ (t.low w).reads, r.overlaps W = false := by
  intro t
  induction t with
  | leaf e => intro h r hr; exact h r (by simpa [PTree.low, Expr2.reads] using hr)
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ r hr
      simp only [PTree.low, Expr2.joinIte] at hr
      split at hr
      · exact iha ha r hr
      · simp only [Expr2.reads, Expr2.ifGuard, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with (hr | hr) | hr
        · exact hc r hr
        · exact iha ha r hr
        · exact ihb hb r hr
  | blk t iht => intro h r hr; exact iht h r (by simpa [PTree.low] using hr)

theorem selfReadFree_tree (W : Win) (w : Nat) (t : PTree) (h : t.noRead W) :
    SymState.selfReadFree [(W, t.low w)] = true := by
  simp only [SymState.selfReadFree, List.map_cons, List.map_nil, Expr2.listReads, List.append_nil,
    List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true, Bool.not_eq_true']
  exact fun r hr => low_reads W w t h r hr

/-! ## A4: the driven windows -/

theorem drvWins_tree (tgt : Lhs2) :
    ∀ t : PTree, ∀ x ∈ (t.toStmt tgt).drvWins, x ∈ tgt.drvWins := by
  intro t
  induction t with
  | leaf e => intro x hx; simpa [PTree.toStmt, Stmt2.drvWins] using hx
  | ite c a b iha ihb =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.drvWins, Stmt2.drvWinsOpt, List.mem_append] at hx
      rcases hx with hx | hx
      · exact iha x hx
      · exact ihb x hx
  | blk t iht =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.drvWins, Stmt2.drvWinsList, List.append_nil] at hx
      exact iht x hx

/-! ## A3: the self-read guard admits the body -/

/-- Every read window of every expression of the tree meets the window in zero bits. -/
def PTree.noRdW (wd : String → Option Nat) (W : BWin) : PTree → Prop
  | .leaf e => ∀ r ∈ e.rdW wd, (BWin.inter r W).2.2 = 0
  | .ite c a b => (∀ r ∈ c.rdW wd, (BWin.inter r W).2.2 = 0) ∧ a.noRdW wd W ∧ b.noRdW wd W
  | .blk t => t.noRdW wd W

theorem BWin.subAll_nil_of_zero (a : BWin) (h : a.2.2 = 0) : ∀ M : List BWin, BWin.subAll a M = [] := by
  intro M
  induction M generalizing a with
  | nil => simp [BWin.subAll, h]
  | cons b bs ih =>
      simp only [BWin.subAll, BWin.sub]
      split
      · -- same signal
        have h1 : ¬ a.2.1 < min (a.2.1 + a.2.2) b.2.1 := by omega
        have h2 : ¬ max a.2.1 (b.2.1 + b.2.2) < a.2.1 + a.2.2 := by omega
        simp [h1, h2]
      · simp

theorem readsViol_none (M A R : List BWin) (W : BWin) (hA : ∀ x ∈ A, x = W)
    (hR : ∀ r ∈ R, (BWin.inter r W).2.2 = 0) : readsViol M A R = none := by
  unfold readsViol
  rw [List.findSome?_eq_none_iff]
  intro r hr
  rw [List.findSome?_eq_none_iff]
  intro x hx
  have := hA x hx
  subst this
  rw [BWin.subAll_nil_of_zero _ (hR r hr)]
  rfl

theorem mayW_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W]) :
    ∀ t : PTree, ∀ x ∈ (t.toStmt tgt).mayW wd, x = W := by
  intro t
  induction t with
  | leaf e => intro x hx; simpa [PTree.toStmt, Stmt2.mayW, hm] using hx
  | ite c a b iha ihb =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.mayW, Stmt2.optMayW, List.mem_append] at hx
      rcases hx with hx | hx
      · exact iha x hx
      · exact ihb x hx
  | blk t iht =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.mayW, Stmt2.listMayW, List.append_nil] at hx
      exact iht x hx

theorem combViol_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) :
    ∀ t : PTree, t.noRdW wd W → ∀ (M A : List BWin), (∀ x ∈ A, x = W) →
      (t.toStmt tgt).combViol wd M A = none := by
  intro t
  induction t with
  | leaf e =>
      intro h M A hA
      simp only [PTree.toStmt, Stmt2.combViol, hm, hr, List.append_nil]
      apply readsViol_none M _ _ W
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with rfl | hx
        · rfl
        · exact hA x hx
      · exact h
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ M A hA
      simp only [PTree.toStmt, Stmt2.combViol, Stmt2.optCombViol]
      rw [readsViol_none M _ _ W _ hc, iha ha M A hA, ihb hb M A hA]
      · rfl
      · intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact mayW_tree wd tgt W hm a x hx
        · exact mayW_tree wd tgt W hm b x (by simpa [PTree.toStmt, Stmt2.optMayW] using hx)
        · exact hA x hx
  | blk t iht =>
      intro h M A hA
      have h0 := iht h M A hA
      simp only [PTree.toStmt, Stmt2.combViol, Stmt2.listCombViol, Stmt2.listMayW, List.nil_append]
      rw [h0]
      rfl

theorem combAdmits_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) (t : PTree) (h : t.noRdW wd W) :
    (t.toStmt tgt).combAdmits wd = true := by
  unfold Stmt2.combAdmits
  rw [combViol_tree wd tgt W hm hr t h [] [] (by simp)]
  rfl


/-! ## The Boolean semantics of the lowered equation (the netlist-view shape) -/

/-- The Boolean semantics of the tree. -/
def PTree.bit (d : Design2) (env : String → Nat → Bool) : PTree → Nat → Bool
  | .leaf e => fun k => e.xfBits d env k
  | .ite c a b => fun k => if c.xfBits d env 0 then a.bit d env k else b.bit d env k
  | .blk t => t.bit d env

/-- Every leaf is `w` bits wide, every condition 1 bit, in the x-free fragment. -/
def PTree.xfOk (d : Design2) (w : Nat) : PTree → Prop
  | .leaf e => e.xfWidth d = some w
  | .ite c a b => c.xfWidth d = some 1 ∧ a.xfOk d w ∧ b.xfOk d w
  | .blk t => t.xfOk d w

theorem ifGuard_xfWidth (d : Design2) (c : Expr2) (h : c.xfWidth d = some 1) :
    (Expr2.ifGuard c).xfWidth d = some 1 := by
  simp [Expr2.ifGuard, Expr2.xfWidth, h, XF.same, LVec.ofLogic, LVec.knownB, LVec.width, Logic.isKnown]

theorem ifGuard_xfBits (d : Design2) (env : String → Nat → Bool) (c : Expr2) (h : c.xfWidth d = some 1) (k : Nat) :
    (Expr2.ifGuard c).xfBits d env k = c.xfBits d env 0 := by
  simp [Expr2.ifGuard, Expr2.xfBits, Expr2.xfWidth, h, XF.eqv, XF.red, XF.any, LVec.ofLogic, LVec.boolAt]

theorem low_xfWidth (d : Design2) (w : Nat) :
    ∀ t : PTree, t.xfOk d w → (t.low w).xfWidth d = some w := by
  intro t
  induction t with
  | leaf e => intro h; simp only [PTree.low, Expr2.xfWidth, PTree.xfOk] at *; simp [h]
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩
      simp only [PTree.low, Expr2.joinIte]
      split
      · exact iha ha
      · simp [Expr2.xfWidth, ifGuard_xfWidth d c hc, iha ha, ihb hb, XF.same]
  | blk t iht => intro h; simpa [PTree.low] using iht h

theorem low_xfBits (d : Design2) (env : String → Nat → Bool) (w : Nat) :
    ∀ t : PTree, t.xfOk d w → ∀ k, k < w → (t.low w).xfBits d env k = t.bit d env k := by
  intro t
  induction t with
  | leaf e => intro h k hk; simp [PTree.low, PTree.bit, Expr2.xfBits, PTree.xfOk] at *; simp [h, hk]
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ k hk
      simp only [PTree.low, Expr2.joinIte]
      split
      · rename_i hs
        have hab := Expr2.eq_of_same _ _ hs
        have h1 := iha ha k hk
        have h2 := ihb hb k hk
        rw [← hab] at h2
        have h3 : a.bit d env k = b.bit d env k := h1.symm.trans h2
        simp [PTree.bit, h1, h3]
      · simp [Expr2.xfBits, ifGuard_xfWidth d c hc, ifGuard_xfBits d env c hc, iha ha k hk, ihb hb k hk, PTree.bit, XF.any]
  | blk t iht => intro h k hk; simpa [PTree.low, PTree.bit] using iht h k hk


/-- A read window that does not overlap the write window meets it in zero bits (BWin form). -/
theorem inter_zero_of_win (n : String) (lo w : Nat) (W : Win)
    (h : (ReadWin.win n lo w).overlaps W = false) : (BWin.inter (n, lo, w) W).2.2 = 0 := by
  obtain ⟨m, l', w'⟩ := W
  simp only [ReadWin.overlaps, Win.overlaps_eq_false] at h
  simp only [BWin.inter]
  split
  · rename_i hn; subst hn; simp at h ⊢; omega
  · rfl

theorem inter_zero_of_whole (wd : String → Option Nat) (n : String) (W : Win)
    (h : (ReadWin.whole n).overlaps W = false) : (BWin.inter (whole wd n) W).2.2 = 0 := by
  obtain ⟨m, l', w'⟩ := W
  simp only [ReadWin.overlaps, beq_eq_false_iff_ne] at h
  simp [BWin.inter, whole, h]

set_option linter.unnecessarySimpa false in
theorem rdW_of_reads_aux (wd : String → Option Nat) (W : Win) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.idxFree = true → (∀ r ∈ e.reads, r.overlaps W = false) →
      ∀ x ∈ e.rdW wd, (BWin.inter x W).2.2 = 0) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → Expr2.listIdxFree l = true →
      (∀ r ∈ Expr2.listReads l, r.overlaps W = false) →
      ∀ x ∈ Expr2.listRdW wd l, (BWin.inter x W).2.2 = 0) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h => by omega, fun l h => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he hi hr x hx => ?_, fun l hl hi hr x hx => ?_⟩
    · cases e with
      | lit v => simp [Expr2.rdW] at hx
      | unsupported k t => simp [Expr2.rdW] at hx
      | ident m =>
          simp only [Expr2.rdW, List.mem_singleton] at hx; subst hx
          exact inter_zero_of_whole wd m W (hr _ (by simp [Expr2.reads]))
      | unary op a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | resizeSigned w a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | squash2 a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | repl k a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | reduce op a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | resize w a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | binary op l r =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe l (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihe r (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | scmp op l r =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe l (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihe r (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | logical b l r =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe l (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihe r (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | index a i w => simp [Expr2.idxFree] at hi
      | ternary c t f =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx | hx
          · exact ihe c (by omega) hi.1.1 (fun r' h => hr r' (Or.inl (Or.inl h))) x hx
          · exact ihe t (by omega) hi.1.2 (fun r' h => hr r' (Or.inl (Or.inr h))) x hx
          · exact ihe f (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | slice a lo w =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          cases a with
          | ident m =>
              simp only [Expr2.rdW, sliceRd, List.mem_singleton] at hx; subst hx
              exact inter_zero_of_win m lo w W (hr _ (by simp [Expr2.reads, Expr2.sliceReads]))
          | _ =>
              rename_i a'
              first
              | (exact ihe _ (by omega) hi (by simpa [Expr2.reads, Expr2.sliceReads] using hr) x
                  (by simpa [Expr2.rdW, sliceRd] using hx))
      | concat parts =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihl parts.toList (by omega) hi (by simpa [Expr2.reads] using hr) x
            (by simpa [Expr2.rdW] using hx)
    · cases l with
      | nil => simp [Expr2.listRdW] at hx
      | cons e es =>
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listIdxFree, Bool.and_eq_true] at hi
          simp only [Expr2.listReads, List.mem_append] at hr
          simp only [Expr2.listRdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe e (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihl es (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx

theorem rdW_of_reads (wd : String → Option Nat) (W : Win) (e : Expr2) (hi : e.idxFree = true)
    (hr : ∀ r ∈ e.reads, r.overlaps W = false) : ∀ x ∈ e.rdW wd, (BWin.inter x W).2.2 = 0 :=
  (rdW_of_reads_aux wd W (e.size + 1)).1 e (Nat.lt_succ_self _) hi hr


/-- The tree has no `index` node. -/
def PTree.idxFree : PTree → Prop
  | .leaf e => e.idxFree = true
  | .ite c a b => c.idxFree = true ∧ a.idxFree ∧ b.idxFree
  | .blk t => t.idxFree

/-- The window-level (`ReadWin`) non-overlap, which is what the summary's `noSelfRead` obligation gives,
implies the bit-level one the self-read guard walks. -/
theorem noRdW_of_noRead (wd : String → Option Nat) (W : Win) :
    ∀ t : PTree, t.idxFree → t.noRead W → t.noRdW wd W := by
  intro t
  induction t with
  | leaf e => exact fun hi h => rdW_of_reads wd W e hi h
  | ite c a b iha ihb =>
      intro ⟨hi, ha, hb⟩ ⟨hc, hna, hnb⟩
      exact ⟨rdW_of_reads wd W c hi hc, iha ha hna, ihb hb hnb⟩
  | blk t iht => exact fun hi h => iht hi h
/-! ## S-C (generic form): the lowering of an instantiated tree -/

theorem lower_tree (d : Design2) (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hsw : tgt.symWin d = some W) (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (t : PTree)
    (hwf : t.wf d) (hrd : t.noRdW wd W) (hno : t.noRead W) :
    Process2.lowerComb d (combGuardProc wd (t.toStmt tgt)) =
      some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2])) := by
  rw [combGuardProc_of_admits (combAdmits_tree wd tgt W hm hr t hrd)]
  have h1 : (t.toStmt tgt).symExec d [] = some [(W, t.low W.2.2)] := symExec_tree d tgt W hsw t hwf
  simp [Process2.lowerComb, h1, selfReadFree_tree W W.2.2 t hno, SymState.toAssign, SymState.target,
    SymState.rhs]

/-- The final form: ONE non-overlap hypothesis (window level) and no index nodes. -/
theorem lower_tree' (d : Design2) (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hsw : tgt.symWin d = some W) (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (t : PTree)
    (hwf : t.wf d) (hix : t.idxFree) (hno : t.noRead W) :
    Process2.lowerComb d (combGuardProc wd (t.toStmt tgt)) =
      some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2])) :=
  lower_tree d wd tgt W hsw hm hr t hwf (noRdW_of_noRead wd W t hix hno) hno

/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombProc.wfB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wfB_iff

/-- info: 'LeanModels.Sv.CombProc.listWfB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms listWfB_iff

/-- info: 'LeanModels.Sv.CombProc.symSubst_nil_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_nil_aux

/-- info: 'LeanModels.Sv.CombProc.symSubst_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_nil

/-- info: 'LeanModels.Sv.CombProc.symExec_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExec_tree

/-- info: 'LeanModels.Sv.CombProc.low_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_reads

/-- info: 'LeanModels.Sv.CombProc.selfReadFree_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selfReadFree_tree

/-- info: 'LeanModels.Sv.CombProc.drvWins_tree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms drvWins_tree

/-- info: 'LeanModels.Sv.CombProc.BWin.subAll_nil_of_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BWin.subAll_nil_of_zero

/-- info: 'LeanModels.Sv.CombProc.readsViol_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readsViol_none

/-- info: 'LeanModels.Sv.CombProc.mayW_tree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms mayW_tree

/-- info: 'LeanModels.Sv.CombProc.combViol_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combViol_tree

/-- info: 'LeanModels.Sv.CombProc.combAdmits_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combAdmits_tree

/-- info: 'LeanModels.Sv.CombProc.ifGuard_xfWidth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ifGuard_xfWidth

/-- info: 'LeanModels.Sv.CombProc.ifGuard_xfBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ifGuard_xfBits

/-- info: 'LeanModels.Sv.CombProc.low_xfWidth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfWidth

/-- info: 'LeanModels.Sv.CombProc.low_xfBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfBits

/-- info: 'LeanModels.Sv.CombProc.inter_zero_of_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inter_zero_of_win

/-- info: 'LeanModels.Sv.CombProc.inter_zero_of_whole' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inter_zero_of_whole

/-- info: 'LeanModels.Sv.CombProc.rdW_of_reads_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rdW_of_reads_aux

/-- info: 'LeanModels.Sv.CombProc.rdW_of_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rdW_of_reads

/-- info: 'LeanModels.Sv.CombProc.noRdW_of_noRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noRdW_of_noRead

/-- info: 'LeanModels.Sv.CombProc.lower_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_tree

/-- info: 'LeanModels.Sv.CombProc.lower_tree'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_tree'

end CombProc
end LeanModels.Sv
