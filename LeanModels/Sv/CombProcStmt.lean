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

/-- A read window is not empty (a zero-width slice at the edge of a window is "covered" by it, which the
independence of a read from an earlier write needs to exclude). -/
def ReadWin.pos : ReadWin → Prop
  | .whole _ => True
  | .win _ _ w => 0 < w

/-- A read that is apart from the window `W`: it overlaps nothing of `W` and is not empty. -/
def ReadWin.apart (W : Win) (r : ReadWin) : Prop := r.overlaps W = false ∧ r.pos

/-- The statements of a block, or the statement itself (the flattening of a default-then-override body). -/
def Stmt2.unblock : Stmt2 → List Stmt2
  | .block ss => ss.toList
  | s => [s]

namespace CombProc
open CombGuard

/-- The arms of a tree `case`: patterns and the value assigned on a hit. -/
def caseItems (tgt : Lhs2) : List (List Expr2 × Expr2) → List CaseItem2
  | [] => []
  | (ps, e) :: rest => CaseItem2.mk ps.toArray (.blockingAssign tgt e) :: caseItems tgt rest

/-- The lowered right-hand side of a tree `case`: first hit wins, ending in the default. -/
def caseLow (w : Nat) (s : Expr2) : List (List Expr2 × Expr2) → Expr2 → Expr2
  | [], d => .resize w d
  | (ps, e) :: rest, d =>
      Expr2.joinIte (Expr2.anyGuard .normal s ps) (.resize w e) (caseLow w s rest d)

/-- Every pattern list and arm value of the arms is well formed. -/
def CasesWf (d : Design2) (its : List (List Expr2 × Expr2)) : Prop :=
  ∀ it ∈ its, Expr2.listWfB d it.1 = true ∧ it.2.wfB d = true

/-! A tree of `if/else` over leaf right-hand sides, all assigning ONE target `tgt` (a whole signal or a
constant slice; its window is `W`): the S1 body shape. `blk` is a `begin t end` around one tree (the body of
the process, and the arms of an `if` written with `begin ... end`). -/
inductive PTree where
  | leaf (e : Expr2)
  | ite (c : Expr2) (a b : PTree)
  | blk (t : PTree)
  /-- A plain `case` whose arms are single assignments of the target (WP-G S3a): the subject, the arms
  (patterns and the value assigned on a hit, in source order) and the default's value. -/
  | cases (s : Expr2) (its : List (List Expr2 × Expr2)) (d : Expr2)
  /-- WP-G S3b: default-then-override on the one window, `b; if (c) a;` (the statements of `b`, then an
  `if` without `else` whose branch is the tree `a`): the last write wins. Its lowering is that of
  `ite c a b`; only the statement differs. -/
  | ovr (c : Expr2) (a b : PTree)

/-- The tree is an override (its statement is a block of several statements). -/
def PTree.isOvr : PTree → Bool
  | .ovr .. => true
  | _ => false

/-- The statements before the override `if`: the flattened block of an override base, else the base's
statement. -/
def PTree.baseL (b : PTree) (sb : Stmt2) : List Stmt2 := if b.isOvr then Stmt2.unblock sb else [sb]

/-- The statement a tree stands for. -/
def PTree.toStmt (tgt : Lhs2) : PTree → Stmt2
  | .leaf e => .blockingAssign tgt e
  | .ite c a b => .ifStmt c (a.toStmt tgt) (some (b.toStmt tgt))
  | .blk t => .block #[t.toStmt tgt]
  | .cases s its d => .caseStmt s (caseItems tgt its).toArray (some (.blockingAssign tgt d)) .normal .none
  | .ovr c a b => .block (b.baseL (b.toStmt tgt) ++ [Stmt2.ifStmt c (a.toStmt tgt) none]).toArray

/-- The lowered right-hand side of the window. -/
def PTree.low (w : Nat) : PTree → Expr2
  | .leaf e => .resize w e
  | .ite c a b => Expr2.joinIte (Expr2.ifGuard c) (a.low w) (b.low w)
  | .blk t => t.low w
  | .cases s its d => caseLow w s its d
  | .ovr c a b => Expr2.joinIte (Expr2.ifGuard c) (a.low w) (b.low w)

/-- Well-formedness of every expression of the tree. -/
def PTree.wf (d : Design2) : PTree → Prop
  | .leaf e => e.wfB d = true
  | .ite c a b => c.wfB d = true ∧ a.wf d ∧ b.wf d
  | .blk t => t.wf d
  | .cases s its dd => s.wfB d = true ∧ CasesWf d its ∧ dd.wfB d = true
  | .ovr c a b => c.wfB d = true ∧ a.wf d ∧ b.wf d

/-! ## Helper: substitution into the empty symbolic state is the identity -/

theorem wfB_iff (d : Design2) (e : Expr2) :
    e.wfB d = true ↔ e.unsupportedFree = true ∧ ∀ x ∈ e.idents, x ∈ d.symNames := by
  simp [Expr2.wfB, List.all_eq_true]

theorem listWfB_iff (d : Design2) (l : List Expr2) :
    Expr2.listWfB d l = true ↔ Expr2.listUnsupportedFree l = true ∧ ∀ x ∈ Expr2.listIdents l, x ∈ d.symNames := by
  simp [Expr2.listWfB, List.all_eq_true]

theorem symSubst_nil_aux (d : Design2) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.wfB d = true → e.idxFree = true → e.symSubst d [] = some e) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → Expr2.listWfB d l = true →
      Expr2.listIdxFree l = true → Expr2.listSymSubst d [] l = some l) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h _ _ => by omega, fun l h _ _ => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he hw hx => ?_, fun l hl hw hx => ?_⟩
    · rw [wfB_iff] at hw
      obtain ⟨hu, hi⟩ := hw
      have sub : ∀ a : Expr2, a.size < n → a.unsupportedFree = true →
          (∀ x ∈ a.idents, x ∈ d.symNames) → a.idxFree = true →
          a.symSubst d [] = some a :=
        fun a ha hu hi hx => ihe a ha ((wfB_iff d a).2 ⟨hu, hi⟩) hx
      cases e with
      | lit v => simp [Expr2.symSubst]
      | ident m =>
          have : m ∈ d.symNames := hi m (by simp [Expr2.idents])
          simp [Expr2.symSubst, this, SymState.readWhole, SymState.writesName]
      | unsupported k t => simp [Expr2.unsupportedFree] at hu
      | unary op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hx
          simp [Expr2.symSubst, sub a (by omega) hu hi hx]
      | resizeSigned w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hx
          simp [Expr2.symSubst, sub a (by omega) hu hi hx]
      | squash2 a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hx
          simp [Expr2.symSubst, sub a (by omega) hu hi hx]
      | repl k a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hx
          simp [Expr2.symSubst, sub a (by omega) hu hi hx]
      | reduce op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hx
          simp [Expr2.symSubst, sub a (by omega) hu hi hx]
      | resize w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hx
          simp [Expr2.symSubst, sub a (by omega) hu hi hx]
      | binary op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp only [Expr2.idxFree, Bool.and_eq_true] at hx
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)) hx.1,
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hx.2]
      | scmp op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp only [Expr2.idxFree, Bool.and_eq_true] at hx
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)) hx.1,
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hx.2]
      | logical b l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp only [Expr2.idxFree, Bool.and_eq_true] at hx
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)) hx.1,
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hx.2]
      | index a i w =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.idxFree] at hx
      | ternary c t f =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp only [Expr2.idxFree, Bool.and_eq_true] at hx
          simp [Expr2.symSubst, sub c (by omega) hu.1.1 (fun x hx => hi x (Or.inl (Or.inl hx))) hx.1.1,
            sub t (by omega) hu.1.2 (fun x hx => hi x (Or.inl (Or.inr hx))) hx.1.2,
            sub f (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hx.2]
      | slice a lo w =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idents] at hi
          by_cases hid : ∃ m, a = .ident m
          · obtain ⟨m, rfl⟩ := hid
            have : m ∈ d.symNames := hi m (by simp [Expr2.idents])
            simp only [Expr2.idxFree] at hx
            simp [Expr2.symSubst, Expr2.sliceSubst, this, SymState.readWin, SymState.findCover,
              SymState.overlapsAny]
          · have hs : ∀ r, Expr2.sliceSubst d [] a lo w r = r.map fun b => Expr2.slice b lo w := by
              intro r; cases a <;> simp_all [Expr2.sliceSubst]
            have ih := sub a (by omega) hu hi hx
            simp [Expr2.symSubst, hs, ih]
      | concat parts =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idents] at hi
          simp only [Expr2.idxFree] at hx
          have := ihl parts.toList (by omega) ((listWfB_iff d _).2 ⟨hu, hi⟩) hx
          simp [Expr2.symSubst, this]
    · cases l with
      | nil => simp [Expr2.listSymSubst]
      | cons e es =>
          rw [listWfB_iff] at hw
          obtain ⟨hu, hi⟩ := hw
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listUnsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.listIdents, List.mem_append] at hi
          simp only [Expr2.listIdxFree, Bool.and_eq_true] at hx
          have h1 := ihe e (by omega) ((wfB_iff d e).2 ⟨hu.1, fun x hx => hi x (Or.inl hx)⟩)
            hx.1
          have h2 := ihl es (by omega) ((listWfB_iff d es).2 ⟨hu.2, fun x hx => hi x (Or.inr hx)⟩)
            hx.2
          simp [Expr2.listSymSubst, h1, h2]

theorem symSubst_nil (d : Design2) (e : Expr2) (h : e.wfB d = true)
    (hx : e.idxFree = true) : e.symSubst d [] = some e :=
  (symSubst_nil_aux d (e.size + 1)).1 e (Nat.lt_succ_self _) h hx



/-! ## A1: the symbolic execution -/

theorem listSymSubst_nil (d : Design2) (l : List Expr2) (h : Expr2.listWfB d l = true)
    (hx : Expr2.listIdxFree l = true) : Expr2.listSymSubst d [] l = some l :=
  (symSubst_nil_aux d (Expr2.listSize l + 1)).2 l (Nat.lt_succ_self _) h hx

/-- No `index` node in a pattern or arm value. -/
def CasesIdxFree (its : List (List Expr2 × Expr2)) : Prop :=
  ∀ it ∈ its, Expr2.listIdxFree it.1 = true ∧ it.2.idxFree = true

/-- The tree has no `index` node. -/
def PTree.idxFree : PTree → Prop
  | .leaf e => e.idxFree = true
  | .ite c a b => c.idxFree = true ∧ a.idxFree ∧ b.idxFree
  | .blk t => t.idxFree
  | .cases s its dd => s.idxFree = true ∧ CasesIdxFree its ∧ dd.idxFree = true
  | .ovr c a b => c.idxFree = true ∧ a.idxFree ∧ b.idxFree

/-- No read of a pattern or arm value is near the written window (overlapping it, or empty). -/
def CasesNoRead (W : Win) (its : List (List Expr2 × Expr2)) : Prop :=
  ∀ it ∈ its, (∀ r ∈ Expr2.listReads it.1, r.apart W) ∧ ∀ r ∈ it.2.reads, r.apart W

/-- No read of any expression of the tree is near the window `W`. -/
def PTree.noRead (W : Win) : PTree → Prop
  | .leaf e => ∀ r ∈ e.reads, r.apart W
  | .ite c a b => (∀ r ∈ c.reads, r.apart W) ∧ a.noRead W ∧ b.noRead W
  | .blk t => t.noRead W
  | .cases s its dd => (∀ r ∈ s.reads, r.apart W) ∧ CasesNoRead W its ∧ ∀ r ∈ dd.reads, r.apart W
  | .ovr c a b => (∀ r ∈ c.reads, r.apart W) ∧ a.noRead W ∧ b.noRead W

theorem apart_contains_false (m : String) (lo w : Nat) (X : Win) (h : (ReadWin.win m lo w).apart X) :
    Win.contains X (m, lo, w) = false ∧ Win.overlaps X (m, lo, w) = false := by
  obtain ⟨n0, l0, v0⟩ := X
  have h1 := h.1
  have h2 : 0 < w := h.2
  simp only [ReadWin.overlaps, Win.overlaps_eq_false] at h1
  have key : m = n0 → (l0 + v0 ≤ lo ∨ lo + w ≤ l0) := by
    intro hmn
    rcases h1 with h | h | h
    · exact absurd hmn h
    · exact Or.inl h
    · exact Or.inr h
  constructor
  · simp only [Win.contains]
    by_cases hn : n0 = m
    · have := key hn.symm
      subst hn; simp; omega
    · simp [hn]
  · simp only [Win.overlaps]
    by_cases hn : n0 = m
    · have := key hn.symm
      subst hn; simp; omega
    · simp [hn]

theorem symSubst_apartL_ident (d : Design2) (S : SymState) (m : String) (hm : m ∈ d.symNames)
    (h : ∀ x ∈ S, (ReadWin.whole m).apart x.1) : (Expr2.ident m).symSubst d S = some (.ident m) := by
  have hwn : S.writesName m = false := by
    simp only [SymState.writesName, List.any_eq_false]
    intro x hx
    have h1 := (h x hx).1
    have : x.1.1 ≠ m := by
      obtain ⟨⟨n0, l0, v0⟩, E⟩ := x
      simp only [ReadWin.overlaps, beq_eq_false_iff_ne] at h1
      exact fun hh => h1 hh.symm
    simpa using this
  simp [Expr2.symSubst, hm, SymState.readWhole, hwn]

theorem symSubst_apartL_slice (d : Design2) (S : SymState) (m : String) (lo w : Nat)
    (hm : m ∈ d.symNames) (h : ∀ x ∈ S, (ReadWin.win m lo w).apart x.1) (r : Option Expr2) :
    Expr2.sliceSubst d S (.ident m) lo w r = some (.slice (.ident m) lo w) := by
  have hc : S.findCover (m, lo, w) = none := by
    simp only [SymState.findCover, List.find?_eq_none]
    intro x hx
    have := (apart_contains_false m lo w x.1 (h x hx)).1
    simp [this]
  have ho : S.overlapsAny (m, lo, w) = false := by
    simp only [SymState.overlapsAny, List.any_eq_false]
    intro x hx
    have := (apart_contains_false m lo w x.1 (h x hx)).2
    simp [this]
  simp [Expr2.sliceSubst, hm, SymState.readWin, hc, ho]

theorem symSubst_slice_nonident (d : Design2) (S : SymState) (a : Expr2) (lo w : Nat)
    (h : ∀ m, a ≠ .ident m) :
    (Expr2.slice a lo w).symSubst d S = (a.symSubst d S).map fun b => .slice b lo w := by
  cases a with
  | ident m => exact absurd rfl (h m)
  | _ => simp [Expr2.symSubst, Expr2.sliceSubst]

theorem reads_slice_nonident (a : Expr2) (lo w : Nat) (h : ∀ m, a ≠ .ident m) :
    (Expr2.slice a lo w).reads = a.reads := by
  cases a with
  | ident m => exact absurd rfl (h m)
  | _ => simp [Expr2.reads, Expr2.sliceReads]

theorem symSubst_apartL_aux (d : Design2) (S : SymState) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.wfB d = true → e.idxFree = true →
      (∀ r ∈ e.reads, ∀ x ∈ S, r.apart x.1) → e.symSubst d S = some e) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → Expr2.listWfB d l = true → Expr2.listIdxFree l = true →
      (∀ r ∈ Expr2.listReads l, ∀ x ∈ S, r.apart x.1) →
      Expr2.listSymSubst d S l = some l) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h => by omega, fun l h => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he hw hix hrd => ?_, fun l hl hw hix hrd => ?_⟩
    · rw [wfB_iff] at hw
      obtain ⟨hu, hi⟩ := hw
      have sub : ∀ a : Expr2, a.size < n → a.unsupportedFree = true →
          (∀ x ∈ a.idents, x ∈ d.symNames) → a.idxFree = true →
          (∀ r ∈ a.reads, ∀ x ∈ S, r.apart x.1) →
          a.symSubst d S = some a :=
        fun a ha hu hi hx hr => ihe a ha ((wfB_iff d a).2 ⟨hu, hi⟩) hx hr
      cases e with
      | lit v => simp [Expr2.symSubst]
      | ident m =>
          exact symSubst_apartL_ident d S m (hi m (by simp [Expr2.idents]))
            (fun x hx => hrd _ (by simp [Expr2.reads]) x hx)
      | unsupported k t => simp [Expr2.unsupportedFree] at hu
      | unary op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp [Expr2.symSubst, sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)]
      | resizeSigned w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp [Expr2.symSubst, sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)]
      | squash2 a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp [Expr2.symSubst, sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)]
      | repl k a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp [Expr2.symSubst, sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)]
      | reduce op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp [Expr2.symSubst, sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)]
      | resize w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp [Expr2.symSubst, sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)]
      | binary op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idxFree, Bool.and_eq_true] at hix
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst,
            sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)) hix.1
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hix.2
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx)]
      | scmp op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idxFree, Bool.and_eq_true] at hix
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst,
            sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)) hix.1
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hix.2
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx)]
      | logical b l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idxFree, Bool.and_eq_true] at hix
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst,
            sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)) hix.1
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hix.2
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx)]
      | index a i w => simp [Expr2.idxFree] at hix
      | ternary c t f =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idxFree, Bool.and_eq_true] at hix
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst,
            sub c (by omega) hu.1.1 (fun x hx => hi x (Or.inl (Or.inl hx))) hix.1.1
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx),
            sub t (by omega) hu.1.2 (fun x hx => hi x (Or.inl (Or.inr hx))) hix.1.2
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx),
            sub f (by omega) hu.2 (fun x hx => hi x (Or.inr hx)) hix.2
              (fun r' h x hx => hrd r' (by simp [Expr2.reads, h]) x hx)]
      | slice a lo w =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp only [Expr2.idents] at hi
          by_cases hid : ∃ m, a = .ident m
          · obtain ⟨m, rfl⟩ := hid
            have hm : m ∈ d.symNames := hi m (by simp [Expr2.idents])
            have hr1 : ∀ x ∈ S, (ReadWin.win m lo w).apart x.1 :=
              fun x hx => hrd _ (by simp [Expr2.reads, Expr2.sliceReads]) x hx
            simp only [Expr2.symSubst]
            exact symSubst_apartL_slice d S m lo w hm hr1 _
          · have hna : ∀ m, a ≠ .ident m := fun m h => hid ⟨m, h⟩
            rw [symSubst_slice_nonident d _ a lo w hna]
            rw [sub a (by omega) hu hi hix (fun r' h x hx => hrd r' (by rw [reads_slice_nonident a lo w hna]; exact h) x hx)]
            rfl
      | concat parts =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idxFree] at hix
          simp only [Expr2.idents] at hi
          have := ihl parts.toList (by omega) ((listWfB_iff d _).2 ⟨hu, hi⟩) hix
            (fun r' h x hx => hrd r' (by simpa [Expr2.reads] using h) x hx)
          simp [Expr2.symSubst, this]
    · cases l with
      | nil => simp [Expr2.listSymSubst]
      | cons e es =>
          rw [listWfB_iff] at hw
          obtain ⟨hu, hi⟩ := hw
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listUnsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.listIdxFree, Bool.and_eq_true] at hix
          simp only [Expr2.listIdents, List.mem_append] at hi
          have h1 := ihe e (by omega) ((wfB_iff d e).2 ⟨hu.1, fun x hx => hi x (Or.inl hx)⟩) hix.1
            (fun r' h x hx => hrd r' (by simp [Expr2.listReads, h]) x hx)
          have h2 := ihl es (by omega) ((listWfB_iff d es).2 ⟨hu.2, fun x hx => hi x (Or.inr hx)⟩) hix.2
            (fun r' h x hx => hrd r' (by simp [Expr2.listReads, h]) x hx)
          simp [Expr2.listSymSubst, h1, h2]


theorem symSubst_apartL (d : Design2) (S : SymState) (e : Expr2) (hw : e.wfB d = true)
    (hi : e.idxFree = true) (hr : ∀ r ∈ e.reads, ∀ x ∈ S, r.apart x.1) : e.symSubst d S = some e :=
  (symSubst_apartL_aux d S (e.size + 1)).1 e (Nat.lt_succ_self _) hw hi hr

theorem listSymSubst_apartL (d : Design2) (S : SymState) (l : List Expr2)
    (hw : Expr2.listWfB d l = true) (hi : Expr2.listIdxFree l = true)
    (hr : ∀ r ∈ Expr2.listReads l, ∀ x ∈ S, r.apart x.1) : Expr2.listSymSubst d S l = some l :=
  (symSubst_apartL_aux d S (Expr2.listSize l + 1)).2 l (Nat.lt_succ_self _) hw hi hr



/-- A symbolic state that is empty or holds just the window `W`. -/
def SingleW (W : Win) (S : SymState) : Prop := S = [] ∨ ∃ E0, S = [(W, E0)]

theorem symSubst_apart (d : Design2) (W : Win) (S : SymState) (hS : SingleW W S) (e : Expr2)
    (hw : e.wfB d = true) (hi : e.idxFree = true) (hr : ∀ r ∈ e.reads, r.apart W) :
    e.symSubst d S = some e :=
  symSubst_apartL d S e hw hi (by
    rcases hS with rfl | ⟨E0, rfl⟩
    · intro r _ x hx; exact absurd hx List.not_mem_nil
    · intro r hr' x hx; rw [List.mem_singleton.mp hx]; exact hr r hr')

theorem listSymSubst_apart (d : Design2) (W : Win) (S : SymState) (hS : SingleW W S)
    (l : List Expr2) (hw : Expr2.listWfB d l = true) (hi : Expr2.listIdxFree l = true)
    (hr : ∀ r ∈ Expr2.listReads l, r.apart W) : Expr2.listSymSubst d S l = some l :=
  listSymSubst_apartL d S l hw hi (by
    rcases hS with rfl | ⟨E0, rfl⟩
    · intro r _ x hx; exact absurd hx List.not_mem_nil
    · intro r hr' x hx; rw [List.mem_singleton.mp hx]; exact hr r hr')

/-- Writing the window into a state that is empty or holds it leaves just that entry. -/
theorem write_single (W : Win) (S : SymState) (hS : SingleW W S) (E : Expr2) :
    S.write W E = some [(W, E)] := by
  rcases hS with rfl | ⟨E0, rfl⟩
  · simp [SymState.write, SymState.findCover, SymState.overlapsAny]
  · simp [SymState.write]

theorem join_single (G a b : Expr2) (W : Win) :
    SymState.join G [(W, a)] [(W, b)] = some [(W, Expr2.joinIte G a b)] := by
  simp [SymState.join, SymState.joinWins, Win.allDisjoint, SymState.lookupOr, SymState.findWin]

theorem symExecList_append (d : Design2) :
    ∀ (l1 l2 : List Stmt2) (S : SymState), Stmt2.symExecList d S (l1 ++ l2) =
      (Stmt2.symExecList d S l1).bind fun S' => Stmt2.symExecList d S' l2
  | [], l2, S => by simp [Stmt2.symExecList]
  | s :: r, l2, S => by
      simp only [List.cons_append, Stmt2.symExecList]
      cases s.symExec d S with
      | none => rfl
      | some S' => exact symExecList_append d r l2 S'

/-- The statements before an override `if`, run: the base's own run. -/
theorem symExecList_baseL (d : Design2) (S : SymState) (b : PTree) (tgt : Lhs2) (r : SymState)
    (h : (b.toStmt tgt).symExec d S = some r) :
    Stmt2.symExecList d S (b.baseL (b.toStmt tgt)) = some r := by
  unfold PTree.baseL
  split
  · rename_i ho
    cases b <;> simp [PTree.isOvr] at ho
    simp only [PTree.toStmt, Stmt2.unblock, Stmt2.symExec] at h ⊢
    exact h
  · simp [Stmt2.symExecList, h]

theorem symExec_caseItems (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W)
    (S : SymState) (hS : SingleW W S) (s dflt : Expr2) :
    ∀ its : List (List Expr2 × Expr2), CasesWf d its → CasesIdxFree its → CasesNoRead W its →
      CaseItem2.symExecList d S s .normal [(W, .resize W.2.2 dflt)] (caseItems tgt its) =
        some [(W, caseLow W.2.2 s its dflt)] := by
  intro its
  induction its with
  | nil => intro _ _ _; simp [caseItems, CaseItem2.symExecList, caseLow]
  | cons it rest ih =>
      intro h hi hn
      obtain ⟨ps, e⟩ := it
      have hps := (h (ps, e) (List.mem_cons_self ..)).1
      have he := (h (ps, e) (List.mem_cons_self ..)).2
      have hips := (hi (ps, e) (List.mem_cons_self ..)).1
      have hie := (hi (ps, e) (List.mem_cons_self ..)).2
      have hnps := (hn (ps, e) (List.mem_cons_self ..)).1
      have hne := (hn (ps, e) (List.mem_cons_self ..)).2
      have hrest : CasesWf d rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hirest : CasesIdxFree rest := fun x hx => hi x (List.mem_cons_of_mem _ hx)
      have hnrest : CasesNoRead W rest := fun x hx => hn x (List.mem_cons_of_mem _ hx)
      have hw1 : Stmt2.symExec d S (.blockingAssign tgt e) = some [(W, .resize W.2.2 e)] := by
        simp [Stmt2.symExec, he, symSubst_apart d W S hS e he hie hne, hsw, write_single W S hS]
      simp [caseItems, CaseItem2.symExecList, CaseItem2.symArm, hps,
        listSymSubst_apart d W S hS ps hps hips hnps, hw1, ih hrest hirest hnrest, join_single,
        caseLow]

theorem symExec_cases (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W)
    (S : SymState) (hS : SingleW W S)
    (s dflt : Expr2) (its : List (List Expr2 × Expr2)) (hs : s.wfB d = true)
    (hsi : s.idxFree = true) (hsn : ∀ r ∈ s.reads, r.apart W)
    (hd : dflt.wfB d = true) (hdi : dflt.idxFree = true) (hdn : ∀ r ∈ dflt.reads, r.apart W)
    (hits : CasesWf d its) (hii : CasesIdxFree its) (hin : CasesNoRead W its) :
    (Stmt2.caseStmt s (caseItems tgt its).toArray (some (.blockingAssign tgt dflt)) .normal .none).symExec
        d S = some [(W, caseLow W.2.2 s its dflt)] := by
  have h1 : Stmt2.symExecOpt d S (some (.blockingAssign tgt dflt)) =
      some [(W, .resize W.2.2 dflt)] := by
    simp [Stmt2.symExecOpt, Stmt2.symExec, hd, symSubst_apart d W S hS dflt hd hdi hdn, hsw,
      write_single W S hS]
  simp only [Stmt2.symExec, hs, if_true, symSubst_apart d W S hS s hs hsi hsn, Option.bind_some, h1]
  exact symExec_caseItems d tgt W hsw S hS s dflt its hits hii hin

theorem symExec_tree (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W) :
    ∀ t : PTree, t.wf d → t.idxFree → t.noRead W → ∀ S : SymState, SingleW W S →
      (t.toStmt tgt).symExec d S = some [(W, t.low W.2.2)] := by
  intro t
  induction t with
  | leaf e =>
      intro (h1 : e.wfB d = true) (hi : e.idxFree = true) (hn : ∀ r ∈ e.reads, r.apart W) S hS
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, h1, symSubst_apart d W S hS e h1 hi hn, hsw,
        write_single W S hS]
  | ite c a b iha ihb =>
      intro ⟨h1, ha, hb⟩ ⟨hic, hia, hib⟩ ⟨hnc, hna, hnb⟩ S hS
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecOpt, h1,
        symSubst_apart d W S hS c h1 hic hnc, iha ha hia hna S hS, ihb hb hib hnb S hS, join_single]
  | blk t iht =>
      intro (ht : t.wf d) (hit : t.idxFree) (hnt : t.noRead W) S hS
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecList, iht ht hit hnt S hS]
  | cases s its dd =>
      intro ⟨hs, hits, hdd⟩ ⟨hsi, hii, hdi⟩ ⟨hsn, hin, hdn⟩ S hS
      exact symExec_cases d tgt W hsw S hS s dd its hs hsi hsn hdd hdi hdn hits hii hin
  | ovr c a b iha ihb =>
      intro ⟨h1, ha, hb⟩ ⟨hic, hia, hib⟩ ⟨hnc, hna, hnb⟩ S hS
      have hbase := symExecList_baseL d S b tgt _ (ihb hb hib hnb S hS)
      have hS1 : SingleW W [(W, b.low W.2.2)] := Or.inr ⟨_, rfl⟩
      simp only [PTree.toStmt, Stmt2.symExec]
      rw [symExecList_append, hbase]
      simp [Stmt2.symExecList, Stmt2.symExec, Stmt2.symExecOpt, h1,
        symSubst_apart d W _ hS1 c h1 hic hnc, iha ha hia hna _ hS1, join_single, PTree.low]


/-! ## A2: no self-read of the lowered equation -/

theorem anyGuard_reads (s : Expr2) :
    ∀ (ps : List Expr2) (r : ReadWin), r ∈ (Expr2.anyGuard .normal s ps).reads →
      r ∈ s.reads ∨ r ∈ Expr2.listReads ps
  | [], r, h => by simp [Expr2.anyGuard, Expr2.reads] at h
  | p :: ps, r, h => by
      simp only [Expr2.anyGuard, Expr2.hitGuard, Bool.false_eq_true, if_false, Expr2.reads,
        List.mem_append] at h
      rcases h with (h | h) | h
      · exact Or.inl h
      · right; simp only [Expr2.listReads, List.mem_append]; exact Or.inl h
      · rcases anyGuard_reads s ps r h with h | h
        · exact Or.inl h
        · right; simp only [Expr2.listReads, List.mem_append]; exact Or.inr h

theorem reads_caseLow (W : Win) (w : Nat) (s : Expr2) (hs : ∀ r ∈ s.reads, r.apart W)
    (dd : Expr2) (hd : ∀ r ∈ dd.reads, r.apart W) :
    ∀ its : List (List Expr2 × Expr2), CasesNoRead W its →
      ∀ r ∈ (caseLow w s its dd).reads, r.overlaps W = false := by
  intro its
  induction its with
  | nil => intro _ r hr; exact (hd r (by simpa [caseLow, Expr2.reads] using hr)).1
  | cons it rest ih =>
      intro h r hr
      obtain ⟨ps, e⟩ := it
      have h1 := (h (ps, e) (List.mem_cons_self ..)).1
      have h2 := (h (ps, e) (List.mem_cons_self ..)).2
      have hrest : CasesNoRead W rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [caseLow, Expr2.joinIte] at hr
      split at hr
      · exact (h2 r (by simpa [Expr2.reads] using hr)).1
      · simp only [Expr2.reads, List.mem_append] at hr
        rcases hr with (hr | hr) | hr
        · rcases anyGuard_reads s ps r hr with hr | hr
          · exact (hs r hr).1
          · exact (h1 r hr).1
        · exact (h2 r (by simpa [Expr2.reads] using hr)).1
        · exact ih hrest r hr

theorem low_reads (W : Win) (w : Nat) :
    ∀ t : PTree, t.noRead W → ∀ r ∈ (t.low w).reads, r.overlaps W = false := by
  intro t
  induction t with
  | leaf e => intro h r hr; exact (h r (by simpa [PTree.low, Expr2.reads] using hr)).1
  | ite c a b iha ihb | ovr c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ r hr
      simp only [PTree.low, Expr2.joinIte] at hr
      split at hr
      · exact iha ha r hr
      · simp only [Expr2.reads, Expr2.ifGuard, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with (hr | hr) | hr
        · exact (hc r hr).1
        · exact iha ha r hr
        · exact ihb hb r hr
  | blk t iht => intro h r hr; exact iht h r (by simpa [PTree.low] using hr)
  | cases s its dd =>
      intro ⟨hs, hits, hdd⟩ r hr
      exact reads_caseLow W w s hs dd hdd its hits r hr

theorem selfReadFree_tree (W : Win) (w : Nat) (t : PTree) (h : t.noRead W) :
    SymState.selfReadFree [(W, t.low w)] = true := by
  simp only [SymState.selfReadFree, List.map_cons, List.map_nil, Expr2.listReads, List.append_nil,
    List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true, Bool.not_eq_true']
  exact fun r hr => low_reads W w t h r hr

/-! ## A4: the driven windows -/

theorem drvWins_caseItems (tgt : Lhs2) :
    ∀ its : List (List Expr2 × Expr2), ∀ x ∈ CaseItem2.drvWinsList (caseItems tgt its),
      x ∈ tgt.drvWins := by
  intro its
  induction its with
  | nil => intro x hx; simp [caseItems, CaseItem2.drvWinsList] at hx
  | cons it rest ih =>
      intro x hx
      obtain ⟨ps, e⟩ := it
      simp only [caseItems, CaseItem2.drvWinsList, CaseItem2.drvWins, Stmt2.drvWins,
        List.mem_append] at hx
      rcases hx with hx | hx
      · exact hx
      · exact ih x hx

theorem drvWins_cases (tgt : Lhs2) (s dflt : Expr2) (its : List (List Expr2 × Expr2)) :
    ∀ x ∈ (Stmt2.caseStmt s (caseItems tgt its).toArray (some (.blockingAssign tgt dflt)) .normal
        .none).drvWins, x ∈ tgt.drvWins := by
  intro x hx
  simp only [Stmt2.drvWins, Stmt2.drvWinsOpt, List.mem_append] at hx
  rcases hx with hx | hx
  · exact drvWins_caseItems tgt its x hx
  · simpa [Stmt2.drvWins] using hx

theorem drvWinsList_append : ∀ (l1 l2 : List Stmt2),
    Stmt2.drvWinsList (l1 ++ l2) = Stmt2.drvWinsList l1 ++ Stmt2.drvWinsList l2
  | [], l2 => by simp [Stmt2.drvWinsList]
  | s :: r, l2 => by simp [Stmt2.drvWinsList, drvWinsList_append r l2]

theorem drvWinsList_baseL (tgt : Lhs2) (b : PTree) :
    ∀ x ∈ Stmt2.drvWinsList (b.baseL (b.toStmt tgt)), x ∈ (b.toStmt tgt).drvWins := by
  unfold PTree.baseL
  split
  · rename_i ho
    cases b <;> simp [PTree.isOvr] at ho
    simp only [PTree.toStmt, Stmt2.unblock, Stmt2.drvWins]
    exact fun x hx => hx
  · intro x hx; simpa [Stmt2.drvWinsList] using hx

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
  | cases s its dd => intro x hx; exact drvWins_cases tgt s dd its x hx
  | ovr c a b iha ihb =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.drvWins, List.toList_toArray, drvWinsList_append,
        Stmt2.drvWinsList, Stmt2.drvWinsOpt, List.append_nil, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihb x (drvWinsList_baseL tgt b x hx)
      · exact iha x hx

/-! ## A3: the self-read guard admits the body -/

/-- No read window of a pattern or an arm value meets the written window. -/
def CasesNoRdW (wd : String → Option Nat) (W : BWin) (its : List (List Expr2 × Expr2)) : Prop :=
  ∀ it ∈ its, (∀ r ∈ Expr2.listRdW wd it.1, (BWin.inter r W).2.2 = 0) ∧
    ∀ r ∈ it.2.rdW wd, (BWin.inter r W).2.2 = 0

/-- Every read window of every expression of the tree meets the window in zero bits. -/
def PTree.noRdW (wd : String → Option Nat) (W : BWin) : PTree → Prop
  | .leaf e => ∀ r ∈ e.rdW wd, (BWin.inter r W).2.2 = 0
  | .ite c a b => (∀ r ∈ c.rdW wd, (BWin.inter r W).2.2 = 0) ∧ a.noRdW wd W ∧ b.noRdW wd W
  | .blk t => t.noRdW wd W
  | .cases s its dd => (∀ r ∈ s.rdW wd, (BWin.inter r W).2.2 = 0) ∧ CasesNoRdW wd W its ∧
      ∀ r ∈ dd.rdW wd, (BWin.inter r W).2.2 = 0
  | .ovr c a b => (∀ r ∈ c.rdW wd, (BWin.inter r W).2.2 = 0) ∧ a.noRdW wd W ∧ b.noRdW wd W

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

theorem mayW_caseItems (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W]) :
    ∀ its : List (List Expr2 × Expr2), ∀ x ∈ CaseItem2.listMayW wd (caseItems tgt its), x = W := by
  intro its
  induction its with
  | nil => intro x hx; simp [caseItems, CaseItem2.listMayW] at hx
  | cons it rest ih =>
      intro x hx
      obtain ⟨ps, e⟩ := it
      simp only [caseItems, CaseItem2.listMayW, CaseItem2.mayW, Stmt2.mayW, hm,
        List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hx
      · exact ih x hx

theorem mayW_cases (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (s dflt : Expr2) (its : List (List Expr2 × Expr2)) :
    ∀ x ∈ (Stmt2.caseStmt s (caseItems tgt its).toArray (some (.blockingAssign tgt dflt)) .normal
        .none).mayW wd, x = W := by
  intro x hx
  simp only [Stmt2.mayW, Stmt2.optMayW, List.mem_append] at hx
  rcases hx with hx | hx
  · exact mayW_caseItems wd tgt W hm its x hx
  · simpa [Stmt2.mayW, hm] using hx

theorem listMayW_append (wd : String → Option Nat) : ∀ (l1 l2 : List Stmt2),
    Stmt2.listMayW wd (l1 ++ l2) = Stmt2.listMayW wd l1 ++ Stmt2.listMayW wd l2
  | [], l2 => by simp [Stmt2.listMayW]
  | s :: r, l2 => by simp [Stmt2.listMayW, listMayW_append wd r l2]

theorem listMayW_baseL (wd : String → Option Nat) (tgt : Lhs2) (b : PTree) :
    Stmt2.listMayW wd (b.baseL (b.toStmt tgt)) = (b.toStmt tgt).mayW wd := by
  unfold PTree.baseL
  split
  · rename_i ho
    cases b <;> simp [PTree.isOvr] at ho
    simp only [PTree.toStmt, Stmt2.unblock, Stmt2.mayW]
  · simp [Stmt2.listMayW]

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
  | cases s its dd => intro x hx; exact mayW_cases wd tgt W hm s dd its x hx
  | ovr c a b iha ihb =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.mayW, List.toList_toArray, listMayW_append, Stmt2.listMayW,
        Stmt2.optMayW, listMayW_baseL, List.append_nil, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihb x hx
      · exact iha x hx

theorem listCombViol_baseL (wd : String → Option Nat) (tgt : Lhs2) (b : PTree) (M A : List BWin) :
    Stmt2.listCombViol wd M A (b.baseL (b.toStmt tgt)) = (b.toStmt tgt).combViol wd M A := by
  unfold PTree.baseL
  split
  · rename_i ho
    cases b <;> simp [PTree.isOvr] at ho
    simp only [PTree.toStmt, Stmt2.unblock, Stmt2.combViol]
  · simp [Stmt2.listCombViol, Stmt2.listMayW]

/-! ## A3b: the self-read guard over several windows

The guard walks a statement list; a window set `Ws` replaces the single window `W` (`x ∈ Ws` for `x = W`): the
may-writes of the later statements and the reads of every expression are compared with every window of the
body (`readsViol_none_ws`). `combViol_tree` is the instance `Ws = [W]`. -/

theorem readsViol_none_ws (M A R : List BWin) (Ws : List BWin) (hA : ∀ x ∈ A, x ∈ Ws)
    (hR : ∀ r ∈ R, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0) : readsViol M A R = none := by
  unfold readsViol
  rw [List.findSome?_eq_none_iff]
  intro r hr
  rw [List.findSome?_eq_none_iff]
  intro x hx
  rw [BWin.subAll_nil_of_zero _ (hR r hr x (hA x hx))]
  rfl

theorem listCombViol_caseItems_ws (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (Ws : List BWin) (hW : W ∈ Ws) (M A dA : List BWin)
    (hA : ∀ x ∈ A, x ∈ Ws) (hdA : ∀ x ∈ dA, x ∈ Ws) :
    ∀ its : List (List Expr2 × Expr2), (∀ V ∈ Ws, CasesNoRdW wd V its) →
      CaseItem2.listCombViol wd M A dA none (caseItems tgt its) = none := by
  intro its
  induction its with
  | nil => intro _; simp [caseItems, CaseItem2.listCombViol]
  | cons it rest ih =>
      intro h
      obtain ⟨ps, e⟩ := it
      have h1 : ∀ r ∈ Expr2.listRdW wd ps, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0 :=
        fun r hr V hV => ((h V hV) (ps, e) (List.mem_cons_self ..)).1 r hr
      have h2 : ∀ r ∈ e.rdW wd, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0 :=
        fun r hr V hV => ((h V hV) (ps, e) (List.mem_cons_self ..)).2 r hr
      have hrest : ∀ V ∈ Ws, CasesNoRdW wd V rest :=
        fun V hV x hx => h V hV x (List.mem_cons_of_mem _ hx)
      simp only [caseItems, CaseItem2.listCombViol]
      have hall : ∀ x ∈ (Stmt2.blockingAssign tgt e).mayW wd ++
          CaseItem2.listMayW wd (caseItems tgt rest) ++ dA ++ A, x ∈ Ws := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with ((hx | hx) | hx) | hx
        · simp only [Stmt2.mayW, hm, List.mem_singleton] at hx; rw [hx]; exact hW
        · rw [mayW_caseItems wd tgt W hm rest x hx]; exact hW
        · exact hdA x hx
        · exact hA x hx
      rw [readsViol_none_ws M _ _ Ws hall h1]
      have hb : (Stmt2.blockingAssign tgt e).combViol wd M A = none := by
        simp only [Stmt2.combViol, hm, hr, List.append_nil]
        apply readsViol_none_ws M _ _ Ws
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with rfl | hx
          · exact hW
          · exact hA x hx
        · intro r hr'
          exact h2 r hr'
      rw [hb, ih hrest]
      rfl

theorem combViol_cases_ws (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) (Ws : List BWin) (hW : W ∈ Ws) (s dflt : Expr2)
    (its : List (List Expr2 × Expr2))
    (hs : ∀ r ∈ s.rdW wd, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0) (hits : ∀ V ∈ Ws, CasesNoRdW wd V its)
    (hd : ∀ r ∈ dflt.rdW wd, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0) (M A : List BWin)
    (hA : ∀ x ∈ A, x ∈ Ws) :
    (Stmt2.caseStmt s (caseItems tgt its).toArray (some (.blockingAssign tgt dflt)) .normal
      .none).combViol wd M A = none := by
  simp only [Stmt2.combViol]
  have hdm : ∀ x ∈ Stmt2.optMayW wd (some (.blockingAssign tgt dflt)), x ∈ Ws := by
    intro x hx
    simp only [Stmt2.optMayW, Stmt2.mayW, hm, List.mem_singleton] at hx
    rw [hx]; exact hW
  have hall : ∀ x ∈ CaseItem2.listMayW wd (caseItems tgt its) ++
      Stmt2.optMayW wd (some (.blockingAssign tgt dflt)) ++ A, x ∈ Ws := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · rw [mayW_caseItems wd tgt W hm its x hx]; exact hW
    · exact hdm x hx
    · exact hA x hx
  rw [readsViol_none_ws M _ _ Ws hall hs]
  have hdV : Stmt2.optCombViol wd M A (some (.blockingAssign tgt dflt)) = none := by
    simp only [Stmt2.optCombViol, Stmt2.combViol, hm, hr, List.append_nil]
    apply readsViol_none_ws M _ _ Ws
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact hW
      · exact hA x hx
    · intro r hr'
      exact hd r hr'
  rw [hdV]
  have := listCombViol_caseItems_ws wd tgt W hm hr Ws hW M A
    (Stmt2.optMayW wd (some (.blockingAssign tgt dflt))) hA hdm its hits
  rw [this]
  rfl

theorem listCombViol_append_ws (wd : String → Option Nat) (Ws : List BWin) :
    ∀ (l1 l2 : List Stmt2) (M : List BWin),
      (∀ A, (∀ x ∈ A, x ∈ Ws) → Stmt2.listCombViol wd M A l1 = none) →
      (∀ M' A, (∀ x ∈ A, x ∈ Ws) → Stmt2.listCombViol wd M' A l2 = none) →
      (∀ x ∈ Stmt2.listMayW wd l2, x ∈ Ws) →
      ∀ A, (∀ x ∈ A, x ∈ Ws) → Stmt2.listCombViol wd M A (l1 ++ l2) = none
  | [], l2, M, _, h2, _, A, hA => h2 M A hA
  | s :: r, l2, M, h1, h2, hm2, A, hA => by
      have hA' : ∀ x ∈ Stmt2.listMayW wd l2 ++ A, x ∈ Ws := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hm2 x hx
        · exact hA x hx
      have h1' := h1 (Stmt2.listMayW wd l2 ++ A) hA'
      simp only [Stmt2.listCombViol] at h1'
      have hs : s.combViol wd M (Stmt2.listMayW wd r ++ (Stmt2.listMayW wd l2 ++ A)) = none := by
        cases hh : s.combViol wd M (Stmt2.listMayW wd r ++ (Stmt2.listMayW wd l2 ++ A)) with
        | none => rfl
        | some v => rw [hh] at h1'; simp at h1'
      have hrest : ∀ A, (∀ x ∈ A, x ∈ Ws) →
          Stmt2.listCombViol wd (M ++ s.mustW wd) A r = none := by
        intro A' hA''
        have := h1 A' hA''
        simp only [Stmt2.listCombViol] at this
        cases hh : Stmt2.listCombViol wd (M ++ s.mustW wd) A' r with
        | none => rfl
        | some v => rw [hh] at this; simp at this
      have e : Stmt2.listMayW wd (r ++ l2) ++ A =
          Stmt2.listMayW wd r ++ (Stmt2.listMayW wd l2 ++ A) := by
        rw [listMayW_append, List.append_assoc]
      simp only [List.cons_append, Stmt2.listCombViol]
      rw [e, hs, listCombViol_append_ws wd Ws r l2 (M ++ s.mustW wd) hrest h2 hm2 A hA]
      rfl

theorem combViol_treeF (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) (Ws : List BWin) (hW : W ∈ Ws) :
    ∀ t : PTree, (∀ V ∈ Ws, t.noRdW wd V) → ∀ (M A : List BWin), (∀ x ∈ A, x ∈ Ws) →
      (t.toStmt tgt).combViol wd M A = none := by
  have hmayW : ∀ t : PTree, ∀ x ∈ (t.toStmt tgt).mayW wd, x ∈ Ws := fun t x hx => by
    rw [mayW_tree wd tgt W hm t x hx]; exact hW
  intro t
  induction t with
  | leaf e =>
      intro h M A hA
      simp only [PTree.toStmt, Stmt2.combViol, hm, hr, List.append_nil]
      apply readsViol_none_ws M _ _ Ws
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with rfl | hx
        · exact hW
        · exact hA x hx
      · intro r hr' V hV
        exact h V hV r hr'
  | ite c a b iha ihb =>
      intro h M A hA
      have hc : ∀ r ∈ c.rdW wd, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0 :=
        fun r hr V hV => (h V hV).1 r hr
      have ha : ∀ V ∈ Ws, a.noRdW wd V := fun V hV => (h V hV).2.1
      have hb : ∀ V ∈ Ws, b.noRdW wd V := fun V hV => (h V hV).2.2
      simp only [PTree.toStmt, Stmt2.combViol, Stmt2.optCombViol]
      rw [readsViol_none_ws M _ _ Ws _ hc, iha ha M A hA, ihb hb M A hA]
      · rfl
      · intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hmayW a x hx
        · exact hmayW b x (by simpa [PTree.toStmt, Stmt2.optMayW] using hx)
        · exact hA x hx
  | blk t iht =>
      intro h M A hA
      have h0 := iht h M A hA
      simp only [PTree.toStmt, Stmt2.combViol, Stmt2.listCombViol, Stmt2.listMayW, List.nil_append]
      rw [h0]
      rfl
  | cases s its dd =>
      intro h M A hA
      exact combViol_cases_ws wd tgt W hm hr Ws hW s dd its (fun r hr V hV => (h V hV).1 r hr)
        (fun V hV => (h V hV).2.1) (fun r hr V hV => (h V hV).2.2 r hr) M A hA
  | ovr c a b iha ihb =>
      intro h M A hA
      have hc : ∀ r ∈ c.rdW wd, ∀ V ∈ Ws, (BWin.inter r V).2.2 = 0 :=
        fun r hr V hV => (h V hV).1 r hr
      have ha : ∀ V ∈ Ws, a.noRdW wd V := fun V hV => (h V hV).2.1
      have hb : ∀ V ∈ Ws, b.noRdW wd V := fun V hV => (h V hV).2.2
      have hl1 : ∀ A', (∀ x ∈ A', x ∈ Ws) →
          Stmt2.listCombViol wd M A' (b.baseL (b.toStmt tgt)) = none := by
        intro A' hA'
        rw [listCombViol_baseL]
        exact ihb hb M A' hA'
      have hif : ∀ M' A', (∀ x ∈ A', x ∈ Ws) →
          Stmt2.listCombViol wd M' A' [Stmt2.ifStmt c (a.toStmt tgt) none] = none := by
        intro M' A' hA'
        simp only [Stmt2.listCombViol, Stmt2.combViol, Stmt2.optCombViol, Stmt2.listMayW,
          List.append_nil, List.nil_append]
        rw [readsViol_none_ws M' _ _ Ws _ hc, iha ha M' A' hA']
        · rfl
        · intro x hx
          simp only [List.mem_append, Stmt2.optMayW, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · exact hmayW a x hx
          · exact hA' x hx
      have hm2 : ∀ x ∈ Stmt2.listMayW wd [Stmt2.ifStmt c (a.toStmt tgt) none], x ∈ Ws := by
        intro x hx
        simp only [Stmt2.listMayW, Stmt2.mayW, Stmt2.optMayW, List.append_nil,
          List.mem_append, List.not_mem_nil, or_false] at hx
        exact hmayW a x hx
      simp only [PTree.toStmt, Stmt2.combViol, List.toList_toArray]
      exact listCombViol_append_ws wd Ws _ _ M hl1 hif hm2 A hA

theorem combViol_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) :
    ∀ t : PTree, t.noRdW wd W → ∀ (M A : List BWin), (∀ x ∈ A, x = W) →
      (t.toStmt tgt).combViol wd M A = none :=
  fun t h M A hA => combViol_treeF wd tgt W hm hr [W] (List.mem_singleton_self _) t
    (fun V hV => by rw [List.mem_singleton.mp hV]; exact h) M A
    (fun x hx => by rw [hA x hx]; exact List.mem_singleton_self _)

theorem combAdmits_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) (t : PTree) (h : t.noRdW wd W) :
    (t.toStmt tgt).combAdmits wd = true := by
  unfold Stmt2.combAdmits
  rw [combViol_tree wd tgt W hm hr t h [] [] (by simp)]
  rfl


/-! ## The Boolean semantics of the lowered equation (the netlist-view shape) -/

/-- The Boolean reading of a tree `case`: the first arm with a matching pattern (the comparison is at the
subject's width `ws`), else the default. -/
def caseBitAux (d : Design2) (env : String → Nat → Bool) (ws : Nat) (sv : Nat → Bool) :
    List (List Expr2 × Expr2) → Expr2 → Nat → Bool
  | [], dd, k => dd.xfBits d env k
  | (ps, e) :: rest, dd, k =>
      if ps.any (fun p => XF.eqv ws sv (p.xfBits d env)) then e.xfBits d env k
      else caseBitAux d env ws sv rest dd k

/-- Every pattern is as wide as the subject, every arm value as wide as the target. -/
def CasesXfOk (d : Design2) (w ws : Nat) (its : List (List Expr2 × Expr2)) : Prop :=
  ∀ it ∈ its, (∀ p ∈ it.1, p.xfWidth d = some ws) ∧ it.2.xfWidth d = some w

theorem anyGuard_xfWidth (d : Design2) (s : Expr2) (ws : Nat) (hs : s.xfWidth d = some ws) :
    ∀ ps : List Expr2, (∀ p ∈ ps, p.xfWidth d = some ws) →
      (Expr2.anyGuard .normal s ps).xfWidth d = some 1
  | [], _ => by
      simp [Expr2.anyGuard, Expr2.xfWidth, LVec.ofLogic, LVec.knownB, LVec.width, Logic.isKnown]
  | p :: ps, h => by
      have hp := h p (List.mem_cons_self ..)
      have ih := anyGuard_xfWidth d s ws hs ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [Expr2.anyGuard, Expr2.hitGuard, Expr2.xfWidth, hs, hp, ih, XF.same]

theorem anyGuard_xfBits (d : Design2) (env : String → Nat → Bool) (s : Expr2) (ws : Nat)
    (hs : s.xfWidth d = some ws) :
    ∀ ps : List Expr2, (∀ p ∈ ps, p.xfWidth d = some ws) → ∀ k,
      (Expr2.anyGuard .normal s ps).xfBits d env k =
        ps.any (fun p => XF.eqv ws (s.xfBits d env) (p.xfBits d env))
  | [], _, k => by
      cases k <;> simp [Expr2.anyGuard, Expr2.xfBits, LVec.ofLogic, LVec.boolAt]
  | p :: ps, h, k => by
      have hp := h p (List.mem_cons_self ..)
      have ih := anyGuard_xfBits d env s ws hs ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) k
      simp [Expr2.anyGuard, Expr2.hitGuard, Expr2.xfBits, hs, hp, ih]

theorem caseLow_xfWidth (d : Design2) (w ws : Nat) (s : Expr2) (hs : s.xfWidth d = some ws)
    (dd : Expr2) (hdd : dd.xfWidth d = some w) :
    ∀ its : List (List Expr2 × Expr2), CasesXfOk d w ws its →
      (caseLow w s its dd).xfWidth d = some w := by
  intro its
  induction its with
  | nil => intro _; simp [caseLow, Expr2.xfWidth, hdd]
  | cons it rest ih =>
      intro h
      obtain ⟨ps, e⟩ := it
      have h1 := (h (ps, e) (List.mem_cons_self ..)).1
      have h2 := (h (ps, e) (List.mem_cons_self ..)).2
      have hrest : CasesXfOk d w ws rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have ihr := ih hrest
      simp only [caseLow, Expr2.joinIte]
      split
      · simp [Expr2.xfWidth, h2]
      · have hg := anyGuard_xfWidth d s ws hs ps h1
        simp [Expr2.xfWidth, hg, ihr, h2, XF.same]

theorem caseLow_xfBits (d : Design2) (env : String → Nat → Bool) (w ws : Nat) (s : Expr2)
    (hs : s.xfWidth d = some ws) (dd : Expr2) (hdd : dd.xfWidth d = some w) :
    ∀ its : List (List Expr2 × Expr2), CasesXfOk d w ws its → ∀ k, k < w →
      (caseLow w s its dd).xfBits d env k = caseBitAux d env ws (s.xfBits d env) its dd k := by
  intro its
  induction its with
  | nil => intro _ k hk; simp [caseLow, caseBitAux, Expr2.xfBits, hdd, hk]
  | cons it rest ih =>
      intro h k hk
      obtain ⟨ps, e⟩ := it
      have h1 := (h (ps, e) (List.mem_cons_self ..)).1
      have h2 := (h (ps, e) (List.mem_cons_self ..)).2
      have hrest : CasesXfOk d w ws rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have ihr := ih hrest k hk
      have hrw : (caseLow w s rest dd).xfWidth d = some w := caseLow_xfWidth d w ws s hs dd hdd rest hrest
      simp only [caseLow, Expr2.joinIte]
      split
      · rename_i hsame
        have hab := Expr2.eq_of_same _ _ hsame
        rw [← hab] at ihr
        simp only [caseBitAux]
        have hA : (Expr2.resize w e).xfBits d env k = e.xfBits d env k := by simp [Expr2.xfBits, h2, hk]
        rw [hA] at ihr ⊢
        rw [ihr]
        split <;> rfl
      · have hg := anyGuard_xfWidth d s ws hs ps h1
        simp [Expr2.xfBits, hg, anyGuard_xfBits d env s ws hs ps h1, ihr, h2, hk, caseBitAux, XF.any]

/-- The Boolean semantics of the tree. -/
def PTree.bit (d : Design2) (env : String → Nat → Bool) : PTree → Nat → Bool
  | .leaf e => fun k => e.xfBits d env k
  | .ite c a b => fun k => if c.xfBits d env 0 then a.bit d env k else b.bit d env k
  | .blk t => t.bit d env
  | .cases s its dd => fun k => caseBitAux d env ((s.xfWidth d).getD 0) (s.xfBits d env) its dd k
  | .ovr c a b => fun k => if c.xfBits d env 0 then a.bit d env k else b.bit d env k

/-- Every leaf is `w` bits wide, every condition 1 bit, in the x-free fragment. -/
def PTree.xfOk (d : Design2) (w : Nat) : PTree → Prop
  | .leaf e => e.xfWidth d = some w
  | .ite c a b => c.xfWidth d = some 1 ∧ a.xfOk d w ∧ b.xfOk d w
  | .blk t => t.xfOk d w
  | .cases s its dd => ∃ ws, s.xfWidth d = some ws ∧ CasesXfOk d w ws its ∧ dd.xfWidth d = some w
  | .ovr c a b => c.xfWidth d = some 1 ∧ a.xfOk d w ∧ b.xfOk d w

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
  | ite c a b iha ihb | ovr c a b iha ihb =>
      intro ⟨hc, ha, hb⟩
      simp only [PTree.low, Expr2.joinIte]
      split
      · exact iha ha
      · simp [Expr2.xfWidth, ifGuard_xfWidth d c hc, iha ha, ihb hb, XF.same]
  | blk t iht => intro h; simpa [PTree.low] using iht h
  | cases s its dd =>
      intro ⟨ws, hs, hits, hdd⟩
      exact caseLow_xfWidth d w ws s hs dd hdd its hits

theorem low_xfBits (d : Design2) (env : String → Nat → Bool) (w : Nat) :
    ∀ t : PTree, t.xfOk d w → ∀ k, k < w → (t.low w).xfBits d env k = t.bit d env k := by
  intro t
  induction t with
  | leaf e => intro h k hk; simp [PTree.low, PTree.bit, Expr2.xfBits, PTree.xfOk] at *; simp [h, hk]
  | ite c a b iha ihb | ovr c a b iha ihb =>
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
  | cases s its dd =>
      intro ⟨ws, hs, hits, hdd⟩ k hk
      simp only [PTree.bit, hs, Option.getD_some]
      exact caseLow_xfBits d env w ws s hs dd hdd its hits k hk


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


theorem listRdW_of_reads (wd : String → Option Nat) (W : Win) (l : List Expr2)
    (hi : Expr2.listIdxFree l = true) (hr : ∀ r ∈ Expr2.listReads l, r.overlaps W = false) :
    ∀ x ∈ Expr2.listRdW wd l, (BWin.inter x W).2.2 = 0 :=
  (rdW_of_reads_aux wd W (Expr2.listSize l + 1)).2 l (Nat.lt_succ_self _) hi hr

theorem casesNoRdW_of_noRead (wd : String → Option Nat) (W : Win)
    (its : List (List Expr2 × Expr2)) (hi : CasesIdxFree its) (hr : CasesNoRead W its) :
    CasesNoRdW wd W its := fun it hit =>
  ⟨listRdW_of_reads wd W it.1 (hi it hit).1 (fun r h => ((hr it hit).1 r h).1),
    rdW_of_reads wd W it.2 (hi it hit).2 (fun r h => ((hr it hit).2 r h).1)⟩

/-- The window-level (`ReadWin`) non-overlap, which is what the summary's `noSelfRead` obligation gives,
implies the bit-level one the self-read guard walks. -/
theorem noRdW_of_noRead (wd : String → Option Nat) (W : Win) :
    ∀ t : PTree, t.idxFree → t.noRead W → t.noRdW wd W := by
  intro t
  induction t with
  | leaf e => exact fun hi h => rdW_of_reads wd W e hi (fun r hr => (h r hr).1)
  | ite c a b iha ihb | ovr c a b iha ihb =>
      intro ⟨hi, ha, hb⟩ ⟨hc, hna, hnb⟩
      exact ⟨rdW_of_reads wd W c hi (fun r hr => (hc r hr).1), iha ha hna, ihb hb hnb⟩
  | blk t iht => exact fun hi h => iht hi h
  | cases s its dd =>
      exact fun ⟨hi1, hi2, hi3⟩ ⟨hn1, hn2, hn3⟩ =>
        ⟨rdW_of_reads wd W s hi1 (fun r hr => (hn1 r hr).1), casesNoRdW_of_noRead wd W its hi2 hn2,
          rdW_of_reads wd W dd hi3 (fun r hr => (hn3 r hr).1)⟩

/-! ## S-C (generic form): the lowering of an instantiated tree -/

theorem lower_tree (d : Design2) (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hsw : tgt.symWin d = some W) (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (t : PTree)
    (hwf : t.wf d) (hix : t.idxFree) (hrd : t.noRdW wd W) (hno : t.noRead W) :
    Process2.lowerComb d (combGuardProc wd (t.toStmt tgt)) =
      some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2])) := by
  rw [combGuardProc_of_admits (combAdmits_tree wd tgt W hm hr t hrd)]
  have h1 : (t.toStmt tgt).symExec d [] = some [(W, t.low W.2.2)] :=
    symExec_tree d tgt W hsw t hwf hix hno [] (Or.inl rfl)
  simp [Process2.lowerComb, h1, selfReadFree_tree W W.2.2 t hno, SymState.toAssign, SymState.target,
    SymState.rhs]

/-- The final form: ONE non-overlap hypothesis (window level) and no index nodes. -/
theorem lower_tree' (d : Design2) (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hsw : tgt.symWin d = some W) (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (t : PTree)
    (hwf : t.wf d) (hix : t.idxFree) (hno : t.noRead W) :
    Process2.lowerComb d (combGuardProc wd (t.toStmt tgt)) =
      some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2])) :=
  lower_tree d wd tgt W hsw hm hr t hwf hix (noRdW_of_noRead wd W t hix hno) hno

/-! ## S1b gate a: the semantic core of a body that writes SEVERAL windows

A body is a list of segments, each a tree over its own target and window (`Seg`); the symbolic execution of the
whole body is the entries of its segments in order (`symExec_body`), the self-read guard admits it
(`combAdmits_body`), and its lowering is ONE assign of all the windows (`lower_body`). The tree executor runs over a
PREFIX of the windows written before (`symExec_treeF`): reads apart from every window of the body make
`symSubst` the identity (`symSubst_apartL`), `write_frame` appends, `join_frame` joins two branches that
both extend the same prefix (`Expr2.same_self`: the prefix entries agree). -/

mutual
theorem Expr2.same_self : ∀ (a : Expr2), a.same a = true
  | .lit v => by simp [Expr2.same]
  | .ident n => by simp [Expr2.same]
  | .unsupported k x => by simp [Expr2.same]
  | .unary o a => by simp [Expr2.same, Expr2.same_self a]
  | .resizeSigned w a => by simp [Expr2.same, Expr2.same_self a]
  | .squash2 a => by simp [Expr2.same, Expr2.same_self a]
  | .repl k a => by simp [Expr2.same, Expr2.same_self a]
  | .reduce o a => by simp [Expr2.same, Expr2.same_self a]
  | .resize w a => by simp [Expr2.same, Expr2.same_self a]
  | .binary o l r => by simp [Expr2.same, Expr2.same_self l, Expr2.same_self r]
  | .scmp o l r => by simp [Expr2.same, Expr2.same_self l, Expr2.same_self r]
  | .logical c l r => by simp [Expr2.same, Expr2.same_self l, Expr2.same_self r]
  | .index a i w => by simp [Expr2.same, Expr2.same_self a, Expr2.same_self i]
  | .ternary c t f => by simp [Expr2.same, Expr2.same_self c, Expr2.same_self t, Expr2.same_self f]
  | .slice a lo w => by simp [Expr2.same, Expr2.same_self a]
  | .concat ps => by simp [Expr2.same, Expr2.listSame_self ps.toList]
termination_by structural a => a

theorem Expr2.listSame_self : ∀ (l : List Expr2), Expr2.listSame l l = true
  | [] => by simp [Expr2.listSame]
  | e :: es => by simp [Expr2.listSame, Expr2.same_self e, Expr2.listSame_self es]
termination_by structural l => l
end

theorem joinIte_self (G E : Expr2) : Expr2.joinIte G E E = E := by
  simp [Expr2.joinIte, Expr2.same_self E]

/-- A state is the prefix `P` of the windows written so far, possibly followed by the entry of `W`. -/
def FrameS (P : SymState) (W : Win) (S : SymState) : Prop := S = P ∨ ∃ E0, S = P ++ [(W, E0)]

/-- The prefix and the next window are non-empty and pairwise disjoint. -/
def PrefixOk (P : SymState) (W : Win) : Prop :=
  0 < W.2.2 ∧ (∀ x ∈ P, 0 < x.1.2.2) ∧ Win.allDisjoint (P.map Prod.fst ++ [W]) = true

theorem PrefixOk.overlaps {P : SymState} {W : Win} (h : PrefixOk P W) :
    ∀ x ∈ P, Win.overlaps x.1 W = false := by
  intro x hx
  have := (Win.allDisjoint_iff _).1 h.2.2
  rw [List.pairwise_append] at this
  exact this.2.2 x.1 (List.mem_map_of_mem hx) W (List.mem_singleton_self _)

theorem overlaps_self_true (W : Win) (h : 0 < W.2.2) : Win.overlaps W W = true := by
  obtain ⟨n, lo, w⟩ := W
  have h' : 0 < w := h
  simp only [Win.overlaps_eq_true]
  refine ⟨trivial, ?_, ?_⟩ <;> omega

theorem PrefixOk.ne {P : SymState} {W : Win} (h : PrefixOk P W) : ∀ x ∈ P, x.1 ≠ W := by
  intro x hx hxW
  have := h.overlaps x hx
  rw [hxW, overlaps_self_true W h.1] at this
  exact Bool.noConfusion this

theorem PrefixOk.nodup {P : SymState} {W : Win} (h : PrefixOk P W) : (P.map Prod.fst).Nodup := by
  have hp := (Win.allDisjoint_iff _).1 h.2.2
  rw [List.pairwise_append] at hp
  refine List.Pairwise.imp_of_mem ?_ hp.1
  intro a b ha hb hab hEq
  subst hEq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  rw [overlaps_self_true _ (h.2.1 x hx)] at hab
  exact Bool.noConfusion hab

theorem PrefixOk.contains {P : SymState} {W : Win} (h : PrefixOk P W) :
    ∀ x ∈ P, Win.contains x.1 W = false := by
  intro x hx
  cases hc : Win.contains x.1 W
  · rfl
  have hc' := hc
  have ho := h.overlaps x hx
  rw [Win.contains_iff] at hc'
  obtain ⟨⟨n, l, v⟩, E⟩ := x
  obtain ⟨n', l', w'⟩ := W
  have hw := h.1
  simp only [Win.overlaps_eq_false] at ho
  simp only at hc' hw
  obtain ⟨h1, h2, h3⟩ := hc'
  subst h1
  rcases ho with ho | ho | ho
  · exact (ho rfl).elim
  · omega
  · omega

theorem write_frame (P : SymState) (W : Win) (E : Expr2) (hP : PrefixOk P W) (S : SymState)
    (hS : FrameS P W S) : S.write W E = some (P ++ [(W, E)]) := by
  have hne : ∀ x ∈ P, (x.1 == W) = false := fun x hx => by simpa using hP.ne x hx
  have hcov : P.findCover W = none := by
    simp only [SymState.findCover, List.find?_eq_none]
    intro x hx
    simp [hP.contains x hx]
  have hovl : P.overlapsAny W = false := by
    simp only [SymState.overlapsAny, List.any_eq_false]
    intro x hx
    simp [hP.overlaps x hx]
  rcases hS with hS | ⟨E0, hS⟩
  · have hany : P.any (fun e => e.1 == W) = false := by
      simp only [List.any_eq_false]
      intro x hx
      simp [hne x hx]
    rw [hS]
    simp [SymState.write, hany, hcov, hovl]
  · have hmap : (P.map fun e => if e.1 == W then (W, E) else e) = P := by
      rw [List.map_congr_left (g := id) (fun x hx => by simp [hne x hx])]
      exact List.map_id P
    have hmap' : (P.map fun e => if e.1 = W then (W, E) else e) = P := by
      rw [List.map_congr_left (g := id) (fun x hx => by simp [hP.ne x hx])]
      exact List.map_id P
    rw [hS]
    simp [SymState.write, hmap, hmap']

theorem find_of_nodup : ∀ (P : SymState), (P.map Prod.fst).Nodup → ∀ x ∈ P,
    P.find? (fun e => e.1 == x.1) = some x
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: ys, hnd, x, hx => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp [List.find?_cons]
      · have hne : y.1 ≠ x.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hx')
        simp [List.find?_cons, hne, find_of_nodup ys hnd.2 x hx']

theorem join_frame (G a b : Expr2) (P : SymState) (W : Win) (hP : PrefixOk P W) :
    SymState.join G (P ++ [(W, a)]) (P ++ [(W, b)]) = some (P ++ [(W, Expr2.joinIte G a b)]) := by
  have hnd := hP.nodup
  have hjw : SymState.joinWins (P ++ [(W, a)]) (P ++ [(W, b)]) = P.map Prod.fst ++ [W] := by
    simp only [SymState.joinWins, List.map_append, List.map_cons, List.map_nil]
    have : ((P.map Prod.fst ++ [W]).filter
        fun V => !((P ++ [(W, a)]).any fun e => e.1 == V)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro V hV
      have : (P ++ [(W, a)]).any (fun e => e.1 == V) = true := by
        simp only [List.any_eq_true]
        rcases List.mem_append.mp hV with hV | hV
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hV
          exact ⟨x, List.mem_append_left _ hx, by simp⟩
        · rw [List.mem_singleton] at hV
          exact ⟨(W, a), List.mem_append_right _ (List.mem_singleton_self _), by simp [hV]⟩
      simp [this]
    rw [this, List.append_nil]
  have hlk : ∀ (c : Expr2) (x : Win × Expr2), x ∈ P →
      SymState.lookupOr (P ++ [(W, c)]) x.1 = x.2 := by
    intro c x hx
    have := find_of_nodup P hnd x hx
    simp [SymState.lookupOr, SymState.findWin, List.find?_append, this]
  have hlW : ∀ c : Expr2, SymState.lookupOr (P ++ [(W, c)]) W = c := by
    intro c
    have hn : P.find? (fun e => e.1 == W) = none := by
      rw [List.find?_eq_none]
      intro x hx
      simp [hP.ne x hx]
    simp [SymState.lookupOr, SymState.findWin, List.find?_append, hn]
  simp only [SymState.join, hjw, hP.2.2, if_true]
  congr 1
  rw [List.map_append]
  congr 1
  · rw [List.map_map]
    rw [List.map_congr_left (g := id) (fun x hx => by
      simp only [Function.comp_apply, id]
      rw [hlk a x hx, hlk b x hx, joinIte_self])]
    exact List.map_id P
  · simp [hlW]


/-! ### The tree executor over a prefix -/

theorem frameS_mem {P : SymState} {W : Win} {Ws : List Win} (hWsP : ∀ x ∈ P, x.1 ∈ Ws) (hW : W ∈ Ws)
    {S : SymState} (hS : FrameS P W S) : ∀ x ∈ S, x.1 ∈ Ws := by
  intro x hx
  rcases hS with rfl | ⟨E0, rfl⟩
  · exact hWsP x hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact hWsP x hx
    · rw [List.mem_singleton.mp hx]; exact hW

theorem symExec_caseItemsF (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W)
    (Ws : List Win) (P S : SymState) (hP : PrefixOk P W) (hF : FrameS P W S)
    (hSW : ∀ x ∈ S, x.1 ∈ Ws) (s dflt : Expr2) :
    ∀ its : List (List Expr2 × Expr2), CasesWf d its → CasesIdxFree its →
      (∀ V ∈ Ws, CasesNoRead V its) →
      CaseItem2.symExecList d S s .normal (P ++ [(W, .resize W.2.2 dflt)]) (caseItems tgt its) =
        some (P ++ [(W, caseLow W.2.2 s its dflt)]) := by
  have wf := fun E => write_frame P W E hP S hF
  have jf := fun G a b => join_frame G a b P W hP
  intro its
  induction its with
  | nil => intro _ _ _; simp [caseItems, CaseItem2.symExecList, caseLow]
  | cons it rest ih =>
      intro h hi hn
      obtain ⟨ps, e⟩ := it
      have hps := (h (ps, e) (List.mem_cons_self ..)).1
      have he := (h (ps, e) (List.mem_cons_self ..)).2
      have hips := (hi (ps, e) (List.mem_cons_self ..)).1
      have hie := (hi (ps, e) (List.mem_cons_self ..)).2
      have hnps : ∀ r ∈ Expr2.listReads ps, ∀ x ∈ S, r.apart x.1 :=
        fun r hr x hx => ((hn x.1 (hSW x hx)) (ps, e) (List.mem_cons_self ..)).1 r hr
      have hne : ∀ r ∈ e.reads, ∀ x ∈ S, r.apart x.1 :=
        fun r hr x hx => ((hn x.1 (hSW x hx)) (ps, e) (List.mem_cons_self ..)).2 r hr
      have hrest : CasesWf d rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hirest : CasesIdxFree rest := fun x hx => hi x (List.mem_cons_of_mem _ hx)
      have hnrest : ∀ V ∈ Ws, CasesNoRead V rest :=
        fun V hV x hx => hn V hV x (List.mem_cons_of_mem _ hx)
      have hw1 : Stmt2.symExec d S (.blockingAssign tgt e) = some (P ++ [(W, .resize W.2.2 e)]) := by
        simp [Stmt2.symExec, he, symSubst_apartL d S e he hie hne, hsw, wf]
      simp [caseItems, CaseItem2.symExecList, CaseItem2.symArm, hps,
        listSymSubst_apartL d S ps hps hips hnps, hw1, ih hrest hirest hnrest, jf, caseLow]

theorem symExec_casesF (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W)
    (Ws : List Win) (P S : SymState) (hP : PrefixOk P W) (hF : FrameS P W S)
    (hSW : ∀ x ∈ S, x.1 ∈ Ws)
    (s dflt : Expr2) (its : List (List Expr2 × Expr2)) (hs : s.wfB d = true)
    (hsi : s.idxFree = true) (hsn : ∀ r ∈ s.reads, ∀ V ∈ Ws, r.apart V)
    (hd : dflt.wfB d = true) (hdi : dflt.idxFree = true) (hdn : ∀ r ∈ dflt.reads, ∀ V ∈ Ws, r.apart V)
    (hits : CasesWf d its) (hii : CasesIdxFree its) (hin : ∀ V ∈ Ws, CasesNoRead V its) :
    (Stmt2.caseStmt s (caseItems tgt its).toArray (some (.blockingAssign tgt dflt)) .normal .none).symExec
        d S = some (P ++ [(W, caseLow W.2.2 s its dflt)]) := by
  have wf := fun E => write_frame P W E hP S hF
  have hsn' : ∀ r ∈ s.reads, ∀ x ∈ S, r.apart x.1 := fun r hr x hx => hsn r hr x.1 (hSW x hx)
  have hdn' : ∀ r ∈ dflt.reads, ∀ x ∈ S, r.apart x.1 := fun r hr x hx => hdn r hr x.1 (hSW x hx)
  have h1 : Stmt2.symExecOpt d S (some (.blockingAssign tgt dflt)) =
      some (P ++ [(W, .resize W.2.2 dflt)]) := by
    simp [Stmt2.symExecOpt, Stmt2.symExec, hd, symSubst_apartL d S dflt hd hdi hdn', hsw, wf]
  simp only [Stmt2.symExec, hs, if_true, symSubst_apartL d S s hs hsi hsn', Option.bind_some, h1]
  exact symExec_caseItemsF d tgt W hsw Ws P S hP hF hSW s dflt its hits hii hin

theorem symExec_treeF (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W)
    (Ws : List Win) (P : SymState) (hP : PrefixOk P W) (hWsP : ∀ x ∈ P, x.1 ∈ Ws) (hW : W ∈ Ws) :
    ∀ t : PTree, t.wf d → t.idxFree → (∀ V ∈ Ws, t.noRead V) → ∀ S : SymState, FrameS P W S →
      (t.toStmt tgt).symExec d S = some (P ++ [(W, t.low W.2.2)]) := by
  intro t
  induction t with
  | leaf e =>
      intro (h1 : e.wfB d = true) (hi : e.idxFree = true) (hn : ∀ V ∈ Ws, ∀ r ∈ e.reads, r.apart V) S hS
      have hSW := frameS_mem hWsP hW hS
      have hap : ∀ r ∈ e.reads, ∀ x ∈ S, r.apart x.1 := fun r hr x hx => hn x.1 (hSW x hx) r hr
      have wf := fun E => write_frame P W E hP S hS
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, h1, symSubst_apartL d S e h1 hi hap, hsw, wf]
  | ite c a b iha ihb =>
      intro ⟨h1, ha, hb⟩ ⟨hic, hia, hib⟩ hn S hS
      have hSW := frameS_mem hWsP hW hS
      have hnc : ∀ r ∈ c.reads, ∀ x ∈ S, r.apart x.1 :=
        fun r hr x hx => (hn x.1 (hSW x hx)).1 r hr
      have hna : ∀ V ∈ Ws, a.noRead V := fun V hV => (hn V hV).2.1
      have hnb : ∀ V ∈ Ws, b.noRead V := fun V hV => (hn V hV).2.2
      have jf := fun G a b => join_frame G a b P W hP
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecOpt, h1,
        symSubst_apartL d S c h1 hic hnc, iha ha hia hna S hS, ihb hb hib hnb S hS, jf]
  | blk t iht =>
      intro (ht : t.wf d) (hit : t.idxFree) (hnt : ∀ V ∈ Ws, t.noRead V) S hS
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecList, iht ht hit hnt S hS]
  | cases s its dd =>
      intro ⟨hs, hits, hdd⟩ ⟨hsi, hii, hdi⟩ hn S hS
      have hSW := frameS_mem hWsP hW hS
      exact symExec_casesF d tgt W hsw Ws P S hP hS hSW s dd its hs hsi
        (fun r hr V hV => (hn V hV).1 r hr) hdd hdi (fun r hr V hV => (hn V hV).2.2 r hr)
        hits hii (fun V hV => (hn V hV).2.1)
  | ovr c a b iha ihb =>
      intro ⟨h1, ha, hb⟩ ⟨hic, hia, hib⟩ hn S hS
      have hSW := frameS_mem hWsP hW hS
      have hnc : ∀ r ∈ c.reads, ∀ V ∈ Ws, r.apart V := fun r hr V hV => (hn V hV).1 r hr
      have hna : ∀ V ∈ Ws, a.noRead V := fun V hV => (hn V hV).2.1
      have hnb : ∀ V ∈ Ws, b.noRead V := fun V hV => (hn V hV).2.2
      have hbase := symExecList_baseL d S b tgt _ (ihb hb hib hnb S hS)
      have hS1 : FrameS P W (P ++ [(W, b.low W.2.2)]) := Or.inr ⟨_, rfl⟩
      have hSW1 := frameS_mem hWsP hW hS1
      have jf := fun G a b => join_frame G a b P W hP
      simp only [PTree.toStmt, Stmt2.symExec]
      rw [symExecList_append, hbase]
      simp [Stmt2.symExecList, Stmt2.symExec, Stmt2.symExecOpt, h1,
        symSubst_apartL d _ c h1 hic (fun r hr x hx => hnc r hr x.1 (hSW1 x hx)),
        iha ha hia hna _ hS1, jf, PTree.low]


/-! ### A body of several windows -/

/-- One segment of a body: a tree over its own target and window. -/
structure Seg where
  tgt : Lhs2
  W : Win
  t : PTree

/-- The statements of a segment (the flattened block of an override tree, else the one statement). -/
def Seg.stmts (sg : Seg) : List Stmt2 := sg.t.baseL (sg.t.toStmt sg.tgt)

def bodyStmts : List Seg → List Stmt2
  | [] => []
  | sg :: rest => sg.stmts ++ bodyStmts rest

/-- The body: the statements of its segments in order. -/
def bodyStmt (segs : List Seg) : Stmt2 := .block (bodyStmts segs).toArray

def bodyWins (segs : List Seg) : List Win := segs.map Seg.W

def bodyEntries (segs : List Seg) : SymState := segs.map fun sg => (sg.W, sg.t.low sg.W.2.2)

/-- One segment's static facts at the design `d`, against the windows `Ws` of the whole body. -/
structure SegOk (d : Design2) (Ws : List Win) (sg : Seg) : Prop where
  sw : sg.tgt.symWin d = some sg.W
  wf : sg.t.wf d
  ix : sg.t.idxFree
  nr : ∀ V ∈ Ws, sg.t.noRead V
  mem : sg.W ∈ Ws

theorem symExecList_body (d : Design2) (Ws : List Win) (hposWs : ∀ V ∈ Ws, 0 < V.2.2) :
    ∀ (segs : List Seg) (P : SymState), (∀ sg ∈ segs, SegOk d Ws sg) →
      Win.allDisjoint (P.map Prod.fst ++ bodyWins segs) = true → (∀ x ∈ P, x.1 ∈ Ws) →
      Stmt2.symExecList d P (bodyStmts segs) = some (P ++ bodyEntries segs)
  | [], P, _, _, _ => by simp [bodyStmts, Stmt2.symExecList, bodyEntries]
  | sg :: rest, P, hs, hdisj, hP => by
      have hsg := hs sg (List.mem_cons_self ..)
      have hrest : ∀ s ∈ rest, SegOk d Ws s := fun s hs' => hs s (List.mem_cons_of_mem _ hs')
      have hPW : PrefixOk P sg.W := by
        refine ⟨hposWs _ hsg.mem, fun x hx => hposWs _ (hP x hx), ?_⟩
        have hpw := (Win.allDisjoint_iff _).1 hdisj
        rw [Win.allDisjoint_iff]
        refine hpw.sublist (List.Sublist.append (List.Sublist.refl _) ?_)
        simp [bodyWins]
      have htree := symExec_treeF d sg.tgt sg.W hsg.sw Ws P hPW hP hsg.mem sg.t hsg.wf hsg.ix hsg.nr
        P (Or.inl rfl)
      have hstmts := symExecList_baseL d P sg.t sg.tgt _ htree
      have hP' : ∀ x ∈ P ++ [(sg.W, sg.t.low sg.W.2.2)], x.1 ∈ Ws := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hP x hx
        · rw [List.mem_singleton.mp hx]; exact hsg.mem
      have hdisj' : Win.allDisjoint ((P ++ [(sg.W, sg.t.low sg.W.2.2)]).map Prod.fst ++ bodyWins rest)
          = true := by
        have : (P ++ [(sg.W, sg.t.low sg.W.2.2)]).map Prod.fst ++ bodyWins rest =
            P.map Prod.fst ++ bodyWins (sg :: rest) := by
          simp [bodyWins]
        rw [this]; exact hdisj
      have ih := symExecList_body d Ws hposWs rest (P ++ [(sg.W, sg.t.low sg.W.2.2)]) hrest hdisj' hP'
      simp only [bodyStmts, symExecList_append]
      rw [show Stmt2.symExecList d P sg.stmts = some (P ++ [(sg.W, sg.t.low sg.W.2.2)]) from hstmts]
      simp [ih, bodyEntries, List.append_assoc]

theorem symExec_body (d : Design2) (Ws : List Win) (hposWs : ∀ V ∈ Ws, 0 < V.2.2) (segs : List Seg)
    (hs : ∀ sg ∈ segs, SegOk d Ws sg) (hdisj : Win.allDisjoint (bodyWins segs) = true) :
    (bodyStmt segs).symExec d [] = some (bodyEntries segs) := by
  have := symExecList_body d Ws hposWs segs [] hs (by simpa using hdisj) (by simp)
  simpa [bodyStmt, Stmt2.symExec] using this

theorem mem_listReads {r : ReadWin} : ∀ {L : List Expr2}, r ∈ Expr2.listReads L → ∃ e ∈ L, r ∈ e.reads
  | [], h => by simp [Expr2.listReads] at h
  | e :: es, h => by
      simp only [Expr2.listReads, List.mem_append] at h
      rcases h with h | h
      · exact ⟨e, List.mem_cons_self .., h⟩
      · obtain ⟨e', he', h'⟩ := mem_listReads h
        exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

theorem selfReadFree_body (Ws : List Win) (segs : List Seg)
    (hnr : ∀ sg ∈ segs, ∀ V ∈ Ws, sg.t.noRead V) (hmem : ∀ sg ∈ segs, sg.W ∈ Ws) :
    SymState.selfReadFree (bodyEntries segs) = true := by
  simp only [SymState.selfReadFree, List.all_eq_true, Bool.not_eq_true']
  intro r hr V hV
  obtain ⟨e, he, hre⟩ := mem_listReads hr
  obtain ⟨⟨W1, E1⟩, hm1, rfl⟩ := List.mem_map.mp he
  obtain ⟨sg, hsg, hsg'⟩ := List.mem_map.mp hm1
  obtain ⟨⟨W2, E2⟩, hm2, rfl⟩ := List.mem_map.mp hV
  obtain ⟨sg2, hsg2, hsg2'⟩ := List.mem_map.mp hm2
  simp only [Prod.mk.injEq] at hsg' hsg2'
  rw [← hsg'.2] at hre
  rw [← hsg2'.1]
  exact low_reads sg2.W sg.W.2.2 sg.t (hnr sg hsg sg2.W (hmem sg2 hsg2)) r hre



theorem listMayW_bodyStmts (wd : String → Option Nat) (Ws : List BWin) :
    ∀ segs : List Seg, (∀ sg ∈ segs, sg.tgt.mayW wd = [sg.W] ∧ sg.W ∈ Ws) →
      ∀ x ∈ Stmt2.listMayW wd (bodyStmts segs), x ∈ Ws
  | [], _ => by intro x hx; simp [bodyStmts, Stmt2.listMayW] at hx
  | sg :: rest, h => by
      intro x hx
      simp only [bodyStmts, listMayW_append, List.mem_append] at hx
      rcases hx with hx | hx
      · have hsg := h sg (List.mem_cons_self ..)
        simp only [Seg.stmts, listMayW_baseL] at hx
        rw [mayW_tree wd sg.tgt sg.W hsg.1 sg.t x hx]
        exact hsg.2
      · exact listMayW_bodyStmts wd Ws rest (fun s hs => h s (List.mem_cons_of_mem _ hs)) x hx

theorem listCombViol_body (wd : String → Option Nat) (Ws : List BWin) :
    ∀ segs : List Seg,
      (∀ sg ∈ segs, sg.tgt.mayW wd = [sg.W] ∧ sg.tgt.rdW wd = [] ∧ sg.W ∈ Ws ∧
        ∀ V ∈ Ws, sg.t.noRdW wd V) →
      ∀ (M A : List BWin), (∀ x ∈ A, x ∈ Ws) →
        Stmt2.listCombViol wd M A (bodyStmts segs) = none
  | [], _ => by intro M A _; simp [bodyStmts, Stmt2.listCombViol]
  | sg :: rest, h => by
      intro M A hA
      have hsg := h sg (List.mem_cons_self ..)
      have hrest : ∀ s ∈ rest, s.tgt.mayW wd = [s.W] ∧ s.tgt.rdW wd = [] ∧ s.W ∈ Ws ∧
          ∀ V ∈ Ws, s.t.noRdW wd V := fun s hs => h s (List.mem_cons_of_mem _ hs)
      have hl1 : ∀ A', (∀ x ∈ A', x ∈ Ws) → Stmt2.listCombViol wd M A' sg.stmts = none := by
        intro A' hA'
        simp only [Seg.stmts]
        rw [listCombViol_baseL]
        exact combViol_treeF wd sg.tgt sg.W hsg.1 hsg.2.1 Ws hsg.2.2.1 sg.t hsg.2.2.2 M A' hA'
      have h2 : ∀ M' A', (∀ x ∈ A', x ∈ Ws) →
          Stmt2.listCombViol wd M' A' (bodyStmts rest) = none :=
        fun M' A' hA' => listCombViol_body wd Ws rest hrest M' A' hA'
      have hm2 := listMayW_bodyStmts wd Ws rest (fun s hs => ⟨(hrest s hs).1, (hrest s hs).2.2.1⟩)
      simp only [bodyStmts]
      exact listCombViol_append_ws wd Ws _ _ M hl1 h2 hm2 A hA

/-- Everything `lower_body` needs of a body. -/
structure BodyOk (d : Design2) (wd : String → Option Nat) (segs : List Seg) : Prop where
  pos : ∀ V ∈ bodyWins segs, 0 < V.2.2
  disj : Win.allDisjoint (bodyWins segs) = true
  seg : ∀ sg ∈ segs, SegOk d (bodyWins segs) sg
  mw : ∀ sg ∈ segs, sg.tgt.mayW wd = [sg.W]
  rw : ∀ sg ∈ segs, sg.tgt.rdW wd = []

theorem combAdmits_body (d : Design2) (wd : String → Option Nat) (segs : List Seg)
    (hok : BodyOk d wd segs) : (bodyStmt segs).combAdmits wd = true := by
  have hl := listCombViol_body wd (bodyWins segs) segs (fun sg hsg =>
    ⟨hok.mw sg hsg, hok.rw sg hsg, (hok.seg sg hsg).mem,
      fun V hV => noRdW_of_noRead wd V sg.t (hok.seg sg hsg).ix ((hok.seg sg hsg).nr V hV)⟩) [] []
    (by simp)
  unfold Stmt2.combAdmits
  simp only [bodyStmt, Stmt2.combViol, List.toList_toArray]
  rw [hl]
  rfl

/-- **The lowering of a body that writes several windows IS the assign of all of them.** -/
theorem lower_body_plain (d : Design2) (segs : List Seg) (Ws : List Win)
    (hpos : ∀ V ∈ Ws, 0 < V.2.2) (hdisj : Win.allDisjoint (bodyWins segs) = true)
    (hs : ∀ sg ∈ segs, SegOk d Ws sg) (hWs : ∀ sg ∈ segs, ∀ V ∈ Ws, sg.t.noRead V) :
    Process2.lowerComb d (.alwaysComb (bodyStmt segs)) =
      some (.assign (.concat ((bodyWins segs).map Win.lhs))
        (.concat (segs.map fun sg => sg.t.low sg.W.2.2).toArray)) := by
  have h1 := symExec_body d Ws hpos segs hs hdisj
  have hsrf := selfReadFree_body Ws segs hWs (fun sg hsg => (hs sg hsg).mem)
  simp only [Process2.lowerComb, h1, Option.bind_some, hsrf, if_true]
  simp [SymState.toAssign, SymState.target, SymState.rhs, bodyEntries, bodyWins, List.map_map,
    Function.comp_def]

/-- … and the guard admits the body, so the instantiated process IS the body. -/
theorem lower_body (d : Design2) (wd : String → Option Nat) (segs : List Seg)
    (hok : BodyOk d wd segs) :
    Process2.lowerComb d (combGuardProc wd (bodyStmt segs)) =
      some (.assign (.concat ((bodyWins segs).map Win.lhs))
        (.concat (segs.map fun sg => sg.t.low sg.W.2.2).toArray)) := by
  rw [combGuardProc_of_admits (combAdmits_body d wd segs hok)]
  exact lower_body_plain d segs (bodyWins segs) hok.pos hok.disj hok.seg
    (fun sg hsg => (hok.seg sg hsg).nr)

theorem drvWins_bodyStmts : ∀ segs : List Seg, ∀ x ∈ Stmt2.drvWinsList (bodyStmts segs),
    ∃ sg ∈ segs, x ∈ sg.tgt.drvWins
  | [] => by intro x hx; simp [bodyStmts, Stmt2.drvWinsList] at hx
  | sg :: rest => by
      intro x hx
      simp only [bodyStmts, drvWinsList_append, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ⟨sg, List.mem_cons_self .., drvWins_tree sg.tgt sg.t x (drvWinsList_baseL sg.tgt sg.t x hx)⟩
      · obtain ⟨s, hs, hxs⟩ := drvWins_bodyStmts rest x hx
        exact ⟨s, List.mem_cons_of_mem _ hs, hxs⟩

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

/-- info: 'LeanModels.Sv.CombProc.drvWins_tree' depends on axioms: [propext, Quot.sound] -/
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

/-- info: 'LeanModels.Sv.CombProc.symSubst_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_apart

/-- info: 'LeanModels.Sv.CombProc.listSymSubst_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms listSymSubst_apart

/-- info: 'LeanModels.Sv.CombProc.write_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms write_single

/-- info: 'LeanModels.Sv.CombProc.join_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms join_single

/-- info: 'LeanModels.Sv.CombProc.symExecList_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExecList_append

/-- info: 'LeanModels.Sv.CombProc.symExecList_baseL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExecList_baseL

/-- info: 'LeanModels.Sv.CombProc.drvWinsList_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms drvWinsList_append

/-- info: 'LeanModels.Sv.CombProc.drvWinsList_baseL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms drvWinsList_baseL

/-- info: 'LeanModels.Sv.CombProc.listMayW_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms listMayW_append

/-- info: 'LeanModels.Sv.CombProc.listMayW_baseL' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms listMayW_baseL

/-- info: 'LeanModels.Sv.CombProc.listCombViol_baseL' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms listCombViol_baseL

/-- info: 'LeanModels.Sv.CombProc.apart_contains_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms apart_contains_false

/-- info: 'LeanModels.Sv.CombProc.symSubst_apartL_ident' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_apartL_ident

/-- info: 'LeanModels.Sv.CombProc.symSubst_apartL_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_apartL_slice

/-- info: 'LeanModels.Sv.CombProc.symSubst_apartL_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_apartL_aux

/-- info: 'LeanModels.Sv.CombProc.symSubst_apartL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symSubst_apartL

/-- info: 'LeanModels.Sv.CombProc.listSymSubst_apartL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms listSymSubst_apartL

/-- info: 'LeanModels.Sv.CombProc.Expr2.same_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Expr2.same_self

/-- info: 'LeanModels.Sv.CombProc.Expr2.listSame_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Expr2.listSame_self

/-- info: 'LeanModels.Sv.CombProc.joinIte_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joinIte_self

/-- info: 'LeanModels.Sv.CombProc.PrefixOk.overlaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixOk.overlaps

/-- info: 'LeanModels.Sv.CombProc.overlaps_self_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overlaps_self_true

/-- info: 'LeanModels.Sv.CombProc.PrefixOk.ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixOk.ne

/-- info: 'LeanModels.Sv.CombProc.PrefixOk.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixOk.nodup

/-- info: 'LeanModels.Sv.CombProc.PrefixOk.contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixOk.contains

/-- info: 'LeanModels.Sv.CombProc.write_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms write_frame

/-- info: 'LeanModels.Sv.CombProc.find_of_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms find_of_nodup

/-- info: 'LeanModels.Sv.CombProc.join_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms join_frame

/-- info: 'LeanModels.Sv.CombProc.frameS_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms frameS_mem

/-- info: 'LeanModels.Sv.CombProc.symExec_caseItemsF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExec_caseItemsF

/-- info: 'LeanModels.Sv.CombProc.symExec_casesF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExec_casesF

/-- info: 'LeanModels.Sv.CombProc.symExec_treeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExec_treeF

/-- info: 'LeanModels.Sv.CombProc.symExecList_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExecList_body

/-- info: 'LeanModels.Sv.CombProc.symExec_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symExec_body

/-- info: 'LeanModels.Sv.CombProc.mem_listReads' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_listReads

/-- info: 'LeanModels.Sv.CombProc.selfReadFree_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selfReadFree_body

/-- info: 'LeanModels.Sv.CombProc.readsViol_none_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readsViol_none_ws

/-- info: 'LeanModels.Sv.CombProc.listCombViol_caseItems_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms listCombViol_caseItems_ws

/-- info: 'LeanModels.Sv.CombProc.combViol_cases_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combViol_cases_ws

/-- info: 'LeanModels.Sv.CombProc.listCombViol_append_ws' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms listCombViol_append_ws

/-- info: 'LeanModels.Sv.CombProc.combViol_treeF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combViol_treeF

/-- info: 'LeanModels.Sv.CombProc.listMayW_bodyStmts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms listMayW_bodyStmts

/-- info: 'LeanModels.Sv.CombProc.listCombViol_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms listCombViol_body

/-- info: 'LeanModels.Sv.CombProc.combAdmits_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combAdmits_body

/-- info: 'LeanModels.Sv.CombProc.lower_body_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_body_plain

/-- info: 'LeanModels.Sv.CombProc.lower_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_body

/-- info: 'LeanModels.Sv.CombProc.drvWins_bodyStmts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms drvWins_bodyStmts

end CombProc
end LeanModels.Sv
