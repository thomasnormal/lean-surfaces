import LeanModels.Sv.PinAxioms
import LeanModels.Sv.CombProcLower
import LeanModels.Sv.CombEqThm

/-!
# `always_comb` bodies in the `sv_comb` fragment, stage 5: the skeleton of a procedural site (WP-G, G2.2, R4)

`sv_equations` states, for every assign of the netlist, the pointwise Boolean equation of its right-hand side
(`Sk.bit`: the gate structure of the SystemVerilog is preserved). A procedural site `always_comb if (c) t = A;
else t = B;` has a right-hand side with a choice in it, so its skeleton `PSk` has an `ite` node:

    st.boolAt n (lo + k) = if (c bit 0) = true then A bit k else B bit k

This file defines the skeleton of a template body (`stmtSk`, consuming the site's flat read list exactly like
`skT` / `skRhs` do, with the counts `cnt` / `rcnt`), proves that it is the instantiation of the recognized tree
(`ptr_low_shape`: the `PT.low` of `CombProc.lean` equals `PSk.low` of the skeleton, the condition through
`cond_shape`), and that its Boolean reading is the Boolean reading of the lowered tree (`psk_xfOk`, `psk_bit`,
on top of the `PTree`-level `CombProc.low_xfBits` of G2.1). The per-site lemma `site_lowL` says that the
instantiated process of a site (an assign, or a procedural body through `CombProc.lower_site`) lowers to an
assign with the promised window, width and Boolean reading, and the producer theorem **`eq_of_summaryL`** is
`eq_of_summary` for the lowered design `d'` (`CombEq.eq_of_summary`, `CombEqThm.lean`): from `CombDesign d'`,
`Acyclic d'`, a settled state of `d'` and the obligations (`EqFragL`, `WidthOblL`, `BitReadObl`, `CoverObl`,
`InKnown`, plus the structural ones) it returns the netlist view `EqsL ∧ Knowns`.

| theorem | statement |
|---|---|
| `ptr_sk_eq`, `ptr_sk_leaves` | the skeleton computed from the flat read list is the annotated tree's, with the reads as leaves |
| `cond_shape` | a condition instantiates (context `none`) to its skeleton at width one |
| `ptr_low_shape` | `PT.low` of the recognized tree is the lowering of its skeleton |
| `psk_low_xfWidth`, `psk_low_xfBits` | the lowered tree is x-free at the target width and evaluates to the skeleton's bits |
| `site_lowL` | one site: the lowered process, its window, width and bits |
| `instantiateGD2_eq_of_lowerable` | a guarded instantiation that lowers passed the driver guard |
| `eq_of_summaryL`, `eq_viewL` | the netlist view for the lowered design |
| `site_lowLM`, `eq_of_summaryM`, `eq_viewLM` | the same for a body that writes several windows (WP-G S1b gate d): `EqFragM`, `WidthOblM`, `CoverOblM` in, `EqsM ∧ KnownsM` out |

## Soundness story

Nothing is trusted. The skeleton is a plain function of the template and the site's reads; the theorems below
say it describes the tree the instantiation builds (`ptr_low_shape`) and that the lowered expression evaluates to
its Boolean reading, using only the same x-free fragment lemmas as `sv_equations` (`low_xfWidth`, `low_xfBits`)
and the tree lemmas of G2.1. COPY NOTE: `cond_shape` is the `skT_shape` proof with the
context `none` of an `if` condition; `PSk` is `Sk` with a choice node (`G22-NOTE.md`, section 3).

## The `#pin_axioms` command (WP-G S2)

This file also defines `#pin_axioms c₁ c₂ …` (next to the last section, "Axiom pins for the lemmas of the second
fragment"). It is a SUBSET check, not an exact pin: it fails (naming the constant and the axiom) when a constant
depends on anything outside `propext`, `Classical.choice`, `Quot.sound` (so `sorryAx`, `Lean.ofReduceBool` and any
hand-declared axiom are caught), and says nothing when it passes. It does NOT detect a lemma whose axiom set got
smaller or larger within the three; the older theorems of the lane keep their exact `#print axioms` pin under
`#guard_msgs`, and a new lemma that must not drift gets one of those.
-/

namespace LeanModels.Sv

/-- The width of a literal vector (for the tactics' normalization of `width_k`: a literal `{ bits := #[…] }`
has as many bits as listed; the lemma does not fire on a vector given by a variable). -/
theorem LVec.width_mk_toArray (l : List Logic) : (LVec.mk l.toArray).width = l.length := by
  simp [LVec.width]

/-- The unsigned value of a literal vector (its known bits; an `x`/`z` reads as `0`). -/
def LVec.nat (v : LVec) : Nat := XF.val v.boolAt v.width

namespace XF

/-- **`case` as a fold** (WP-G S3a). The value of bit `k` of the first arm one of whose patterns equals the
subject `sv` (compared at width `w`, `XF.eqv`), else of the default. `sv_equations` prints a plain `case` with
constant items this way (the one place where the printed shape of a procedural statement is a fold and not
an `if` chain); `caseSel_cons` unfolds one arm. -/
def caseSel (w : Nat) (sv : Nat → Bool) :
    List (List (Nat → Bool) × (Nat → Bool)) → (Nat → Bool) → Nat → Bool
  | [], d, k => d k
  | (ps, v) :: rest, d, k => if ps.any (fun p => XF.eqv w sv p) then v k else caseSel w sv rest d k

@[simp] theorem caseSel_nil (w : Nat) (sv : Nat → Bool) (d : Nat → Bool) (k : Nat) :
    caseSel w sv [] d k = d k := rfl

theorem caseSel_cons (w : Nat) (sv : Nat → Bool) (ps : List (Nat → Bool)) (v : Nat → Bool)
    (rest : List (List (Nat → Bool) × (Nat → Bool))) (d : Nat → Bool) (k : Nat) :
    caseSel w sv ((ps, v) :: rest) d k =
      if ps.any (fun p => XF.eqv w sv p) then v k else caseSel w sv rest d k := rfl


/-! ### A `case` over a table of literals: the lookup in the table of numbers (WP-G S3a)

The items `sv_equations` prints for a `case` whose patterns and values are literals are `tbl.map fun e => ([e.1.boolAt], e.2.boolAt)`
for a `tbl : List (LVec × LVec)`; `caseSel_table` says the fold is the Boolean reading of `lookupNat (tblNat tbl) d.nat (val xf w)`, a
lookup in the table of numbers, which one `decide +kernel` over the inputs evaluates. -/

theorem val_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : val f n = val g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [val]
      rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem eqv_eq_true_iff (w : Nat) (f g : Nat → Bool) :
    XF.eqv w f g = true ↔ val f w = val g w := by
  simp only [XF.eqv, decide_eq_true_eq]
  constructor
  · intro h; exact val_congr h
  · intro h k hk
    rw [← testBit_val f w k hk, ← testBit_val g w k hk, h]

theorem testBit_nat_boolAt (v : LVec) (k : Nat) : (v.nat).testBit k = v.boolAt k := by
  by_cases hk : k < v.width
  · exact testBit_val v.boolAt v.width k hk
  · have h1 : v.boolAt k = false := by
      simp only [LVec.boolAt]
      have : v.bits[k]? = none := by
        apply Array.getElem?_eq_none
        simpa [LVec.width] using hk
      simp [this]
    rw [h1]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega)))

/-- A table as numbers: each pattern and value by its unsigned value. -/
def tblNat (tbl : List (LVec × LVec)) : List (Nat × Nat) := tbl.map fun e => (e.1.nat, e.2.nat)

/-- The first entry whose key is `n`, else the default. -/
def lookupNat : List (Nat × Nat) → Nat → Nat → Nat
  | [], d, _ => d
  | (p, v) :: rest, d, n => if n = p then v else lookupNat rest d n

theorem caseSel_table (w : Nat) (xf : Nat → Bool) (d : LVec) (k : Nat) :
    ∀ (tbl : List (LVec × LVec)), (∀ e ∈ tbl, e.1.width = w) →
      caseSel w xf (tbl.map fun e => ([e.1.boolAt], e.2.boolAt)) d.boolAt k =
        (lookupNat (tblNat tbl) d.nat (val xf w)).testBit k
  | [], _ => by simp [tblNat, lookupNat, testBit_nat_boolAt]
  | e :: rest, h => by
      have ih := caseSel_table w xf d k rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hw := h e (List.mem_cons_self ..)
      simp only [List.map_cons, caseSel, tblNat, lookupNat, List.any_cons, List.any_nil, Bool.or_false]
      by_cases hq : XF.eqv w xf e.1.boolAt = true
      · have hq' := (eqv_eq_true_iff w xf e.1.boolAt).1 hq
        have : val e.1.boolAt w = e.1.nat := by simp [LVec.nat, hw]
        rw [if_pos hq, if_pos (by omega)]
        exact (testBit_nat_boolAt e.2 k).symm
      · have hq' : ¬ val xf w = e.1.nat := by
          intro h'
          apply hq
          rw [eqv_eq_true_iff, h']
          simp [LVec.nat, hw]
        rw [if_neg hq, if_neg hq']
        exact ih

/-- **A table `case` at the bit-vector level.** The fold `sv_equations` prints for a `case` over the literals of a
table, read at inputs that are the bits of `x`, is bit `j` of `f x`, when the lookup in the table of numbers
is `f` on every input (`hf`, one `decide +kernel`). -/
theorem caseSel_bv {w m : Nat} (tbl : List (LVec × LVec)) (d : LVec) (f : BitVec w → BitVec m)
    (hw : ∀ e ∈ tbl, e.1.width = w)
    (hf : ∀ n : Fin (2 ^ w), lookupNat (tblNat tbl) d.nat n.val = (f (BitVec.ofFin n)).toNat)
    (xf : Nat → Bool) (x : BitVec w) (hx : ∀ i, i < w → xf i = x.getLsbD i) (j : Nat) :
    caseSel w xf (tbl.map fun e => ([e.1.boolAt], e.2.boolAt)) d.boolAt j = (f x).getLsbD j := by
  have hbv : XF.bv w xf = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [XF.getLsbD_bv hi]
    exact hx i hi
  have hxv : XF.val xf w = x.toNat := by
    rw [← hbv]
    simp only [XF.bv, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (XF.val_lt _ _)).symm
  rw [caseSel_table w xf d j tbl hw, hxv]
  have h : lookupNat (tblNat tbl) d.nat x.toNat = (f x).toNat := by
    have h' := hf x.toFin
    simp only [BitVec.ofFin_toFin] at h'
    exact h'
  rw [h]
  rfl

/-- **From the equation of a table `case` to the outputs**: the equation `hy` of the target (the fold, as
`sv_equations` states it), the inputs' bits (`hx`) and a known `m`-bit value for the target give
`target = f x`. -/
theorem caseSel_out {w m : Nat} (tbl : List (LVec × LVec)) (d : LVec) (f : BitVec w → BitVec m)
    (hw : ∀ e ∈ tbl, e.1.width = w)
    (hf : ∀ n : Fin (2 ^ w), lookupNat (tblNat tbl) d.nat n.val = (f (BitVec.ofFin n)).toNat)
    {st : SvState} (xn yn : String) {x : BitVec w}
    (hx : ∀ i, i < w → st.boolAt xn i = x.getLsbD i)
    (hy : ∀ k, k < m → st.boolAt yn k =
      caseSel w (st.boolAt xn) (tbl.map fun e => ([e.1.boolAt], e.2.boolAt)) d.boolAt k)
    {vs : LVec} (hs : SvState.lookup st yn = some vs) (hsw : vs.width = m)
    (hks : ∀ k, k < m → KnownBit st yn k) :
    SvState.lookup st yn = some (LVec.ofBitVec (f x)) := by
  have hvs := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  rw [hvs] at hs
  have heq : XF.bv m (st.boolAt yn) = f x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [XF.getLsbD_bv hj, hy j hj]
    exact caseSel_bv tbl d f hw hf (st.boolAt xn) x hx j
  rw [hs, heq]

end XF

namespace CombEq
open CombView

/-! ## The skeleton -/

/-- The shape of a right-hand side of a procedural site: a leaf is the skeleton of one assignment's right-hand
side, `ite` a choice on the first bit of a gate-tree condition, `blk` a `begin … end`. -/
inductive PSk where
  | leaf (sk : Sk)
  | ite (c : Sk) (a b : PSk)
  | blk (a : PSk)
  /-- A plain `case` with constant items (WP-G S3a): the subject, the arms (literal patterns, value) in
  source order, the default's value. -/
  | cases (s : Sk) (its : List (List LVec × Sk)) (d : Sk)
  /-- Default-then-override (WP-G S3b): the same choice as `ite`, but its access leaves are listed in SOURCE
  order, the statements before the `if` first. -/
  | ovr (c : Sk) (a b : PSk)

/-- The Boolean reading of the arms: pattern bits and value bits. -/
def pskArmsBit (σ : String → Int) (dw : String → Nat) (tw : Nat) (rd : String → Nat → Bool) :
    List (List LVec × Sk) → List (List (Nat → Bool) × (Nat → Bool))
  | [] => []
  | (ps, a) :: rest => (ps.map LVec.boolAt, a.bitC σ dw tw rd) :: pskArmsBit σ dw tw rd rest

/-- The instantiated arms: literal patterns, values lowered at the target width. -/
def pskArmsLow (σ : String → Int) (dw : String → Nat) (tw : Nat) :
    List (List LVec × Sk) → List (List Expr2 × Expr2)
  | [] => []
  | (ps, a) :: rest => (ps.map Expr2.lit, a.low σ dw tw) :: pskArmsLow σ dw tw rest

/-- Every pattern is as wide as the subject, every value as wide as the target. -/
def PskArmsOk (σ : String → Int) (dw : String → Nat) (ws tw : Nat) (its : List (List LVec × Sk)) : Prop :=
  ∀ it ∈ its, (∀ v ∈ it.1, v.width = ws) ∧ it.2.WidthOkC σ dw tw

/-- The access leaves of the arms' values (patterns are literals). -/
def pskArmLeaves : List (List LVec × Sk) → List Acc
  | [] => []
  | (_, a) :: rest => a.leaves ++ pskArmLeaves rest

/-- Patterns and values carry no `x`/`z`. -/
def pskArmsKnown : List (List LVec × Sk) → Bool
  | [] => true
  | (ps, a) :: rest => ps.all (fun v => v.knownB) && a.knownB && pskArmsKnown rest

/-- Bit `k` of the skeleton: a choice is the `if` rule (the condition's bit 0 is `1`). -/
def PSk.bit (σ : String → Int) (dw : String → Nat) (tw : Nat) (rd : String → Nat → Bool) :
    PSk → Nat → Bool
  | .leaf sk, k => sk.bitC σ dw tw rd k
  | .ite c a b, k =>
      if c.bitC σ dw 1 rd 0 then a.bit σ dw tw rd k else b.bit σ dw tw rd k
  | .blk a, k => a.bit σ dw tw rd k
  | .cases s its d, k =>
      XF.caseSel (s.width σ dw) (s.bitC σ dw (s.width σ dw) rd) (pskArmsBit σ dw tw rd its)
        (d.bitC σ dw tw rd) k
  | .ovr c a b, k =>
      if c.bitC σ dw 1 rd 0 then a.bit σ dw tw rd k else b.bit σ dw tw rd k

/-- The tree the instantiation builds for the skeleton at target width `tw` (conditions are one bit). -/
def PSk.low (σ : String → Int) (dw : String → Nat) (tw : Nat) : PSk → CombProc.PTree
  | .leaf sk => .leaf (sk.low σ dw tw)
  | .ite c a b => .ite (c.low σ dw 1) (a.low σ dw tw) (b.low σ dw tw)
  | .blk a => .blk (a.low σ dw tw)
  | .cases s its d => .cases (s.low σ dw 0) (pskArmsLow σ dw tw its) (d.low σ dw tw)
  | .ovr c a b => .ovr (c.low σ dw 1) (a.low σ dw tw) (b.low σ dw tw)

/-- Every leaf operand fits the target (`Sk.WidthOkC`: a bare access exactly, a `Resize` marker at most), every
condition operand is one bit. -/
def PSk.WidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : PSk → Prop
  | .leaf sk => sk.WidthOkC σ dw tw
  | .ite c a b => c.WidthOkC σ dw 1 ∧ a.WidthOk σ dw tw ∧ b.WidthOk σ dw tw
  | .blk a => a.WidthOk σ dw tw
  | .cases s its d => s.SelfOk σ dw ∧ PskArmsOk σ dw (s.width σ dw) tw its ∧ d.WidthOkC σ dw tw
  | .ovr c a b => c.WidthOkC σ dw 1 ∧ a.WidthOk σ dw tw ∧ b.WidthOk σ dw tw

/-- The access leaves, conditions first (the order of the site's read list). -/
def PSk.leaves : PSk → List Acc
  | .leaf sk => sk.leaves
  | .ite c a b => c.leaves ++ a.leaves ++ b.leaves
  | .blk a => a.leaves
  | .cases s its d => s.leaves ++ pskArmLeaves its ++ d.leaves
  | .ovr c a b => b.leaves ++ c.leaves ++ a.leaves

/-- Literals and fills carry no `x`/`z`. -/
def PSk.knownB : PSk → Bool
  | .leaf sk => sk.knownB
  | .ite c a b => c.knownB && a.knownB && b.knownB
  | .blk a => a.knownB
  | .cases s its d => s.knownB && pskArmsKnown its && d.knownB
  | .ovr c a b => c.knownB && a.knownB && b.knownB

/-! ## From the template -/

/-- Number of access leaves `skRhs` consumes. -/
def rcnt : PExpr → Nat
  | .fill _ => 0
  | .concat ps => pcnt ps
  | v => cnt v

/-- Number of access leaves of an arm's value. -/
def armRcnt : PStmt → Nat
  | .blockingAssign _ v => rcnt v
  | .blockingAssignL _ v => rcnt v
  | _ => 0

/-- … of the arms of a `case`. -/
def itemsRcnt : List (List PExpr × PStmt) → Nat
  | [] => 0
  | (_, b) :: rest => armRcnt b + itemsRcnt rest

/-- A literal pattern's value. -/
def patLit : PExpr → LVec
  | .lit v => v
  | _ => ⟨#[]⟩

/-- The skeleton of an arm's value, taking its accesses from `as`. -/
def armSk (as : List Acc) : PStmt → Sk
  | .blockingAssign _ v => skRhs v as
  | .blockingAssignL _ v => skRhs v as
  | _ => .fill .l0

/-- The skeletons of the arms of a `case`, taking the accesses of `as` in order. -/
def caseSkItems (as : List Acc) : List (List PExpr × PStmt) → List (List LVec × Sk)
  | [] => []
  | (ps, b) :: rest =>
      (ps.map patLit, armSk (as.take (armRcnt b)) b) :: caseSkItems (as.drop (armRcnt b)) rest

mutual
/-- Number of access leaves the skeleton of a statement consumes. -/
def stmtRcnt : PStmt → Nat
  | .blockingAssign _ v => rcnt v
  | .blockingAssignL _ v => rcnt v
  | .ifStmt c a (some b) => cnt c + stmtRcnt a + stmtRcnt b
  | .ifStmt c a none => cnt c + stmtRcnt a
  | .block ss => stmtRcntL ss
  | .caseStmt subj items (some d) .normal .none => cnt subj + itemsRcnt items + armRcnt d
  | _ => 0
termination_by structural s => s

def stmtRcntL : List PStmt → Nat
  | [] => 0
  | s :: rest => stmtRcnt s + stmtRcntL rest
termination_by structural ss => ss
end

mutual
/-- **The skeleton of a template body**, taking the accesses of the site's read list in order. -/
def stmtSk (as : List Acc) : PStmt → PSk
  | .blockingAssign _ v => .leaf (skRhs v as)
  | .blockingAssignL _ v => .leaf (skRhs v as)
  | .ifStmt c a (some b) =>
      .ite (skT c (as.take (cnt c))) (stmtSk ((as.drop (cnt c)).take (stmtRcnt a)) a)
        (stmtSk ((as.drop (cnt c)).drop (stmtRcnt a)) b)
  | .block ss => stmtSkL as ss
  | .caseStmt subj items (some d) .normal .none =>
      .cases (skT subj (as.take (cnt subj))) (caseSkItems (as.drop (cnt subj)) items)
        (armSk ((as.drop (cnt subj)).drop (itemsRcnt items)) d)
  | _ => .leaf (.fill .l0)
termination_by structural s => s

def stmtSkL (as : List Acc) : List PStmt → PSk
  | [s] => .blk (stmtSk as s)
  | s :: t :: rest =>
      ovrSk (as.drop (stmtRcnt s)) (stmtSk (as.take (stmtRcnt s)) s) (t :: rest)
  | [] => .leaf (.fill .l0)
termination_by structural ss => ss

/-- One override statement `if (c) a;` laid over the skeleton `base` of the statements before it. -/
def stepSk (as : List Acc) (base : PSk) : PStmt → PSk
  | .ifStmt c a none =>
      .ovr (skT c (as.take (cnt c))) (stmtSk ((as.drop (cnt c)).take (stmtRcnt a)) a) base
  | _ => base
termination_by structural s => s

/-- The overrides of a block, in source order, over the skeleton of the statements before them. It STOPS at
the first statement that is not an override `if (c) …;` without `else`: the next statement starts the next
window of a body that writes several (S1b gate d), and a body of one window has nothing but overrides after
its first statement (what the recognizer accepts). -/
def ovrSk (as : List Acc) (base : PSk) : List PStmt → PSk
  | [] => base
  | .ifStmt c a none :: rest =>
      ovrSk (as.drop (cnt c + stmtRcnt a))
        (.ovr (skT c (as.take (cnt c))) (stmtSk ((as.drop (cnt c)).take (stmtRcnt a)) a) base) rest
  | _ :: _ => base
termination_by structural ss => ss
end

/-- The skeleton of a nonempty statement list: the first statement, then the overrides. -/
def listSk (as : List Acc) : List PStmt → PSk
  | [] => .leaf (.fill .l0)
  | s :: rest => ovrSk (as.drop (stmtRcnt s)) (stmtSk (as.take (stmtRcnt s)) s) rest

/-- The skeleton of the right-hand side of a process: an `always_comb` body, or the single assignment. For a body
of several windows it is the skeleton of the HEAD window (`ovrSk` stops at the next window's first statement). -/
def rhsSk : PProcess → List Acc → PSk
  | .alwaysComb b, as => stmtSk as b
  | p, as => .leaf (skRhs (rhsOf p) as)

/-- A statement is an override `if (c) …;` without `else`. -/
def IsOvrStmt (s : PStmt) : Prop := ∃ c a, s = .ifStmt c a none

/-- The leading overrides of a statement list, and the rest. -/
def spanOvr : List PStmt → List PStmt × List PStmt
  | [] => ([], [])
  | .ifStmt c a none :: rest => ((.ifStmt c a none :: (spanOvr rest).1), (spanOvr rest).2)
  | s :: rest => ([], s :: rest)

/-- The skeletons of the windows of a body, one per segment (a segment: a statement that is not an override and the
overrides after it), taking the reads chunk by chunk; the fuel is the number of statements. -/
def windowSksF : Nat → List Acc → List PStmt → List PSk
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | n + 1, as, s :: rest =>
      listSk as (s :: (spanOvr rest).1) ::
        windowSksF n (as.drop (stmtRcntL (s :: (spanOvr rest).1))) (spanOvr rest).2

def windowSks (as : List Acc) (ss : List PStmt) : List PSk := windowSksF ss.length as ss

/-- The skeletons of the windows of a process: one per segment of an `always_comb` block, one otherwise. The head
window's skeleton is `rhsSk`; this list is read for the FURTHER windows (its tail). -/
def procSks : PProcess → List Acc → List PSk
  | .alwaysComb (.block ss), as => windowSks as ss
  | p, as => [rhsSk p as]

/-- The right-hand side `sv_equations` checks is in the fragment: a procedural body was checked by the
recognizer, anything else by `fragOk`. -/
def fragOkP : PProcess → Bool
  | .alwaysComb _ => true
  | p => fragOk (rhsOf p)

theorem rhsSk_of_ne {p : PProcess} (h : ∀ b, p ≠ .alwaysComb b) (as : List Acc) :
    rhsSk p as = .leaf (skRhs (rhsOf p) as) := by
  cases p with
  | alwaysComb b => exact absurd rfl (h b)
  | _ => rfl

theorem fragOkP_of_ne {p : PProcess} (h : ∀ b, p ≠ .alwaysComb b) :
    fragOkP p = fragOk (rhsOf p) := by
  cases p with
  | alwaysComb b => exact absurd rfl (h b)
  | _ => rfl

/-! ## The annotated tree's skeleton -/

/-- The skeleton of an annotated tree (what `stmtSk` computes from the flat read list). -/
def ptrArmsSk : List (List PExpr × CombProc.PLfR) → List (List LVec × Sk)
  | [] => []
  | (ps, a) :: rest => (ps.map patLit, skRhs a.pl.val a.rds) :: ptrArmsSk rest

def ptrSk : CombProc.PTR → PSk
  | .leafL _ v rs => .leaf (skRhs v rs)
  | .leafW _ v rs => .leaf (skRhs v rs)
  | .ite c rc a b => .ite (skT c rc) (ptrSk a) (ptrSk b)
  | .ovr c rc a b => .ovr (skT c rc) (ptrSk a) (ptrSk b)
  | .blk a => .blk (ptrSk a)
  | .cases s rc its d => .cases (skT s rc) (ptrArmsSk its) (skRhs d.pl.val d.rds)

theorem rhsRds_len {ds : List DeclT} {v : PExpr} {rs : List Acc}
    (h : rhsRds? ds v = .ok rs) (hf : fragOk v = true) : rs.length = rcnt v := by
  by_cases hfill : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hfill
    simp only [rhsRds?, Except.ok.injEq] at h
    subst h
    simp [rcnt]
  by_cases hcat : ∃ ps, v = .concat ps
  · obtain ⟨ps, rfl⟩ := hcat
    have h' : partsRdW? ds ps = .ok rs := by simpa [rhsRds?, rdsOfW?] using h
    simpa [rcnt] using partsRdW_len ps rs h'
  · have hn1 : ∀ b, v ≠ .fill b := fun b h => hfill ⟨b, h⟩
    have hn2 : ∀ ps, v ≠ .concat ps := fun ps h => hcat ⟨ps, h⟩
    rw [rhsRds?_of_ne hn1] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    have hr : rcnt v = cnt v := by
      cases v <;> first | rfl | exact absurd rfl (hn1 _) | exact absurd rfl (hn2 _)
    rw [hr]
    exact rdsOfW?_len v rs h (fragWV_of_fragW v hf).1

open CombProc in
theorem armRcnt_plfr {ds : List DeclT} {tg : Acc} :
    ∀ (a : PLfR), a.Ok ds tg → armRcnt a.pl.toPStmt = a.rds.length
  | .leafL t v rs, hok => by
      simpa [PLfR.pl, PLf.toPStmt, armRcnt, PLfR.rds] using (rhsRds_len hok.2.1 (fragOkL_spec hok.2.2).1).symm
  | .leafW n v rs, hok => by
      simpa [PLfR.pl, PLf.toPStmt, armRcnt, PLfR.rds] using (rhsRds_len hok.2.1 (fragOkL_spec hok.2.2).1).symm

open CombProc in
theorem itemsRcnt_arms {ds : List DeclT} {tg : Acc} :
    ∀ its : List (List PExpr × PLfR), PLfR.ArmsOk ds tg its →
      itemsRcnt (PLf.items (PLfR.arms its)) = (PLfR.armRds its).length
  | [], _ => by simp [PLfR.arms, PLf.items, itemsRcnt, PLfR.armRds]
  | (ps, a) :: rest, h => by
      have h1 := armRcnt_plfr a (h (ps, a) (List.mem_cons_self ..)).2
      have h2 := itemsRcnt_arms rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp [PLfR.arms, PLf.items, itemsRcnt, PLfR.armRds, h1, h2]

open CombProc in
theorem caseSkItems_arms {ds : List DeclT} {tg : Acc} :
    ∀ (its : List (List PExpr × PLfR)) (extra : List Acc), PLfR.ArmsOk ds tg its →
      caseSkItems (PLfR.armRds its ++ extra) (PLf.items (PLfR.arms its)) = ptrArmsSk its
  | [], extra, _ => by simp [PLfR.arms, PLf.items, caseSkItems, ptrArmsSk]
  | (ps, a) :: rest, extra, h => by
      have h1 := armRcnt_plfr a (h (ps, a) (List.mem_cons_self ..)).2
      have ih := caseSkItems_arms rest extra (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have e1 : (a.rds ++ PLfR.armRds rest ++ extra).take a.rds.length = a.rds := by
        rw [List.append_assoc]; exact List.take_left' rfl
      have e2 : (a.rds ++ PLfR.armRds rest ++ extra).drop a.rds.length =
          PLfR.armRds rest ++ extra := by
        rw [List.append_assoc]; exact List.drop_left' rfl
      simp only [PLfR.arms, PLf.items, PLfR.armRds, caseSkItems, ptrArmsSk, h1, e1, e2, ih]
      cases a <;> rfl

open CombProc in
theorem plfr_leaves {ds : List DeclT} {tg : Acc} :
    ∀ (a : PLfR), a.Ok ds tg → (skRhs a.pl.val a.rds).leaves = a.rds
  | .leafL t v rs, hok => skRhs_leaves hok.2.1 (fragOkL_spec hok.2.2).1
  | .leafW n v rs, hok => skRhs_leaves hok.2.1 (fragOkL_spec hok.2.2).1

open CombProc in
theorem pskArmLeaves_arms {ds : List DeclT} {tg : Acc} :
    ∀ its : List (List PExpr × PLfR), PLfR.ArmsOk ds tg its →
      pskArmLeaves (ptrArmsSk its) = PLfR.armRds its
  | [], _ => by simp [ptrArmsSk, pskArmLeaves, PLfR.armRds]
  | (ps, a) :: rest, h => by
      have h1 := plfr_leaves a (h (ps, a) (List.mem_cons_self ..)).2
      have h2 := pskArmLeaves_arms rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp [ptrArmsSk, pskArmLeaves, PLfR.armRds, h1, h2]

theorem stmtRcntL_append : ∀ l1 l2 : List PStmt,
    stmtRcntL (l1 ++ l2) = stmtRcntL l1 + stmtRcntL l2
  | [], l2 => by simp [stmtRcntL]
  | s :: r, l2 => by simp [stmtRcntL, stmtRcntL_append r l2, Nat.add_assoc]

theorem stmtRcntL_base (b : CombProc.PT) :
    stmtRcntL (if b.isOvr then CombProc.PStmt.unblock b.toPStmt else [b.toPStmt]) = stmtRcnt b.toPStmt := by
  split
  · rename_i ho
    cases b <;> simp [CombProc.PT.isOvr] at ho
    simp [CombProc.PT.toPStmt, CombProc.PStmt.unblock, stmtRcnt]
  · simp [stmtRcntL]

open CombProc in
/-- The statements of a template tree: the first one is not an override, the others are. -/
theorem stmtsP_shape : ∀ b : PT, ∃ s ovs, b.stmtsP = s :: ovs ∧ (∀ y ∈ ovs, IsOvrStmt y) ∧ ¬ IsOvrStmt s
  | .leafL t v => ⟨PStmt.blockingAssignL t v, [], by simp [PT.stmtsP, PT.isOvr, PT.toPStmt], by simp, by rintro ⟨c, a, h⟩; simp at h⟩
  | .leafW n v => ⟨PStmt.blockingAssign n v, [], by simp [PT.stmtsP, PT.isOvr, PT.toPStmt], by simp, by rintro ⟨c, a, h⟩; simp at h⟩
  | .ite c a b => ⟨PStmt.ifStmt c a.toPStmt (some b.toPStmt), [], by simp [PT.stmtsP, PT.isOvr, PT.toPStmt], by simp, by rintro ⟨c', a', h⟩; simp at h⟩
  | .blk a => ⟨PStmt.block [a.toPStmt], [], by simp [PT.stmtsP, PT.isOvr, PT.toPStmt], by simp, by rintro ⟨c, a', h⟩; simp at h⟩
  | .cases s its d => ⟨PStmt.caseStmt s (PLf.items its) (some d.toPStmt) .normal .none, [], by simp [PT.stmtsP, PT.isOvr, PT.toPStmt], by simp, by rintro ⟨c, a, h⟩; simp at h⟩
  | .ovr c a b => by
      obtain ⟨s0, ovs, he, hov, hs0⟩ := stmtsP_shape b
      refine ⟨s0, ovs ++ [PStmt.ifStmt c a.toPStmt none], ?_, ?_, hs0⟩
      · have : (PT.ovr c a b).stmtsP = b.stmtsP ++ [PStmt.ifStmt c a.toPStmt none] := by
          simp [PT.stmtsP, PT.isOvr, PT.toPStmt, PStmt.unblock]
        rw [this, he]; rfl
      · intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact hov y h
        · rw [List.mem_singleton] at h
          exact ⟨c, a.toPStmt, h⟩

/-- One override statement is `stepSk` of the skeleton so far, and the reads move on. -/
theorem ovrSk_cons_ovr (as : List Acc) (base : PSk) (c : PExpr) (a : PStmt) (rest : List PStmt) :
    ovrSk as base (.ifStmt c a none :: rest) =
      ovrSk (as.drop (stmtRcnt (.ifStmt c a none))) (stepSk as base (.ifStmt c a none)) rest := by
  simp [ovrSk, stepSk, stmtRcnt]

/-- A statement that is not an override ends the run. -/
theorem ovrSk_stop (as : List Acc) (base : PSk) (s : PStmt) (rest : List PStmt) (h : ¬ IsOvrStmt s) :
    ovrSk as base (s :: rest) = base := by
  cases s with
  | ifStmt c a b =>
      cases b with
      | none => exact absurd ⟨c, a, rfl⟩ h
      | some b => rfl
  | _ => rfl

theorem ovrSk_append : ∀ (l1 l2 : List PStmt) (as : List Acc) (base : PSk), (∀ x ∈ l1, IsOvrStmt x) →
    ovrSk as base (l1 ++ l2) = ovrSk (as.drop (stmtRcntL l1)) (ovrSk as base l1) l2
  | [], l2, as, base, _ => by simp [ovrSk, stmtRcntL]
  | s :: r, l2, as, base, h => by
      obtain ⟨c, a, rfl⟩ := h s (List.mem_cons_self ..)
      simp only [List.cons_append]
      rw [ovrSk_cons_ovr, ovrSk_cons_ovr,
        ovrSk_append r l2 _ _ (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.drop_drop]
      simp [stmtRcntL]

/-- … and an `ovrSk` over the overrides followed by a statement that is not one is the `ovrSk` over the overrides. -/
theorem ovrSk_append_stop : ∀ (ovs rest : List PStmt) (as : List Acc) (base : PSk),
    (∀ x ∈ ovs, IsOvrStmt x) → (rest = [] ∨ ∃ t r, rest = t :: r ∧ ¬ IsOvrStmt t) →
    ovrSk as base (ovs ++ rest) = ovrSk as base ovs
  | [], rest, as, base, _, hr => by
      rcases hr with rfl | ⟨t, r, rfl, ht⟩
      · simp [ovrSk]
      · simp only [List.nil_append, ovrSk]
        exact ovrSk_stop as base t r ht
  | s :: r, rest, as, base, h, hr => by
      obtain ⟨c, a, rfl⟩ := h s (List.mem_cons_self ..)
      simp only [List.cons_append]
      rw [ovrSk_cons_ovr, ovrSk_cons_ovr,
        ovrSk_append_stop r rest _ _ (fun x hx => h x (List.mem_cons_of_mem _ hx)) hr]

theorem listSk_snoc (as : List Acc) (x : PStmt) (hx : IsOvrStmt x) :
    ∀ L : List PStmt, L ≠ [] → (∀ y ∈ L.tail, IsOvrStmt y) →
      listSk as (L ++ [x]) = stepSk (as.drop (stmtRcntL L)) (listSk as L) x
  | [], h, _ => absurd rfl h
  | s :: rest, _, hr => by
      obtain ⟨c, a, rfl⟩ := hx
      simp only [List.cons_append, listSk, stmtRcntL]
      rw [ovrSk_append rest _ _ _ hr, ovrSk_cons_ovr, List.drop_drop]
      simp [ovrSk, stmtRcnt, stmtRcntL, List.drop_drop]

open CombProc in
/-- The read list of a recognized tree has the length the statement's skeleton consumes. -/
theorem ptr_rds_len {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → ptr.rds.length = stmtRcnt ptr.pt.toPStmt
  | .leafL t v rs, hok => by
      simpa [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt] using rhsRds_len hok.2.1 (fragOkL_spec hok.2.2).1
  | .leafW n v rs, hok => by
      simpa [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt] using rhsRds_len hok.2.1 (fragOkL_spec hok.2.2).1
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      have h1 := rdsOf?_len c rc hc hg
      have h2 := ptr_rds_len a ha
      have h3 := ptr_rds_len b hb
      simp [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt, h1, h2, h3, Nat.add_assoc]
  | .ovr c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      have h1 := rdsOf?_len c rc hc hg
      have h2 := ptr_rds_len a ha
      have h3 := ptr_rds_len b hb
      simp only [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt, stmtRcntL_append, stmtRcntL_base, stmtRcntL,
        List.length_append, h1, h2, h3, Nat.add_zero]
      omega
  | .blk a, hok => by
      simpa [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt, stmtRcntL] using ptr_rds_len a hok
  | .cases s rc its d, ⟨⟨hs, hg⟩, harms, hd⟩ => by
      have h1 := rdsOf?_len s rc hs hg
      have h2 := itemsRcnt_arms its harms
      have h3 := armRcnt_plfr d hd
      simp [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt, h1, h2, h3, Nat.add_assoc]

open CombProc in
theorem listSk_nonovr {ds : List DeclT} {tg : Acc} (ptr : PTR) (hok : ptr.Ok ds tg)
    (hno : ptr.pt.isOvr = false) (h1 : stmtSk ptr.rds ptr.pt.toPStmt = ptrSk ptr) (extra : List Acc) :
    listSk (ptr.rds ++ extra) ptr.pt.stmtsP = ptrSk ptr := by
  have hlen := ptr_rds_len ptr hok
  have e : ptr.pt.stmtsP = [ptr.pt.toPStmt] := by simp [PT.stmtsP, hno]
  rw [e]
  simp only [listSk, ovrSk, ← hlen, List.take_left']
  exact h1

open CombProc in
/-- **The skeleton computed from the flat read list is the annotated tree's** (and, for the override
chain, the skeleton of the statement list is, whatever follows the tree's reads in the list). -/
theorem ptr_sk_both {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → stmtSk ptr.rds ptr.pt.toPStmt = ptrSk ptr ∧
      ∀ extra : List Acc, listSk (ptr.rds ++ extra) ptr.pt.stmtsP = ptrSk ptr
  | .leafL t v rs, hok => by
      have h : stmtSk (PTR.leafL t v rs).rds (PTR.leafL t v rs).pt.toPStmt = ptrSk (.leafL t v rs) := by
        simp [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk]
      exact ⟨h, listSk_nonovr _ hok rfl h⟩
  | .leafW n v rs, hok => by
      have h : stmtSk (PTR.leafW n v rs).rds (PTR.leafW n v rs).pt.toPStmt = ptrSk (.leafW n v rs) := by
        simp [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk]
      exact ⟨h, listSk_nonovr _ hok rfl h⟩
  | .ite c rc a b, hok => by
      obtain ⟨⟨hc, hg⟩, ha, hb⟩ := hok
      have h1 := rdsOf?_len c rc hc hg
      have h2 := ptr_rds_len a ha
      have e1 : (rc ++ a.rds ++ b.rds).take (cnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' h1
      have e2 : (rc ++ a.rds ++ b.rds).drop (cnt c) = a.rds ++ b.rds := by
        rw [List.append_assoc]; exact List.drop_left' h1
      have e3 : (a.rds ++ b.rds).take (stmtRcnt a.pt.toPStmt) = a.rds := List.take_left' h2
      have e4 : (a.rds ++ b.rds).drop (stmtRcnt a.pt.toPStmt) = b.rds := List.drop_left' h2
      have h : stmtSk (PTR.ite c rc a b).rds (PTR.ite c rc a b).pt.toPStmt = ptrSk (.ite c rc a b) := by
        simp only [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk, e1, e2, e3, e4]
        rw [(ptr_sk_both a ha).1, (ptr_sk_both b hb).1]
      exact ⟨h, listSk_nonovr _ ⟨⟨hc, hg⟩, ha, hb⟩ rfl h⟩
  | .blk a, hok => by
      have h : stmtSk (PTR.blk a).rds (PTR.blk a).pt.toPStmt = ptrSk (.blk a) := by
        simp only [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, stmtSkL, ptrSk]
        rw [(ptr_sk_both a hok).1]
      exact ⟨h, listSk_nonovr _ hok rfl h⟩
  | .cases s rc its d, hok => by
      obtain ⟨⟨hs, hg⟩, harms, hd⟩ := hok
      have h1 := rdsOf?_len s rc hs hg
      have h2 := itemsRcnt_arms its harms
      have e1 : (rc ++ PLfR.armRds its ++ d.rds).take (cnt s) = rc := by
        rw [List.append_assoc]; exact List.take_left' h1
      have e2 : (rc ++ PLfR.armRds its ++ d.rds).drop (cnt s) = PLfR.armRds its ++ d.rds := by
        rw [List.append_assoc]; exact List.drop_left' h1
      have e3 : (PLfR.armRds its ++ d.rds).drop (itemsRcnt (PLf.items (PLfR.arms its))) = d.rds := by
        rw [h2]; exact List.drop_left' rfl
      have h : stmtSk (PTR.cases s rc its d).rds (PTR.cases s rc its d).pt.toPStmt =
          ptrSk (.cases s rc its d) := by
        simp only [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk, e1, e2, e3,
          caseSkItems_arms its d.rds harms]
        cases d <;> rfl
      exact ⟨h, listSk_nonovr _ ⟨⟨hs, hg⟩, harms, hd⟩ rfl h⟩
  | .ovr c rc a b, hok => by
      obtain ⟨⟨hc, hg⟩, ha, hb⟩ := hok
      have h1 := rdsOf?_len c rc hc hg
      have h2 := ptr_rds_len a ha
      have h3 := ptr_rds_len b hb
      have ihb := (ptr_sk_both b hb).2
      have iha := (ptr_sk_both a ha).1
      have hL : stmtRcntL (b.pt.stmtsP) = b.rds.length := by
        rw [h3]; exact stmtRcntL_base b.pt
      have hne : b.pt.stmtsP ≠ [] := by
        unfold PT.stmtsP; split
        · rename_i ho
          cases hbp : b.pt <;> rw [hbp] at ho <;> simp [PT.isOvr] at ho
          simp [PT.toPStmt, PStmt.unblock]
        · simp
      have hshape : ∀ y ∈ b.pt.stmtsP.tail, IsOvrStmt y := by
        obtain ⟨s0, ovs, he, hov, -⟩ := stmtsP_shape b.pt
        rw [he]
        exact hov
      -- the general fact, for any tail after the reads of the statements before the `if`
      have key : ∀ extra : List Acc,
          listSk (b.rds ++ rc ++ a.rds ++ extra) (b.pt.stmtsP ++ [PStmt.ifStmt c a.pt.toPStmt none]) =
            ptrSk (.ovr c rc a b) := by
        intro extra
        have e4 : b.rds ++ rc ++ a.rds ++ extra = b.rds ++ (rc ++ (a.rds ++ extra)) := by
          simp [List.append_assoc]
        rw [e4, listSk_snoc _ _ ⟨c, a.pt.toPStmt, rfl⟩ _ hne hshape, hL]
        have e0 : (b.rds ++ (rc ++ (a.rds ++ extra))).drop b.rds.length = rc ++ (a.rds ++ extra) :=
          List.drop_left' rfl
        have e1 : (rc ++ (a.rds ++ extra)).take (cnt c) = rc := List.take_left' h1
        have e2 : (rc ++ (a.rds ++ extra)).drop (cnt c) = a.rds ++ extra := List.drop_left' h1
        have e3 : (a.rds ++ extra).take (stmtRcnt a.pt.toPStmt) = a.rds := by
          rw [← h2]; exact List.take_left' rfl
        rw [e0]
        simp only [stepSk, e1, e2, e3, ptrSk]
        rw [ihb (rc ++ (a.rds ++ extra)), iha]
      have hbody : (PTR.ovr c rc a b).pt.toPStmt = .block (b.pt.stmtsP ++ [PStmt.ifStmt c a.pt.toPStmt none]) := by
        simp [PTR.pt, PT.toPStmt, PT.stmtsP]
      have hstmts : (PTR.ovr c rc a b).pt.stmtsP = b.pt.stmtsP ++ [PStmt.ifStmt c a.pt.toPStmt none] := by
        simp [PT.stmtsP, PT.isOvr, hbody, PStmt.unblock, PTR.pt, PT.toPStmt]
      refine ⟨?_, fun extra => ?_⟩
      · rw [hbody]
        cases hl : b.pt.stmtsP with
        | nil => exact absurd hl hne
        | cons s rest =>
            rw [hl] at key
            have := key []
            simp only [PTR.rds, List.append_nil] at this ⊢
            cases rest with
            | nil => simpa [stmtSk, stmtSkL, listSk, ovrSk] using this
            | cons t rest' => simpa [stmtSk, stmtSkL, listSk] using this
      · rw [hstmts]
        simpa [PTR.rds] using key extra

open CombProc in
theorem ptr_sk_eq {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → stmtSk ptr.rds ptr.pt.toPStmt = ptrSk ptr :=
  fun ptr hok => (ptr_sk_both ptr hok).1

open CombProc in
theorem stmtsP_rcnt {ds : List DeclT} {tg : Acc} (ptr : PTR) (hok : ptr.Ok ds tg) :
    stmtRcntL ptr.pt.stmtsP = ptr.rds.length := by
  rw [ptr_rds_len ptr hok]; exact stmtRcntL_base ptr.pt

/-- The leading overrides of `ovs ++ rest`, when `rest` starts a new segment (or is empty), are `ovs`. -/
theorem spanOvr_append : ∀ (ovs rest : List PStmt), (∀ y ∈ ovs, IsOvrStmt y) →
    (rest = [] ∨ ∃ t r, rest = t :: r ∧ ¬ IsOvrStmt t) → spanOvr (ovs ++ rest) = (ovs, rest)
  | [], rest, _, hr => by
      rcases hr with rfl | ⟨t, r, rfl, ht⟩
      · simp [spanOvr]
      · cases t with
        | ifStmt c a b =>
            cases b with
            | none => exact absurd ⟨c, a, rfl⟩ ht
            | some b => simp [spanOvr]
        | _ => simp [spanOvr]
  | s :: r, rest, h, hr => by
      obtain ⟨c, a, rfl⟩ := h s (List.mem_cons_self ..)
      have ih := spanOvr_append r rest (fun x hx => h x (List.mem_cons_of_mem _ hx)) hr
      simp [spanOvr, ih]

open CombProc in
/-- **The skeletons of the windows of a recognized body are the segments' annotated skeletons.** -/
theorem windowSksF_segs {ds : List DeclT} : ∀ (segs : List (Acc × PTR)) (n : Nat),
    (∀ s ∈ segs, s.2.Ok ds s.1) → (segs.flatMap fun s => s.2.pt.stmtsP).length ≤ n →
    windowSksF n (CombView.segsRds segs) (segs.flatMap fun s => s.2.pt.stmtsP) =
      segs.map fun s => ptrSk s.2
  | [], n, _, _ => by cases n <;> simp [windowSksF, CombView.segsRds]
  | (tg, p) :: rest, n, hok, hn => by
      have hp : p.Ok ds tg := hok _ (List.mem_cons_self ..)
      obtain ⟨s0, ovs, he, hov, hs0⟩ := stmtsP_shape p.pt
      have hrest : ∀ s ∈ rest, s.2.Ok ds s.1 := fun s hs => hok s (List.mem_cons_of_mem _ hs)
      have hstart : (rest.flatMap fun s => s.2.pt.stmtsP) = [] ∨
          ∃ t r, (rest.flatMap fun s => s.2.pt.stmtsP) = t :: r ∧ ¬ IsOvrStmt t := by
        cases rest with
        | nil => left; simp
        | cons q qs =>
            right
            obtain ⟨t, ovs', he', -, ht⟩ := stmtsP_shape q.2.pt
            exact ⟨t, ovs' ++ qs.flatMap (fun s => s.2.pt.stmtsP), by simp [List.flatMap_cons, he'], ht⟩
      have hflat : (((tg, p) :: rest).flatMap fun s => s.2.pt.stmtsP) =
          s0 :: (ovs ++ rest.flatMap fun s => s.2.pt.stmtsP) := by
        simp [List.flatMap_cons, he]
      have hrds : CombView.segsRds ((tg, p) :: rest) = p.rds ++ CombView.segsRds rest := by
        simp [CombView.segsRds, List.flatMap_cons]
      have hn' : (rest.flatMap fun s => s.2.pt.stmtsP).length + ovs.length + 1 ≤ n := by
        rw [hflat] at hn; simp only [List.length_cons, List.length_append] at hn; omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [hflat, hrds]
      simp only [windowSksF]
      rw [spanOvr_append ovs _ hov hstart]
      have hlen : stmtRcntL (s0 :: ovs) = p.rds.length := by rw [← he]; exact stmtsP_rcnt p hp
      have hsk := (ptr_sk_both p hp).2 (CombView.segsRds rest)
      rw [he] at hsk
      rw [hsk, hlen, List.drop_left]
      rw [windowSksF_segs rest n' hrest (by omega)]
      simp

open CombProc in
theorem procSks_multi {ds : List DeclT} (segs : List (Acc × PTR)) (b : PStmt)
    (hbody : bodyP2 segs = b) (hb : ∃ ss, b = .block ss) (hok : ∀ s ∈ segs, s.2.Ok ds s.1) :
    procSks (.alwaysComb b) (CombView.segsRds segs) = segs.map fun s => ptrSk s.2 := by
  obtain ⟨ss, rfl⟩ := hb
  have hss : ss = segs.flatMap fun s => s.2.pt.stmtsP := by
    simpa [bodyP2] using hbody.symm
  subst hss
  simp only [procSks, windowSks]
  exact windowSksF_segs segs _ hok (Nat.le_refl _)

open CombProc in
/-- **The head window's skeleton of a body of several windows**: `rhsSk` stops at the second window. -/
theorem rhsSk_multi {ds : List DeclT} (tg tg2 : Acc) (p p2 : PTR) (rest : List (Acc × PTR))
    (hok : ∀ s ∈ (tg, p) :: (tg2, p2) :: rest, s.2.Ok ds s.1) :
    rhsSk (.alwaysComb (.block (((tg, p) :: (tg2, p2) :: rest).flatMap fun s => s.2.pt.stmtsP)))
      (CombView.segsRds ((tg, p) :: (tg2, p2) :: rest)) = ptrSk p := by
  have hp : p.Ok ds tg := hok _ (List.mem_cons_self ..)
  obtain ⟨s0, ovs, he, hov, hs0⟩ := stmtsP_shape p.pt
  obtain ⟨t, ovs', he', -, ht⟩ := stmtsP_shape p2.pt
  have hflat : (((tg, p) :: (tg2, p2) :: rest).flatMap fun s => s.2.pt.stmtsP) =
      s0 :: (ovs ++ (t :: (ovs' ++ rest.flatMap fun s => s.2.pt.stmtsP))) := by
    simp [List.flatMap_cons, he, he']
  have hrds : CombView.segsRds ((tg, p) :: (tg2, p2) :: rest) =
      p.rds ++ CombView.segsRds ((tg2, p2) :: rest) := by
    simp [CombView.segsRds, List.flatMap_cons]
  rw [hflat, hrds]
  have hstart : (t :: (ovs' ++ rest.flatMap fun s => s.2.pt.stmtsP)) = [] ∨
      ∃ t' r, (t :: (ovs' ++ rest.flatMap fun s => s.2.pt.stmtsP)) = t' :: r ∧ ¬ IsOvrStmt t' :=
    Or.inr ⟨t, _, rfl, ht⟩
  have hsk := (ptr_sk_both p hp).2 (CombView.segsRds ((tg2, p2) :: rest))
  rw [he] at hsk
  have hlen : stmtRcntL (s0 :: ovs) = p.rds.length := by rw [← he]; exact stmtsP_rcnt p hp
  have step : stmtSk ((p.rds ++ CombView.segsRds ((tg2, p2) :: rest)))
      (.block (s0 :: (ovs ++ (t :: (ovs' ++ rest.flatMap fun s => s.2.pt.stmtsP))))) =
      listSk (p.rds ++ CombView.segsRds ((tg2, p2) :: rest))
        (s0 :: (ovs ++ (t :: (ovs' ++ rest.flatMap fun s => s.2.pt.stmtsP)))) := by
    cases ovs with
    | nil => simp [stmtSk, stmtSkL, listSk]
    | cons o os => simp [stmtSk, stmtSkL, listSk]
  simp only [rhsSk]
  rw [step]
  simp only [listSk]
  rw [ovrSk_append_stop ovs _ _ _ hov hstart]
  rw [← hsk]
  simp only [listSk]

open CombProc in
/-- The skeleton's access leaves are exactly the reads. -/
theorem ptr_sk_leaves {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (ptrSk ptr).leaves = ptr.rds
  | .leafL t v rs, hok => by
      simpa [ptrSk, PTR.rds, PSk.leaves] using skRhs_leaves hok.2.1 (fragOkL_spec hok.2.2).1
  | .leafW n v rs, hok => by
      simpa [ptrSk, PTR.rds, PSk.leaves] using skRhs_leaves hok.2.1 (fragOkL_spec hok.2.2).1
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      simp [ptrSk, PTR.rds, PSk.leaves, skT_leaves c rc hc hg, ptr_sk_leaves a ha,
        ptr_sk_leaves b hb]
  | .ovr c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      simp [ptrSk, PTR.rds, PSk.leaves, skT_leaves c rc hc hg, ptr_sk_leaves a ha,
        ptr_sk_leaves b hb]
  | .blk a, hok => by
      simpa [ptrSk, PTR.rds, PSk.leaves] using ptr_sk_leaves a hok
  | .cases s rc its d, ⟨⟨hs, hg⟩, harms, hd⟩ => by
      simp only [ptrSk, PTR.rds, PSk.leaves, skT_leaves s rc hs hg, pskArmLeaves_arms its harms,
        plfr_leaves d hd]

/-! ## The instantiation of a condition -/

section cond
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- A bitwise gate in the self-determined context: both operands are fitted to their common width. -/
theorem instExpr2_gate_none (b : BinOp) (hb : b = .and ∨ b = .or ∨ b = .xor) (l r : PExpr) (w : Nat)
    (hl : selfWidth2 E elems l = some w) (hr : selfWidth2 E elems r = some w) :
    instExpr2 E elems none (.binary (.m0 b) l r) =
      .binary b (fitExpr2 E elems (some w) l) (fitExpr2 E elems (some w) r) := by
  rcases hb with rfl | rfl | rfl <;> simp [instExpr2, hl, hr]

/-- **A condition instantiates to its skeleton at width one** (self-determined: the context is `none`; WP-G S2:
a corollary of `skT_shape`, so the conditions are the expressions of the fragment, `!`, `&&`, `==`, ... included).
The skeleton of a condition has no word-level node (`skT_v1`), so its contract is the v1 one. -/
theorem cond_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → (skT v rs).WidthOkC σ dw 1 →
        instExpr2 E elems none v = (skT v rs).low σ dw 1 :=
  fun v rs h hf hacc hw =>
    (skT_shape C hdw v rs h hf hacc 1 (Sk.WidthOkC.toV1 _ (skT_v1 v rs rs h) hw)).2.2.1

end cond

/-! ## The instantiated tree is the skeleton's -/

section tree
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

open CombProc in
theorem mem_ptrArmsSk : ∀ {its : List (List PExpr × PLfR)} {it : List PExpr × PLfR}, it ∈ its →
    (it.1.map patLit, skRhs it.2.pl.val it.2.rds) ∈ ptrArmsSk its
  | (ps, a) :: rest, it, h => by
      simp only [ptrArmsSk, List.mem_cons]
      rcases List.mem_cons.mp h with rfl | h
      · left; rfl
      · right; exact mem_ptrArmsSk h

theorem foldl_fixed {α β : Type} (f : β → α → β) (b : β) :
    ∀ (l : List α), (∀ a ∈ l, f b a = b) → l.foldl f b = b
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.foldl_cons, h a (List.mem_cons_self ..)]
      exact foldl_fixed f b l (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The comparison width of a `case` whose subject and every pattern are `ws` bits wide. -/
theorem caseWidth2_eq (E : IEnv) (elems : List (String × Nat)) (s : PExpr) (ws : Nat)
    (hs : selfWidth2 E elems s = some ws) (items : List (List PExpr × PStmt))
    (h : ∀ it ∈ items, ∀ p ∈ it.1, selfWidth2 E elems p = some ws) :
    caseWidth2 E elems s items = some ws := by
  unfold caseWidth2
  rw [hs]
  apply foldl_fixed
  intro it hit
  apply foldl_fixed
  intro p hp
  simp [h it hit p hp]

theorem instPats2_lits (E : IEnv) (elems : List (String × Nat)) (ws : Nat) :
    ∀ ps : List PExpr, (∀ p ∈ ps, ∃ v, p = PExpr.lit v ∧ v.width = ws) →
      instPats2 E elems (some ws) ps = (ps.map patLit).map Expr2.lit
  | [], _ => by simp [instPats2]
  | p :: ps, h => by
      obtain ⟨v, rfl, hv⟩ := h p (List.mem_cons_self ..)
      have ih := instPats2_lits E elems ws ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [instPats2, patLit, fitExpr2_lit, hv, ih]

open CombProc in
theorem mem_items_arms : ∀ {its : List (List PExpr × PLfR)} {x : List PExpr × PStmt},
    x ∈ PLf.items (PLfR.arms its) → ∃ it ∈ its, x = (it.1, it.2.pl.toPStmt)
  | (ps, a) :: rest, x, h => by
      simp only [PLfR.arms, PLf.items, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨(ps, a), List.mem_cons_self .., rfl⟩
      · obtain ⟨it, hit, rfl⟩ := mem_items_arms h
        exact ⟨it, List.mem_cons_of_mem _ hit, rfl⟩

open CombProc in
theorem plfr_low_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc} :
    ∀ (a : PLfR), a.Ok ds tg → (∀ x ∈ a.rds, AccOK σ DW DG EW ns x) → ∀ {tw : Nat},
      (skRhs a.pl.val a.rds).WidthOkC σ dw tw →
        a.pl.low E elems tw = (skRhs a.pl.val a.rds).low σ dw tw
  | .leafL t v rs, hok, hacc, tw, hw => rhs_shapeC C hdw hok.2.1 (fragOkL_spec hok.2.2).1 hacc (fragOkL_co hok.2.2) hw
  | .leafW n v rs, hok, hacc, tw, hw => rhs_shapeC C hdw hok.2.1 (fragOkL_spec hok.2.2).1 hacc (fragOkL_co hok.2.2) hw

open CombProc in
theorem lowArms_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc}
    (ws tw : Nat) :
    ∀ (its : List (List PExpr × PLfR)), PLfR.ArmsOk ds tg its →
      (∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x) → PskArmsOk σ dw ws tw (ptrArmsSk its) →
        PLf.lowArms E elems (some ws) tw (PLfR.arms its) = pskArmsLow σ dw tw (ptrArmsSk its)
  | [], _, _, _ => by simp [PLfR.arms, PLf.lowArms, ptrArmsSk, pskArmsLow]
  | (ps, a) :: rest, harms, hacc, hw => by
      have hok := harms (ps, a) (List.mem_cons_self ..)
      have hw1 := hw (ps.map patLit, skRhs a.pl.val a.rds) (by simp [ptrArmsSk])
      have ih := lowArms_shape C hdw ws tw rest (fun x hx => harms x (List.mem_cons_of_mem _ hx))
        (fun x hx => hacc x (by simp [PLfR.armRds, hx]))
        (fun it hit => hw it (by simp [ptrArmsSk, hit]))
      have hpats : instPats2 E elems (some ws) ps = (ps.map patLit).map Expr2.lit :=
        instPats2_lits E elems ws ps (fun p hp => by
          obtain ⟨v, rfl⟩ := hok.1 p hp
          exact ⟨v, rfl, hw1.1 v (List.mem_map.mpr ⟨.lit v, hp, rfl⟩)⟩)
      have hval : a.pl.low E elems tw = (skRhs a.pl.val a.rds).low σ dw tw :=
        plfr_low_shape C hdw a hok.2 (fun x hx => hacc x (by simp [PLfR.armRds, hx])) hw1.2
      simp only [PLfR.arms, PLf.lowArms, ptrArmsSk, pskArmsLow, hpats, hval, ih]

open CombProc in
/-- **`PT.low` of an annotated tree is the lowering of its skeleton**: leaves through `rhs_shapeC`, conditions
through `cond_shape`. -/
theorem ptr_low_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) → ∀ tw,
      (ptrSk ptr).WidthOk σ dw tw → ptr.pt.low E elems tw = (ptrSk ptr).low σ dw tw
  | .leafL t v rs, hok, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [rhs_shapeC C hdw hok.2.1 (fragOkL_spec hok.2.2).1 hacc (fragOkL_co hok.2.2) hw]
  | .leafW n v rs, hok, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [rhs_shapeC C hdw hok.2.1 (fragOkL_spec hok.2.2).1 hacc (fragOkL_co hok.2.2) hw]
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩, hacc, tw, hw
  | .ovr c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [cond_shape C hdw c rc hc hg (fun x hx => hacc x (by simp [PTR.rds, hx])) hw.1,
        ptr_low_shape C hdw a ha (fun x hx => hacc x (by simp [PTR.rds, hx])) tw hw.2.1,
        ptr_low_shape C hdw b hb (fun x hx => hacc x (by simp [PTR.rds, hx])) tw hw.2.2]
  | .blk a, hok, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [ptr_low_shape C hdw a hok hacc tw hw]
  | .cases s rc its d, ⟨⟨hs, hg⟩, harms, hd⟩, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      obtain ⟨hself, hwarms, hwd⟩ := hw
      have haccS : ∀ x ∈ rc, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccA : ∀ x ∈ PLfR.armRds its, AccOK σ DW DG EW ns x :=
        fun x hx => hacc x (by simp [PTR.rds, hx])
      have haccD : ∀ x ∈ d.rds, AccOK σ DW DG EW ns x := fun x hx => hacc x (by simp [PTR.rds, hx])
      have hwS : (skT s rc).WidthOk σ dw ((skT s rc).width σ dw) :=
        Sk.selfOk_widthOk σ dw _ hself
      obtain ⟨hsw, -, -, -, hfit⟩ := skT_shape C hdw s rc hs hg haccS _ hwS
      have hpatw : ∀ it ∈ PLf.items (PLfR.arms its), ∀ p ∈ it.1,
          selfWidth2 E elems p = some ((skT s rc).width σ dw) := by
        intro it hit p hp
        obtain ⟨it', hit', rfl⟩ := mem_items_arms hit
        obtain ⟨v, rfl⟩ := (harms it' hit').1 p hp
        have := (hwarms (it'.1.map patLit, skRhs it'.2.pl.val it'.2.rds)
          (by exact mem_ptrArmsSk hit')).1 v (List.mem_map.mpr ⟨.lit v, hp, rfl⟩)
        simp [selfWidth2, this]
      have hsctx : caseWidth2 E elems s (PLf.items (PLfR.arms its)) =
          some ((skT s rc).width σ dw) := caseWidth2_eq E elems s _ hsw _ hpatw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low, hsctx]
      rw [hfit, Sk.low_irrel σ dw _ hself _ 0,
        lowArms_shape C hdw _ tw its harms haccA hwarms,
        plfr_low_shape C hdw d hd haccD hwd]

end tree

/-! ## The lowered tree is in the x-free fragment, with the skeleton's Boolean reading -/

theorem pskArms_xfOk {m : Design2} {σ : String → Int} {dw : String → Nat} {tw ws : Nat} :
    ∀ (its : List (List LVec × Sk)), pskArmsKnown its = true → PskArmsOk σ dw ws tw its →
      (∀ a ∈ pskArmLeaves its, LeafOk m σ dw a) →
        CombProc.CasesXfOk m tw ws (pskArmsLow σ dw tw its)
  | [], _, _, _ => by intro it hit; simp [pskArmsLow] at hit
  | (ps, a) :: rest, hkn, hw, hL => by
      simp only [pskArmsKnown, Bool.and_eq_true] at hkn
      obtain ⟨⟨hkp, hka⟩, hkr⟩ := hkn
      have hw1 := hw (ps, a) (List.mem_cons_self ..)
      have ihr := pskArms_xfOk rest hkr (fun it hit => hw it (List.mem_cons_of_mem _ hit))
        (fun x hx => hL x (by simp [pskArmLeaves, hx]))
      have hLa : ∀ x ∈ a.leaves, LeafOk m σ dw x := fun x hx => hL x (by simp [pskArmLeaves, hx])
      intro it hit
      simp only [pskArmsLow, List.mem_cons] at hit
      rcases hit with rfl | hit
      · refine ⟨fun p hp => ?_, low_xfWidthC a hka hw1.2 hLa⟩
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
        have hvk : v.knownB = true := List.all_eq_true.mp hkp v hv
        simp [Expr2.xfWidth, hvk, hw1.1 v hv]
      · exact ihr it hit

theorem caseBitAux_pskArms {m : Design2} {σ : String → Int} {dw : String → Nat} {tw ws : Nat}
    (env : String → Nat → Bool) (sv1 sv2 : Nat → Bool) (hsv : ∀ j, j < ws → sv1 j = sv2 j) :
    ∀ (its : List (List LVec × Sk)), pskArmsKnown its = true → PskArmsOk σ dw ws tw its →
      (∀ a ∈ pskArmLeaves its, LeafOk m σ dw a) → ∀ (dd : Expr2) (d2 : Nat → Bool) (k : Nat),
        k < tw → dd.xfBits m env k = d2 k →
        CombProc.caseBitAux m env ws sv1 (pskArmsLow σ dw tw its) dd k =
          XF.caseSel ws sv2 (pskArmsBit σ dw tw env its) d2 k
  | [], _, _, _, dd, d2, k, hk, hd => by
      simpa [CombProc.caseBitAux, pskArmsLow, pskArmsBit] using hd
  | (ps, a) :: rest, hkn, hw, hL, dd, d2, k, hk, hd => by
      simp only [pskArmsKnown, Bool.and_eq_true] at hkn
      obtain ⟨⟨hkp, hka⟩, hkr⟩ := hkn
      have hw1 := hw (ps, a) (List.mem_cons_self ..)
      have ihr := caseBitAux_pskArms env sv1 sv2 hsv rest hkr
        (fun it hit => hw it (List.mem_cons_of_mem _ hit))
        (fun x hx => hL x (by simp [pskArmLeaves, hx])) dd d2 k hk hd
      have hLa : ∀ x ∈ a.leaves, LeafOk m σ dw x := fun x hx => hL x (by simp [pskArmLeaves, hx])
      have hv := low_xfBitsC env a hka hw1.2 hLa k hk
      have hcond : ((ps.map Expr2.lit).any fun p => XF.eqv ws sv1 (p.xfBits m env)) =
          ((ps.map LVec.boolAt).any fun p => XF.eqv ws sv2 p) := by
        rw [List.any_map, List.any_map]
        apply congrArg (List.any ps)
        funext v
        exact XF.eqv_congr hsv (fun _ _ => rfl)
      simp only [CombProc.caseBitAux, pskArmsLow, pskArmsBit, XF.caseSel, hcond]
      split
      · exact hv
      · exact ihr

/-- The tree of a skeleton is in the x-free fragment at the target width. -/
theorem psk_xfOk {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat} :
    ∀ (p : PSk), p.knownB = true → p.WidthOk σ dw tw → (∀ a ∈ p.leaves, LeafOk m σ dw a) →
      (p.low σ dw tw).xfOk m tw
  | .leaf sk, hk, hw, hL => by
      simpa [PSk.low, CombProc.PTree.xfOk] using low_xfWidthC sk hk hw hL
  | .ite c a b, hk, hw, hL
  | .ovr c a b, hk, hw, hL => by
      simp only [PSk.knownB, Bool.and_eq_true] at hk
      simp only [PSk.WidthOk] at hw
      refine ⟨?_, psk_xfOk a hk.1.2 hw.2.1 (fun x hx => hL x (by simp [PSk.leaves, hx])),
        psk_xfOk b hk.2 hw.2.2 (fun x hx => hL x (by simp [PSk.leaves, hx]))⟩
      exact low_xfWidthC (tw := 1) c hk.1.1 hw.1 (fun x hx => hL x (by simp [PSk.leaves, hx]))
  | .blk a, hk, hw, hL => by
      simpa [PSk.low, CombProc.PTree.xfOk] using
        psk_xfOk a (by simpa [PSk.knownB] using hk) (by simpa [PSk.WidthOk] using hw)
          (fun x hx => hL x (by simpa [PSk.leaves] using hx))
  | .cases s its d, hk, hw, hL => by
      simp only [PSk.knownB, Bool.and_eq_true] at hk
      obtain ⟨⟨hks, hka⟩, hkd⟩ := hk
      simp only [PSk.WidthOk] at hw
      obtain ⟨hself, hwarms, hwd⟩ := hw
      have hLs : ∀ a ∈ s.leaves, LeafOk m σ dw a := fun x hx => hL x (by simp [PSk.leaves, hx])
      have hLa : ∀ a ∈ pskArmLeaves its, LeafOk m σ dw a :=
        fun x hx => hL x (by simp [PSk.leaves, hx])
      have hLd : ∀ a ∈ d.leaves, LeafOk m σ dw a := fun x hx => hL x (by simp [PSk.leaves, hx])
      have hss : (s.low σ dw 0).xfWidth m = some (s.width σ dw) := by
        rw [Sk.low_irrel σ dw s hself 0 (s.width σ dw)]
        exact low_xfWidthC s hks (Sk.selfOk_widthOkC σ dw s hself) hLs
      exact ⟨s.width σ dw, hss, pskArms_xfOk its hka hwarms hLa, low_xfWidthC d hkd hwd hLd⟩

/-- … and its Boolean reading (`PTree.bit`) is the skeleton's. -/
theorem psk_bit {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) :
    ∀ (p : PSk), p.knownB = true → p.WidthOk σ dw tw → (∀ a ∈ p.leaves, LeafOk m σ dw a) →
      ∀ k, k < tw → (p.low σ dw tw).bit m env k = p.bit σ dw tw env k
  | .leaf sk, hk, hw, hL, k, hk' => by
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit]
      exact low_xfBitsC env sk hk hw hL k hk'
  | .ite c a b, hk, hw, hL, k, hk'
  | .ovr c a b, hk, hw, hL, k, hk' => by
      simp only [PSk.knownB, Bool.and_eq_true] at hk
      simp only [PSk.WidthOk] at hw
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit]
      rw [low_xfBitsC (tw := 1) env c hk.1.1 hw.1 (fun x hx => hL x (by simp [PSk.leaves, hx])) 0
          (by omega),
        psk_bit env a hk.1.2 hw.2.1 (fun x hx => hL x (by simp [PSk.leaves, hx])) k hk',
        psk_bit env b hk.2 hw.2.2 (fun x hx => hL x (by simp [PSk.leaves, hx])) k hk']
  | .blk a, hk, hw, hL, k, hk' => by
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit]
      exact psk_bit env a (by simpa [PSk.knownB] using hk) (by simpa [PSk.WidthOk] using hw)
        (fun x hx => hL x (by simpa [PSk.leaves] using hx)) k hk'
  | .cases s its d, hk, hw, hL, k, hk' => by
      simp only [PSk.knownB, Bool.and_eq_true] at hk
      obtain ⟨⟨hks, hka⟩, hkd⟩ := hk
      simp only [PSk.WidthOk] at hw
      obtain ⟨hself, hwarms, hwd⟩ := hw
      have hLs : ∀ a ∈ s.leaves, LeafOk m σ dw a := fun x hx => hL x (by simp [PSk.leaves, hx])
      have hLa : ∀ a ∈ pskArmLeaves its, LeafOk m σ dw a :=
        fun x hx => hL x (by simp [PSk.leaves, hx])
      have hLd : ∀ a ∈ d.leaves, LeafOk m σ dw a := fun x hx => hL x (by simp [PSk.leaves, hx])
      have hss : (s.low σ dw 0).xfWidth m = some (s.width σ dw) := by
        rw [Sk.low_irrel σ dw s hself 0 (s.width σ dw)]
        exact low_xfWidthC s hks (Sk.selfOk_widthOkC σ dw s hself) hLs
      have hsb : ∀ j, j < s.width σ dw →
          (s.low σ dw 0).xfBits m env j = s.bitC σ dw (s.width σ dw) env j := by
        intro j hj
        rw [Sk.low_irrel σ dw s hself 0 (s.width σ dw)]
        exact low_xfBitsC env s hks (Sk.selfOk_widthOkC σ dw s hself) hLs j hj
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit, hss, Option.getD_some]
      exact caseBitAux_pskArms env _ _ hsb its hka hwarms hLa _ _ k hk'
        (low_xfBitsC env d hkd hwd hLd k hk')

/-- The lowered expression of the whole tree (`PTree.low`) has the target width. -/
theorem psk_low_xfWidth {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (p : PSk) (hk : p.knownB = true) (hw : p.WidthOk σ dw tw)
    (hL : ∀ a ∈ p.leaves, LeafOk m σ dw a) : ((p.low σ dw tw).low tw).xfWidth m = some tw :=
  CombProc.low_xfWidth m tw _ (psk_xfOk p hk hw hL)

/-- … and its Boolean reading is the skeleton's. -/
theorem psk_low_xfBits {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) (p : PSk) (hk : p.knownB = true) (hw : p.WidthOk σ dw tw)
    (hL : ∀ a ∈ p.leaves, LeafOk m σ dw a) (k : Nat) (hk' : k < tw) :
    ((p.low σ dw tw).low tw).xfBits m env k = p.bit σ dw tw env k := by
  rw [CombProc.low_xfBits m env tw _ (psk_xfOk p hk hw hL) k hk']
  exact psk_bit env p hk hw hL k hk'

/-- A one-part concatenation has its part's width and bits. -/
theorem xfWidth_concat_one {m : Design2} {X : Expr2} {w : Nat} (h : X.xfWidth m = some w) :
    (Expr2.concat #[X]).xfWidth m = some w := by
  simp [Expr2.xfWidth, Expr2.xfWidthSum, h]

theorem xfBits_concat_one {m : Design2} (X : Expr2) (env : String → Nat → Bool) (k : Nat) :
    (Expr2.concat #[X]).xfBits m env k = X.xfBits m env k := by
  simp [Expr2.xfBits, Expr2.catBits, Expr2.xfWidthSum]

end CombEq

/-! ## The obligations and the netlist view of a summary with procedural sites -/

namespace CombView
namespace Summary
open LeanModels.Sv.CombEq

variable (s : Summary)

/-- Every right-hand side is in the fragment of `sv_equations` (a procedural body was checked by the
recognizer) and its literals are known. -/
def EqFragL : Prop :=
  ∀ ls ∈ s.lsites, fragOkP ls.site.proc = true ∧ (rhsSk ls.site.proc ls.site.rds).knownB = true ∧
    ls.site.more = []

instance : Decidable s.EqFragL := by unfold EqFragL; infer_instance

/-- Operand widths equal the target width (conditions: one bit). -/
def WidthOblL (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
    (rhsSk ls.site.proc ls.site.rds).WidthOk σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2

/-- **The equations of one site**: the Boolean bits of its target window are the skeleton's bits. -/
def EqSiteL (σ σ' : String → Int) (st : SvState) (ls : LSite) : Prop :=
  ∀ k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
    st.boolAt (ls.site.tgt.win σ' (s.dw σ)).1 ((ls.site.tgt.win σ' (s.dw σ)).2.1 + k) =
      (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2 st.boolAt k

/-- The netlist view: every site's equations, at every valuation of its loops. -/
def EqsL (σ : String → Int) (st : SvState) : Prop :=
  ∀ ls ∈ s.lsites, LoopsN ls.hdrs σ fun σ' => s.EqSiteL σ σ' st ls

/-! ### The siblings for a body that writes SEVERAL windows (WP-G S1b, gate d)

The single-window route above is the one `sv_equations` has always used: its statements carry no mention of
further windows, so its normal forms and its cost are the ones of the designs without them. A body of several
windows has these siblings (`EqFragM`, `WidthOblM`, `EqsM`, `KnownsM`, `SrcSM`, `CoverOblM`, and the producer
`eq_viewLM`); the tactic selects them only when some site has a further window (a syntactic check of the
recognizer's summary, not a simp guard inside the single-window statements). -/

/-- Every right-hand side is in the fragment of `sv_equations`, for every window of a body: the first window's
skeleton (`rhsSk`) and each further window's (`procSks`, tail) have known literals. -/
def EqFragM : Prop :=
  ∀ ls ∈ s.lsites, fragOkP ls.site.proc = true ∧ (rhsSk ls.site.proc ls.site.rds).knownB = true ∧
    ∀ sk ∈ (procSks ls.site.proc ls.site.rds).tail, sk.knownB = true

instance : Decidable s.EqFragM := by unfold EqFragM; infer_instance

/-- Operand widths equal the target width, for the head window of every site and for every further window. -/
def WidthOblM (σ : String → Int) : Prop :=
  (∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
    (rhsSk ls.site.proc ls.site.rds).WidthOk σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2) ∧
  ∀ ls ∈ s.lsites, ∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
    Loops.all ls.hdrs σ fun σ' => p.2.WidthOk σ' (s.dw σ) (p.1.win σ' (s.dw σ)).2.2

/-- The netlist view of a body of several windows: the equations of every site's head window, then of every
further window (one fact per window, in source order). -/
def EqsM (σ : String → Int) (st : SvState) : Prop :=
  (∀ ls ∈ s.lsites, LoopsN ls.hdrs σ fun σ' => s.EqSiteL σ σ' st ls) ∧
  ∀ ls ∈ s.lsites, ∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
    LoopsN ls.hdrs σ fun σ' =>
      ∀ k, k < (p.1.win σ' (s.dw σ)).2.2 →
        st.boolAt (p.1.win σ' (s.dw σ)).1 ((p.1.win σ' (s.dw σ)).2.1 + k) =
          p.2.bit σ' (s.dw σ) (p.1.win σ' (s.dw σ)).2.2 st.boolAt k

/-- The knownness facts of a body of several windows: one per site (its head window), then one per further
window. -/
def KnownsM (σ : String → Int) (st : SvState) : Prop :=
  (∀ ls ∈ s.lsites, LoopsN ls.hdrs σ fun σ' => s.KnownSite σ σ' st ls) ∧
  ∀ ls ∈ s.lsites, ∀ a ∈ ls.site.more, LoopsN ls.hdrs σ fun σ' =>
    ∀ k, k < (a.win σ' (s.dw σ)).2.2 →
      (∃ v, SvState.lookup st (a.win σ' (s.dw σ)).1 = some v ∧
        v.width = s.dw σ (a.win σ' (s.dw σ)).1) ∧
      KnownBit st (a.win σ' (s.dw σ)).1 ((a.win σ' (s.dw σ)).2.1 + k)

/-- Bit `p` of signal `n` has a source: an input bit, or a bit inside the head window of some site, or inside a
further window of some site. -/
def SrcSM (σ : String → Int) (n : String) (p : Nat) : Prop :=
  ((n ∈ s.inputNames ∧ p < s.dw σ n) ∨
    ∃ b ∈ s.lsites, b.site.tgt.name = n ∧
      LoopsE b.hdrs σ fun σ2 =>
        (b.site.tgt.win σ2 (s.dw σ)).2.1 ≤ p ∧
          p < (b.site.tgt.win σ2 (s.dw σ)).2.1 + (b.site.tgt.win σ2 (s.dw σ)).2.2) ∨
  ∃ b ∈ s.lsites, ∃ a ∈ b.site.more, a.name = n ∧
    LoopsE b.hdrs σ fun σ2 =>
      (a.win σ2 (s.dw σ)).2.1 ≤ p ∧ p < (a.win σ2 (s.dw σ)).2.1 + (a.win σ2 (s.dw σ)).2.2

/-- Every bit a read observes has a source (a body of several windows). -/
def CoverOblM (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
    ∀ r ∈ ls.site.rds, ∀ k, k < (r.win σ' (s.dw σ)).2.2 →
      s.SrcSM σ r.name ((r.win σ' (s.dw σ)).2.1 + k)

end Summary
end CombView

namespace CombEq
open CombView

/-- All-or-nothing: a process list ending in a loud process does not lower. -/
theorem lowerProcs_push_unsupported (d : Design2) :
    ∀ (ps : List Process2) (k t : String), d.lowerProcs (ps ++ [.unsupported k t]) = none
  | [], k, t => by simp [Design2.lowerProcs, Process2.lowerComb]
  | p :: ps, k, t => by
      simp only [List.cons_append, Design2.lowerProcs]
      cases hp : p.lowerComb d with
      | none => rfl
      | some q => simp [Option.bind, lowerProcs_push_unsupported d ps k t]

/-- **A design that lowers IS the unguarded instantiation**: if the guarded instantiation lowers, the driver
guard passed (otherwise it carries the loud `PortConn:driver` process, which does not lower). -/
theorem instantiateGD2_eq_of_lowerable {d : PDesign} {args : List Int} {m d' : Design2}
    (hm : d.instantiate2 args (PDesign.surfaceFuel args) = .ok m)
    (hl : (d.instantiateGD2 args).lowerComb = some d') : d.instantiateGD2 args = m := by
  have hG : d.instantiateGD2 args = d.driverGuard m := by
    unfold PDesign.instantiateGD2 PDesign.instantiateG2
    rw [hm]
    rfl
  rw [hG] at hl ⊢
  unfold PDesign.driverGuard Design2.driverGuard at hl ⊢
  by_cases hd : driversOk d.declNames d.inputNames m.processes.toList = true
  · simp only [hd, if_true]
  · exfalso
    simp only [hd] at hl
    unfold Design2.lowerComb at hl
    simp [Array.toList_push, lowerProcs_push_unsupported] at hl

/-- A guarded instantiation that lowers is a successful instantiation (a failed one collapses into the
loud error design, which does not lower). -/
theorem instantiate2_ok_of_lowerable {d : PDesign} {args : List Int} {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d') :
    ∃ m, d.instantiate2 args (PDesign.surfaceFuel args) = .ok m := by
  unfold PDesign.instantiateGD2 PDesign.instantiateG2 at hl
  cases h : d.instantiate2 args (PDesign.surfaceFuel args) with
  | ok m => exact ⟨m, rfl⟩
  | timeout =>
    exfalso
    rw [h] at hl
    simp [Design2.errorDesign, Design2.lowerComb, Design2.lowerProcs, Process2.lowerComb] at hl
  | unsupported msg =>
    exfalso
    rw [h] at hl
    simp [Design2.errorDesign, Design2.lowerComb, Design2.lowerProcs, Process2.lowerComb] at hl

/-- **The declarations of a design that lowers** are the summary's, evaluated at the valuation: only the
parameter stage and the structural check are needed (the interface theorem needs no process fact). -/
theorem declsL_of_lowerable {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (h1 : d.paramEnv2 args = .ok env)
    (hag : Agrees σ env s.params) (hok : s.StructOk) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d') :
    (d.instantiateGD2 args).decls.toList = s.decls.map (DeclT.toDecl σ) := by
  obtain ⟨m, hm⟩ := instantiate2_ok_of_lowerable hl
  rw [instantiateGD2_eq_of_lowerable hm hl]
  obtain ⟨env', decls, elems, gens, h1', h2, -, -, -, hdecls, -⟩ :=
    PDesign.instantiate2_processes hm
  rw [hdecls]
  rw [h1] at h1'
  have henv : env = env' := Res.ok.inj h1'
  subst henv
  obtain ⟨-, -, -, -, hsd, -, -, -⟩ := summaryP_spec hs
  obtain ⟨-, -, -, -, -, hdecl, -, -⟩ := hok
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.intVal? n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2' := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  rw [h2] at h2'
  exact Res.ok.inj h2'

/-- The tactic's form of `declsL_of_lowerable` (valuation `s.val args`). -/
theorem declsL_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d') :
    (d.instantiateGD2 args).decls.toList = s.decls.map (DeclT.toDecl (s.val args)) :=
  declsL_of_lowerable hs h1 (Agrees_of_map hag) hok hl

/-! ## The windows of a body that writes several: placed skeletons, and the bits of the lowered concatenation -/

/-- `Win.placed` is bounded by the total width. -/
theorem placed_bound : ∀ (ws : List Win) (w : Win) (off : Nat), (w, off) ∈ Win.placed ws →
    off + w.2.2 ≤ Win.sumWidth ws
  | [], _, _, h => by simp [Win.placed] at h
  | w0 :: rest, w, off, h => by
      simp only [Win.placed, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp [Win.sumWidth_cons]; omega
      · have := placed_bound rest w off h
        simp only [Win.sumWidth_cons]; omega

open CombProc in
/-- The windows of the segments of a body, each with its offset in the concatenated target (the total width of
the windows after it) and the annotated skeleton of its segment. -/
def placedSegs (σ' : String → Int) (dw : String → Nat) : List (Acc × PTR) → List (Win × Nat × PSk)
  | [] => []
  | t :: rest =>
      (t.1.win σ' dw, Win.sumWidth (rest.map fun u => u.1.win σ' dw), ptrSk t.2) :: placedSegs σ' dw rest

open CombProc in
theorem placedSegs_placed (σ' : String → Int) (dw : String → Nat) :
    ∀ (segs : List (Acc × PTR)), ∀ x ∈ placedSegs σ' dw segs,
      (x.1, x.2.1) ∈ Win.placed (segs.map fun u => u.1.win σ' dw)
  | [], x, hx => by simp [placedSegs] at hx
  | t :: rest, x, hx => by
      simp only [placedSegs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [Win.placed]
      · simp only [List.map_cons, Win.placed, List.mem_cons]
        exact Or.inr (placedSegs_placed σ' dw rest x hx)

open CombProc in
theorem placedSegs_bound (σ' : String → Int) (dw : String → Nat) :
    ∀ (segs : List (Acc × PTR)), ∀ x ∈ placedSegs σ' dw segs,
      x.2.1 + x.1.2.2 ≤ Win.sumWidth (segs.map fun u => u.1.win σ' dw) := fun segs x hx =>
  placed_bound _ _ _ (placedSegs_placed σ' dw segs x hx)

open CombProc in
theorem mem_placedSegs (σ' : String → Int) (dw : String → Nat) :
    ∀ (segs : List (Acc × PTR)) (t : Acc × PTR), t ∈ segs →
      ∃ off, (t.1.win σ' dw, off, ptrSk t.2) ∈ placedSegs σ' dw segs
  | [], t, h => by simp at h
  | u :: rest, t, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨Win.sumWidth (rest.map fun v => v.1.win σ' dw), by simp only [placedSegs]; exact List.mem_cons_self ..⟩
      · obtain ⟨off, hoff⟩ := mem_placedSegs σ' dw rest t h
        exact ⟨off, by simp [placedSegs, hoff]⟩

/-- The first part of a concatenation sits above the width of the rest, the rest below. -/
theorem catBits_cons_head {d : Design2} {env : String → Nat → Bool} {x : Expr2} {l : List Expr2}
    {m : Nat} (hl : Expr2.xfWidthSum d l = some m) (k : Nat) :
    Expr2.catBits d env (x :: l) (m + k) = x.xfBits d env k := by
  simp only [Expr2.catBits, hl, Option.getD_some]
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem catBits_cons_tail {d : Design2} {env : String → Nat → Bool} {x : Expr2} {l : List Expr2}
    {m : Nat} (hl : Expr2.xfWidthSum d l = some m) {k : Nat} (hk : k < m) :
    Expr2.catBits d env (x :: l) k = Expr2.catBits d env l k := by
  simp only [Expr2.catBits, hl, Option.getD_some]
  rw [if_pos hk]

open CombProc in
/-- **The lowered parts side by side** (`{E₀, …, Eₖ}`, one per segment): their widths add up to the total width of
the windows, and the Boolean bit of each placed window is the bit of its segment's skeleton. -/
theorem parts_bits {d' : Design2} {σ' : String → Int} {dw : String → Nat} :
    ∀ (segs : List (Acc × PTR)),
      (∀ t ∈ segs, (ptrSk t.2).knownB = true ∧ (ptrSk t.2).WidthOk σ' dw (t.1.win σ' dw).2.2 ∧
        ∀ a ∈ (ptrSk t.2).leaves, LeafOk d' σ' dw a) →
      Expr2.xfWidthSum d' (segs.map fun t =>
          ((ptrSk t.2).low σ' dw (t.1.win σ' dw).2.2).low (t.1.win σ' dw).2.2) =
        some (Win.sumWidth (segs.map fun u => u.1.win σ' dw)) ∧
      ∀ x ∈ placedSegs σ' dw segs, ∀ (env : String → Nat → Bool) (k : Nat), k < x.1.2.2 →
        Expr2.catBits d' env (segs.map fun t =>
            ((ptrSk t.2).low σ' dw (t.1.win σ' dw).2.2).low (t.1.win σ' dw).2.2) (x.2.1 + k) =
          x.2.2.bit σ' dw x.1.2.2 env k
  | [], _ => by simp [Expr2.xfWidthSum, Win.sumWidth, placedSegs]
  | t :: rest, h => by
      obtain ⟨hk, hw, hl⟩ := h t (List.mem_cons_self ..)
      have hrest := parts_bits (d' := d') (σ' := σ') (dw := dw) rest
        (fun u hu => h u (List.mem_cons_of_mem _ hu))
      obtain ⟨hsum, hbits⟩ := hrest
      have hx : (((ptrSk t.2).low σ' dw (t.1.win σ' dw).2.2).low (t.1.win σ' dw).2.2).xfWidth d' =
          some (t.1.win σ' dw).2.2 := psk_low_xfWidth _ hk hw hl
      refine ⟨by simp [Expr2.xfWidthSum, hx, hsum, Win.sumWidth_cons], ?_⟩
      intro x hx' env k hk'
      simp only [placedSegs, List.mem_cons] at hx'
      rcases hx' with rfl | hx'
      · simp only [List.map_cons]
        rw [catBits_cons_head hsum]
        exact psk_low_xfBits env _ hk hw hl k hk'
      · simp only [List.map_cons]
        have hb := placedSegs_bound σ' dw rest x hx'
        rw [catBits_cons_tail hsum (by omega)]
        exact hbits x hx' env k hk'

open CombProc in
/-- **The instantiated process of a site of ONE window lowers to an assign with the skeleton's Boolean reading**,
for an assign site and for a procedural body of one window alike (`site_lowL` is the statement for every site). -/
theorem site_lowL_single {s : Summary} {σ : String → Int} {envD : IEnv} {elems : List (String × Nat)}
    {args : List Int} {M d' : Design2}
    (hdecl : M.decls.toList = s.decls.map (DeclT.toDecl σ))
    (hdecl' : d'.decls.toList = s.decls.map (DeclT.toDecl σ))
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hself : s.NoSelfRead σ)
    (hfrag : ∀ ls ∈ s.lsites, fragOkP ls.site.proc = true ∧ (rhsSk ls.site.proc ls.site.rds).knownB = true)
    (hwid : ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
      (rhsSk ls.site.proc ls.site.rds).WidthOk σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2)
    (hbit : s.BitReadObl σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site)
    {ls : LSite} (hls : ls ∈ s.lsites) (hmore : ls.site.more = []) {σ' : String → Int} {E' : IEnv}
    (hr : ReachE ls.hdrs σ envD σ' E') :
    ∃ (t : Lhs2) (e : Expr2), lowP M (instProcess2 E' elems ls.site.proc) = .assign t e ∧
      t.wins d' = [ls.site.tgt.win σ' (s.dw σ)] ∧
      e.xfWidth d' = some (ls.site.tgt.win σ' (s.dw σ)).2.2 ∧
      ∀ env k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
        e.xfBits d' env k =
          (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2 env k := by
  have hb : ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ' r :=
    (Loops.all_iff _ _ _).mp (hbit ls hls) σ' (ReachE_Reach hr)
  obtain ⟨C', hso, hl⟩ := site_ok C hok hauto hin hls hr hb
  have hw := (Loops.all_iff _ _ _).mp (hwid ls hls) σ' (ReachE_Reach hr)
  have hdw : ∀ n, (s.DW σ n).isSome = true → s.DW σ n = some (s.dw σ n) :=
    fun n h => dw_some n h
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl0, hacc, hkeys⟩ := hok'
  have hfindTgt : (s.find ls.site.tgt.name).isSome = true :=
    find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
  have hleaf : ∀ a ∈ ls.site.rds, LeafOk d' σ' (s.dw σ) a := by
    intro a ha
    obtain ⟨hdn, hpos, hle⟩ := hl a ha
    refine ⟨?_, hle, hpos⟩
    rw [declWidth_eq hdecl', dw_some a.name (by simpa [Summary.DW] using hdn)]
  have hwins : (ls.site.tgt.lhs σ').wins d' = [ls.site.tgt.win σ' (s.dw σ)] :=
    Lhs2.wins_of_windows? (acc_windows (σs := σ') hdecl' ls.site.tgt hfindTgt)
  obtain ⟨pos, p, hp⟩ := hsites ls hls
  rcases siteOfP?_cases hp with hp0 | ⟨b, tg, ptr, rfl, htree, hst⟩ | ⟨b, segs, rfl, -, hms⟩
  · -- an assign site
    have hpp := siteOf?_proc hp0
    subst hpp
    have hne : ∀ b, ls.site.proc ≠ .alwaysComb b := fun b hb => by
      rw [hb] at hp0
      simp [siteOf?] at hp0
    have hf : fragOk (rhsOf ls.site.proc) = true := by
      have := (hfrag ls hls).1
      rwa [fragOkP_of_ne hne] at this
    have hk : (skRhs (rhsOf ls.site.proc) ls.site.rds).knownB = true := by
      simpa [rhsSk_of_ne hne, PSk.knownB] using (hfrag ls hls).2
    have hw' : (skRhs (rhsOf ls.site.proc) ls.site.rds).WidthOkC σ' (s.dw σ)
        (ls.site.tgt.win σ' (s.dw σ)).2.2 := by
      simpa [rhsSk_of_ne hne, PSk.WidthOk] using hw
    have hshape := proc_shapeC C' hdw hp0 hso (site_co hok hin hls (ReachE_Reach hr)) hf hw'
    have hleaves := site_sk hp0 hf
    have hlv : ∀ a ∈ (skRhs (rhsOf ls.site.proc) ls.site.rds).leaves, LeafOk d' σ' (s.dw σ) a :=
      fun a ha => hleaf a (by rwa [hleaves] at ha)
    refine ⟨ls.site.tgt.lhs σ',
      (skRhs (rhsOf ls.site.proc) ls.site.rds).low σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2,
      ?_, hwins, low_xfWidthC _ hk hw' hlv, ?_⟩
    · unfold lowP
      rw [hshape] <;> rfl
    · intro env k hk'
      rw [rhsSk_of_ne hne]
      exact low_xfBitsC env _ hk hw' hlv k hk'
  · -- a procedural site
    have hproc : ls.site.proc = .alwaysComb b := congrArg TSite.proc hst
    have htg : ls.site.tgt = tg := congrArg TSite.tgt hst
    have hrds : ls.site.rds = ptr.rds := congrArg TSite.rds hst
    obtain ⟨hbb, hpok⟩ := treeStmt?_spec s.decls b tg ptr htree
    have hproc2 : instProcess2 E' elems ls.site.proc = instProcess2 E' elems ptr.pt.toProc := by
      rw [hproc, PT.toProc, hbb]
    have hatg := hso ls.site.tgt (List.mem_cons_self ..)
    have haccP : ∀ a ∈ ptr.rds,
        AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a :=
      fun a ha => hso a (List.mem_cons_of_mem _ (by rw [hrds]; exact ha))
    have hmem : ls.inst σ' (s.dw σ) ∈ s.insts σ envD :=
      mem_insts.mpr ⟨ls, hls, σ', ReachE_Reach hr, rfl⟩
    obtain ⟨dw0, hdw0, hle0⟩ := inrange_insts hok hauto hin hmem
    have hname : (ls.inst σ' (s.dw σ)).win.1 = ls.site.tgt.name :=
      Acc.win_name σ' (s.dw σ) ls.site.tgt
    rw [hname] at hdw0
    have hdwe : s.DW σ ls.site.tgt.name = some (s.dw σ ls.site.tgt.name) :=
      dw_some ls.site.tgt.name (by rw [hdw0]; rfl)
    have hdweq : dw0 = s.dw σ ls.site.tgt.name := Option.some.inj (hdw0.symm.trans hdwe)
    have hle : (ls.site.tgt.win σ' (s.dw σ)).2.1 + (ls.site.tgt.win σ' (s.dw σ)).2.2 ≤
        s.dw σ ls.site.tgt.name := hdweq ▸ hle0
    have hpok' : ptr.Ok s.decls ls.site.tgt := by rw [htg]; exact hpok
    have hself1 := (Loops.all_iff _ _ _).mp (hself.all ls hls (by rw [hproc]; rfl)) σ' (ReachE_Reach hr)
    have hself' : ∀ a ∈ ptr.rds,
        (a.rd σ').overlaps (ls.site.tgt.win σ' (s.dw σ)) = false :=
      fun a ha => hself1 a (by rw [hrds]; exact ha) ls.site.tgt (List.mem_cons_self ..)
    have hL := lower_site C' (dw := s.dw σ) hdw (declWidth_eq hdecl) hatg hle ptr hpok' haccP hself'
    have hsk : rhsSk ls.site.proc ls.site.rds = ptrSk ptr := by
      rw [hproc, hrds, ← hbb]
      exact ptr_sk_eq ptr hpok
    have hkn : (ptrSk ptr).knownB = true := by rw [← hsk]; exact (hfrag ls hls).2
    have hwk : (ptrSk ptr).WidthOk σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2 := by
      rw [← hsk]; exact hw
    have hlv : ∀ a ∈ (ptrSk ptr).leaves, LeafOk d' σ' (s.dw σ) a := fun a ha =>
      hleaf a (by rw [ptr_sk_leaves ptr hpok'] at ha; rw [hrds]; exact ha)
    have hlow := ptr_low_shape C' hdw ptr hpok' haccP _ hwk
    refine ⟨.concat [(ls.site.tgt.win σ' (s.dw σ)).lhs],
      .concat #[((ptrSk ptr).low σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2).low
        (ls.site.tgt.win σ' (s.dw σ)).2.2], ?_, wins_concat_win d' _, ?_, ?_⟩
    · simp only [lowP, hproc2, hL, hlow, Option.getD_some]
    · exact xfWidth_concat_one (psk_low_xfWidth _ hkn hwk hlv)
    · intro env k hk'
      rw [xfBits_concat_one, psk_low_xfBits env _ hkn hwk hlv k hk', hsk]
  · -- a body of several windows: the equations are the next gate; the fragment check refuses it
    exact absurd hmore (multiSite_shape hms).2.2.2


open CombProc in
/-- **The instantiated process of a site lowers to an assign with the skeleton's Boolean reading**, for an
assign site and for a procedural site alike. (The single-window route: `EqFragL` says every site has one window.
`site_lowLM` is the statement for a body of several windows.) -/
theorem site_lowL {s : Summary} {σ : String → Int} {envD : IEnv} {elems : List (String × Nat)}
    {args : List Int} {M d' : Design2}
    (hdecl : M.decls.toList = s.decls.map (DeclT.toDecl σ))
    (hdecl' : d'.decls.toList = s.decls.map (DeclT.toDecl σ))
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hself : s.NoSelfRead σ)
    (hfrag : s.EqFragL) (hwid : s.WidthOblL σ) (hbit : s.BitReadObl σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site)
    {ls : LSite} (hls : ls ∈ s.lsites) {σ' : String → Int} {E' : IEnv}
    (hr : ReachE ls.hdrs σ envD σ' E') :
    ∃ (t : Lhs2) (e : Expr2), lowP M (instProcess2 E' elems ls.site.proc) = .assign t e ∧
      t.wins d' = [ls.site.tgt.win σ' (s.dw σ)] ∧
      e.xfWidth d' = some (ls.site.tgt.win σ' (s.dw σ)).2.2 ∧
      ∀ env k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
        e.xfBits d' env k =
          (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2 env k :=
  site_lowL_single hdecl hdecl' C hok hauto hin hself
    (fun b hb => ⟨(hfrag b hb).1, (hfrag b hb).2.1⟩) hwid hbit hsites hls (hfrag ls hls).2.2 hr

theorem mem_zip_map {α : Type} {β γ : Type} (f : α → β) (g : α → γ) :
    ∀ (l : List α) (t : α), t ∈ l → (f t, g t) ∈ (l.map f).zip (l.map g)
  | [], t, h => by simp at h
  | u :: rest, t, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_zip_map f g rest t h)

theorem mem_of_zip_map {α : Type} {β γ : Type} (f : α → β) (g : α → γ) :
    ∀ (l : List α) (p : β × γ), p ∈ (l.map f).zip (l.map g) → ∃ t ∈ l, p = (f t, g t)
  | [], p, h => by simp at h
  | u :: rest, p, h => by
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨u, List.mem_cons_self .., rfl⟩
      · obtain ⟨t, ht, rfl⟩ := mem_of_zip_map f g rest p h
        exact ⟨t, List.mem_cons_of_mem _ ht, rfl⟩

/-- **What a lowered site says about its equations**: the lowered target has exactly the windows `wins`, the lowered
expression has their total width, and for every placed window of `W` the Boolean bit of the expression at the
window's offset is the bit of its skeleton. -/
def SiteLow (d' : Design2) (σ' : String → Int) (dw : String → Nat) (t : Lhs2) (e : Expr2) (wins : List Win)
    (W : List (Win × Nat × PSk)) : Prop :=
  t.wins d' = wins ∧ e.xfWidth d' = some (Win.sumWidth wins) ∧
  ∀ x ∈ W, (x.1, x.2.1) ∈ Win.placed wins ∧
    ∀ (env : String → Nat → Bool) (k : Nat), k < x.1.2.2 →
      e.xfBits d' env (x.2.1 + k) = x.2.2.bit σ' dw x.1.2.2 env k

open CombProc in
/-- **The instantiated process of a body of SEVERAL windows lowers to ONE assign of all of them**, each placed
window's Boolean bits being its segment's skeleton's. -/
theorem site_lowL_multi {s : Summary} {σ : String → Int} {envD : IEnv} {elems : List (String × Nat)}
    {args : List Int} {M d' : Design2}
    (hdecl : M.decls.toList = s.decls.map (DeclT.toDecl σ))
    (hdecl' : d'.decls.toList = s.decls.map (DeclT.toDecl σ))
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hwithin : s.DisjWithin σ) (hself : s.NoSelfRead σ)
    (hfrag : s.EqFragM) (hwid : s.WidthOblM σ) (hbit : s.BitReadObl σ)
    {ls : LSite} (hls : ls ∈ s.lsites) {σ' : String → Int} {E' : IEnv}
    (hr : ReachE ls.hdrs σ envD σ' E') {b : PStmt} {segs : List (Acc × PTR)}
    (hb : multiSegs? s.decls b = .ok segs) (hproc : ls.site.proc = .alwaysComb b)
    (hrds : ls.site.rds = CombView.segsRds segs) (haccs : ls.site.tgt :: ls.site.more = segs.map Prod.fst)
    (hmore : ls.site.more ≠ []) :
    ∃ (t : Lhs2) (e : Expr2), lowP M (instProcess2 E' elems ls.site.proc) = .assign t e ∧
      SiteLow d' σ' (s.dw σ) t e (segs.map fun u => u.1.win σ' (s.dw σ)) (placedSegs σ' (s.dw σ) segs) ∧
      (∃ off, (ls.site.tgt.win σ' (s.dw σ), off, rhsSk ls.site.proc ls.site.rds) ∈
        placedSegs σ' (s.dw σ) segs) ∧
      (∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
        ∃ off, (p.1.win σ' (s.dw σ), off, p.2) ∈ placedSegs σ' (s.dw σ) segs) ∧
      (∀ a ∈ ls.site.tgt :: ls.site.more, a.win σ' (s.dw σ) ∈ segs.map fun u => u.1.win σ' (s.dw σ)) := by
  have hc := siteCtx_of_reach C hok hauto hin hls hr
  obtain ⟨ss, hbss, hbody, hsok, -⟩ := multiSegs?_spec s.decls b segs hb
  have hL := multi_lowers hdecl hok hauto hwithin hself hls hc hb hproc hrds haccs
  -- the segments: at least two
  obtain ⟨tg, p0, tg2, p2, rest, rfl⟩ : ∃ tg p0 tg2 p2 rest, segs = (tg, p0) :: (tg2, p2) :: rest := by
    cases segs with
    | nil => simp at haccs
    | cons t1 ts =>
        cases ts with
        | nil => simp at haccs; exact absurd haccs.2 hmore
        | cons t2 ts2 => exact ⟨t1.1, t1.2, t2.1, t2.2, ts2, rfl⟩
  have hb1 : b = .block (((tg, p0) :: (tg2, p2) :: rest).flatMap fun u => u.2.pt.stmtsP) := by
    have : bodyP2 ((tg, p0) :: (tg2, p2) :: rest) = .block ss := hbody
    rw [hbss]
    simpa [bodyP2] using this.symm
  have hsks := procSks_multi ((tg, p0) :: (tg2, p2) :: rest) b (by rw [hb1]; rfl) ⟨_, hb1⟩ hsok
  have hrhs : rhsSk ls.site.proc ls.site.rds = ptrSk p0 := by
    rw [hproc, hrds, hb1]; exact rhsSk_multi tg tg2 p0 p2 rest hsok
  -- facts per segment: known, widths, leaves
  have hb' : ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ' r :=
    (Loops.all_iff _ _ _).mp (hbit ls hls) σ' (ReachE_Reach hr)
  obtain ⟨C', hso, hl⟩ := site_ok C hok hauto hin hls hr hb'
  have hleaf : ∀ a ∈ ls.site.rds, LeafOk d' σ' (s.dw σ) a := by
    intro a ha
    obtain ⟨hdn, hpos, hle⟩ := hl a ha
    refine ⟨?_, hle, hpos⟩
    rw [declWidth_eq hdecl', dw_some a.name (by simpa [Summary.DW] using hdn)]
  have hwid1 := (Loops.all_iff _ _ _).mp (hwid.1 ls hls) σ' (ReachE_Reach hr)
  have hwid2 := hwid.2
  have hmoreEq : ls.site.more = ((tg2, p2) :: rest).map Prod.fst := by
    have h := congrArg List.tail haccs
    simpa using h
  have htg : ls.site.tgt = tg := by
    have h := congrArg List.head? haccs
    simpa using h
  have hsks' : procSks ls.site.proc ls.site.rds =
      ((tg, p0) :: (tg2, p2) :: rest).map fun u => ptrSk u.2 := by
    rw [hproc, hrds]; exact hsks
  have htail : (procSks ls.site.proc ls.site.rds).tail = ((tg2, p2) :: rest).map fun u => ptrSk u.2 := by
    rw [hsks']; rfl
  have hfacts : ∀ t ∈ (tg, p0) :: (tg2, p2) :: rest, (ptrSk t.2).knownB = true ∧
      (ptrSk t.2).WidthOk σ' (s.dw σ) (t.1.win σ' (s.dw σ)).2.2 ∧
      ∀ a ∈ (ptrSk t.2).leaves, LeafOk d' σ' (s.dw σ) a := by
    intro t ht
    have hleaves : ∀ a ∈ (ptrSk t.2).leaves, LeafOk d' σ' (s.dw σ) a := fun a ha => by
      rw [ptr_sk_leaves t.2 (hsok t ht)] at ha
      exact hleaf a (by rw [hrds]; exact List.mem_flatMap.mpr ⟨t, ht, ha⟩)
    rcases List.mem_cons.mp ht with rfl | ht'
    · refine ⟨?_, ?_, hleaves⟩
      · rw [← hrhs]; exact (hfrag ls hls).2.1
      · rw [← hrhs, ← htg]; exact hwid1
    · refine ⟨?_, ?_, hleaves⟩
      · apply (hfrag ls hls).2.2
        rw [htail]
        exact List.mem_map.mpr ⟨t, ht', rfl⟩
      · have hz := mem_zip_map Prod.fst (fun u : Acc × PTR => ptrSk u.2) _ t ht'
        have := hwid2 ls hls (t.1, ptrSk t.2) (by
          rw [hmoreEq, htail]
          exact hz)
        exact (Loops.all_iff _ _ _).mp this σ' (ReachE_Reach hr)
  obtain ⟨hsum, hbits⟩ := parts_bits (d' := d') (σ' := σ') (dw := s.dw σ) _ hfacts
  -- the lowered process
  have hlow : lowP M (instProcess2 E' elems ls.site.proc) = .assign
      (.concat ((((tg, p0) :: (tg2, p2) :: rest).map fun t => t.1.win σ' (s.dw σ)).map Win.lhs))
      (.concat ((((tg, p0) :: (tg2, p2) :: rest).map fun t =>
        ((ptrSk t.2).low σ' (s.dw σ) (t.1.win σ' (s.dw σ)).2.2).low (t.1.win σ' (s.dw σ)).2.2)).toArray) := by
    have hlow' : ∀ t ∈ (tg, p0) :: (tg2, p2) :: rest,
        t.2.pt.low E' elems (t.1.win σ' (s.dw σ)).2.2 = (ptrSk t.2).low σ' (s.dw σ) (t.1.win σ' (s.dw σ)).2.2 := by
      intro t ht
      have hacc : ∀ a ∈ t.2.rds, AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a :=
        fun a ha => hc.so a (List.mem_cons_of_mem _ (List.mem_append_right _
          (by rw [hrds]; exact List.mem_flatMap.mpr ⟨t, ht, ha⟩)))
      exact ptr_low_shape hc.ctx (fun n h => dw_some n h) t.2 (hsok t ht) hacc _ (hfacts t ht).2.1
    have hmap : (((tg, p0) :: (tg2, p2) :: rest).map fun t =>
          (t.2.pt.low E' elems (t.1.win σ' (s.dw σ)).2.2).low (t.1.win σ' (s.dw σ)).2.2) =
        ((tg, p0) :: (tg2, p2) :: rest).map fun t =>
          ((ptrSk t.2).low σ' (s.dw σ) (t.1.win σ' (s.dw σ)).2.2).low (t.1.win σ' (s.dw σ)).2.2 :=
      List.map_congr_left fun t ht => by rw [hlow' t ht]
    simp only [lowP, hL, Option.getD_some, hmap]
  refine ⟨_, _, hlow, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact wins_concat_wins d' _
  · simpa [Expr2.xfWidth] using hsum
  · intro x hx
    refine ⟨placedSegs_placed σ' (s.dw σ) _ x hx, fun env k hk => ?_⟩
    have := hbits x hx env k hk
    simpa [Expr2.xfBits] using this
  · rw [hrhs, htg]
    exact mem_placedSegs σ' (s.dw σ) _ (tg, p0) (List.mem_cons_self ..)
  · intro p hp
    rw [hmoreEq, htail] at hp
    obtain ⟨t, ht, rfl⟩ := mem_of_zip_map Prod.fst (fun u : Acc × PTR => ptrSk u.2) _ p hp
    exact mem_placedSegs σ' (s.dw σ) _ t (List.mem_cons_of_mem _ ht)
  · intro a ha
    rw [haccs] at ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨t, ht, rfl⟩

open CombProc in
/-- **The instantiated process of a site lowers to an assign with the skeleton's Boolean reading**, for an assign
site, a procedural body of one window and a body of several windows alike: the lowered target has the windows of
the site, its expression their total width, and every placed window of `W` reads its skeleton's bits; the head
window (with the skeleton `rhsSk`) and every further window (with its entry of `procSks`) are in `W`. -/
theorem site_lowLM {s : Summary} {σ : String → Int} {envD : IEnv} {elems : List (String × Nat)}
    {args : List Int} {M d' : Design2}
    (hdecl : M.decls.toList = s.decls.map (DeclT.toDecl σ))
    (hdecl' : d'.decls.toList = s.decls.map (DeclT.toDecl σ))
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hwithin : s.DisjWithin σ) (hself : s.NoSelfRead σ)
    (hfrag : s.EqFragM) (hwid : s.WidthOblM σ) (hbit : s.BitReadObl σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site)
    {ls : LSite} (hls : ls ∈ s.lsites) {σ' : String → Int} {E' : IEnv}
    (hr : ReachE ls.hdrs σ envD σ' E') :
    ∃ (t : Lhs2) (e : Expr2) (wins : List Win) (W : List (Win × Nat × PSk)),
      lowP M (instProcess2 E' elems ls.site.proc) = .assign t e ∧
      SiteLow d' σ' (s.dw σ) t e wins W ∧
      (∃ off, (ls.site.tgt.win σ' (s.dw σ), off, rhsSk ls.site.proc ls.site.rds) ∈ W) ∧
      (∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
        ∃ off, (p.1.win σ' (s.dw σ), off, p.2) ∈ W) ∧
      (∀ a ∈ ls.site.tgt :: ls.site.more, a.win σ' (s.dw σ) ∈ wins) := by
  by_cases hmore : ls.site.more = []
  · obtain ⟨t, e, hlow, hw, hxw, hxb⟩ :=
      site_lowL_single hdecl hdecl' C hok hauto hin hself (fun b hb => ⟨(hfrag b hb).1, (hfrag b hb).2.1⟩)
        hwid.1 hbit hsites hls hmore hr
    refine ⟨t, e, [ls.site.tgt.win σ' (s.dw σ)],
      [(ls.site.tgt.win σ' (s.dw σ), 0, rhsSk ls.site.proc ls.site.rds)], hlow,
      ⟨hw, by simpa [Win.sumWidth] using hxw, ?_⟩, ⟨0, by simp⟩, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      refine ⟨by simp [Win.placed, Win.sumWidth], fun env k hk => ?_⟩
      simpa using hxb env k hk
    · intro p hp
      rw [hmore] at hp
      simp at hp
    · intro a ha
      rw [hmore] at ha
      obtain rfl := List.mem_singleton.mp ha
      simp
  · obtain ⟨pos, p, hp⟩ := hsites ls hls
    rcases siteOfP?_cases hp with hp0 | ⟨b, tg, ptr, rfl, htree, hst⟩ | ⟨b, segs, rfl, hb, hms⟩
    · exact absurd (siteOf?_more hp0) hmore
    · exact absurd (congrArg TSite.more hst) hmore
    · obtain ⟨hproc, hrds, haccs, -⟩ := multiSite_shape hms
      obtain ⟨t, e, hlow, h1, h2, h3, h4⟩ :=
        site_lowL_multi hdecl hdecl' C hok hauto hin hwithin hself hfrag hwid hbit hls hr hb hproc hrds
          haccs hmore
      exact ⟨t, e, _, _, hlow, h1, h2, h3, h4⟩

/-- **The equations and knownness of a design `X.sem N` with procedural `always_comb` processes.**
The settled-state hypotheses are about the LOWERED design `d'`. -/
theorem eq_of_summaryL {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hself : s.NoSelfRead σ)
    (hfrag : s.EqFragL) (hwid : s.WidthOblL σ) (hbit : s.BitReadObl σ) (hcov : s.CoverObl σ)
    {st : SvState} (hinK : s.InKnown σ st) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d')
    (heqs : CombEqs d' st) (hsh : StateShape d' st) :
    s.EqsL σ st ∧ s.Knowns σ st := by
  obtain ⟨M, d0, E, elems, hm, hl0, hdecl, hdd, hrel, hR, hproc, C, hdesc, hsites⟩ :=
    Summary.soundL hs harity h1 hag hok hauto hin
      (Summary.DisjWithin.of_single fun b hb => (hfrag b hb).2.2) hself
  have hGD := instantiateGD2_eq_of_lowerable hm hl
  rw [hGD, hl0] at hl
  have hd0 : d0 = d' := Option.some.inj hl
  subst hd0
  have hdecl' : d0.decls.toList = s.decls.map (DeclT.toDecl σ) := by rw [hdd]; exact hdecl
  have hik : d0.InputsKnown st := by
    intro n hn
    rw [Realized.inputNames hdecl'] at hn
    obtain ⟨v, hv, hk, hw⟩ := hinK n hn
    refine ⟨v, hv, hk, ?_⟩
    have hfn : (s.find n).isSome = true := find_isSome_of_mem (mem_declNames_of_input hn)
    rw [declWidth_eq hdecl', dw_some n (by simpa [Summary.DW] using hfn), hw]
  have hP : ∀ q ∈ s.pairs σ E elems, ∃ ls ∈ s.lsites, ∃ σ' E', ReachE ls.hdrs σ E σ' E' ∧
      q = (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) := by
    intro q hq
    unfold Summary.pairs at hq
    rw [mem_enum_E] at hq
    exact hq
  have hsite : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ∃ (t : Lhs2) (e : Expr2), lowP M (instProcess2 E' elems ls.site.proc) = .assign t e ∧
        t.wins d0 = [ls.site.tgt.win σ' (s.dw σ)] ∧
        e.xfWidth d0 = some (ls.site.tgt.win σ' (s.dw σ)).2.2 ∧
        ∀ env k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
          e.xfBits d0 env k =
            (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2 env k :=
    fun ls hls σ' E' hr => site_lowL hdecl hdecl' C hok hauto hin hself hfrag hwid hbit hsites hls hr
  -- index-level facts
  have hform : ∀ (i : Nat) (p : Process2), d0.processes[i]? = some p →
      ∃ q ∈ s.pairs σ E elems, lowP M q.2 = p := by
    intro i p hp
    have h1 : d0.processes.toList[i]? = some p := by rw [Array.getElem?_toList]; exact hp
    rw [hproc, List.getElem?_map] at h1
    cases hL : (s.pairs σ E elems)[i]? with
    | none => simp [hL] at h1
    | some q =>
        simp only [hL, Option.map_some, Option.some.injEq] at h1
        exact ⟨q, List.mem_of_getElem? hL, h1⟩
  have hex : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ∃ (i : Nat) (t : Lhs2) (e : Expr2), d0.processes[i]? = some (.assign t e) ∧
        t.wins d0 = [ls.site.tgt.win σ' (s.dw σ)] ∧
        e.xfWidth d0 = some (ls.site.tgt.win σ' (s.dw σ)).2.2 ∧
        ∀ env k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
          e.xfBits d0 env k =
            (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2 env k := by
    intro ls hls σ' E' hr
    obtain ⟨t, e, hlow, hwins, hxw, hxb⟩ := hsite ls hls σ' E' hr
    have hmem : (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) ∈
        s.pairs σ E elems := by
      unfold Summary.pairs
      rw [mem_enum_E]
      exact ⟨ls, hls, σ', E', hr, rfl⟩
    have h2 : lowP M (instProcess2 E' elems ls.site.proc) ∈ d0.processes.toList := by
      rw [hproc]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h2
    refine ⟨i, t, e, ?_, hwins, hxw, hxb⟩
    rw [← Array.getElem?_toList, hi, hlow]
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl0, hacc, hkeys⟩ := hok'
  have hfindRd : ∀ ls ∈ s.lsites, ∀ a ∈ ls.site.rds, (s.find a.name).isSome = true :=
    fun ls hls a ha => find_isSome_of_mem (hnames ls hls _ (by
      simp only [TSite.names, List.mem_cons, List.mem_map]
      exact Or.inr ⟨a, List.mem_append_right _ ha, rfl⟩))
  have hxf : d0.XFree := by
    intro i t e hp
    obtain ⟨q, hq, hqp⟩ := hform i _ hp
    obtain ⟨ls, hls, σ', E', hr, rfl⟩ := hP q hq
    obtain ⟨t', e', hlow, -, hxw, -⟩ := hsite ls hls σ' E' hr
    simp only at hqp
    rw [hlow] at hqp
    simp only [Process2.assign.injEq] at hqp
    obtain ⟨rfl, rfl⟩ := hqp
    exact ⟨_, hxw⟩
  have hsrc : ∀ n p, s.SrcS σ n p → d0.Sourced n p := by
    intro n p h
    rcases h with ⟨hn, hp⟩ | ⟨b, hb, hname, hl⟩
    · left
      have hf : (s.find n).isSome = true := by
        unfold Summary.dw at hp
        rcases hfi : s.find n with _ | dt
        · simp [hfi] at hp
        · rfl
      refine ⟨?_, s.dw σ n, ?_, hp⟩
      · rw [Realized.inputNames hdecl']; exact hn
      · rw [declWidth_eq hdecl', dw_some n (by simpa [Summary.DW] using hf)]
    · right
      obtain ⟨σ2, hr2, hwin⟩ := reach_of_LoopsE _ _ _ hl
      obtain ⟨E2, hE2⟩ := Reach_ReachE E hr2
      obtain ⟨i, t, e, hi, hwins, -, -⟩ := hex b hb σ2 E2 hE2
      have hn1 : n = (b.site.tgt.win σ2 (s.dw σ)).1 := by
        rw [Acc.win_name]; exact hname.symm
      refine ⟨i, (b.site.tgt.win σ2 (s.dw σ)).2.1, (b.site.tgt.win σ2 (s.dw σ)).2.2,
        ⟨_, _, hi, ?_⟩, hwin.1, hwin.2⟩
      rw [hwins, hn1]
      exact List.mem_singleton.mpr rfl
  have hcv : d0.Covered := by
    intro i t e hp r hr
    obtain ⟨q, hq, hqp⟩ := hform i _ hp
    obtain ⟨r0, hr0, hD, -⟩ := hdesc q hq
    have hlp : lowP M q.2 = r0 := by simp [lowP, hr0]
    rw [hlp] at hqp
    have hrm : r ∈ q.1.rd := by
      rcases hD with ⟨e', hpe, hrd, -⟩ | ⟨e', hpe, hrd, -⟩ <;>
        (rw [hqp] at hpe
         simp only [Process2.assign.injEq] at hpe
         obtain ⟨-, rfl⟩ := hpe
         exact hrd r hr)
    obtain ⟨ls, hls, σ', E', hrch, rfl⟩ := hP q hq
    simp only [LSite.inst, List.mem_map] at hrm
    obtain ⟨a, ha, rfl⟩ := hrm
    have hco := (Loops.all_iff _ _ _).mp (hcov ls hls) σ' (ReachE_Reach hrch) a ha
    cases a with
    | whole n =>
        have hfn : (s.find n).isSome = true := hfindRd ls hls _ ha
        simp only [Acc.rd, ReadWin.Covered]
        refine ⟨s.dw σ n, ?_, dw_pos hfn, fun k hk => ?_⟩
        · rw [declWidth_eq hdecl', dw_some n (by simpa [Summary.DW] using hfn)]
        · have h : d0.Sourced n (0 + k) := hsrc _ _ (hco k hk)
          simpa using h
    | bit n x => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | cell1 n x => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | row n w r' => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | cell2 n w r' c => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | part1 n h l => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | part2 n w r' h l => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
  have hmain : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      s.EqSiteL σ σ' st ls ∧ s.KnownSite σ σ' st ls := by
    intro ls hls σ' E' hr
    obtain ⟨i, t, e, hi, hwins, hxw, hxb⟩ := hex ls hls σ' E' hr
    have hset := fun k (hk : k < (ls.site.tgt.win σ' (s.dw σ)).2.2) =>
      CombKnown.settled hc ha hxf hcv heqs hsh hik i _ _ (ls.site.tgt.win σ' (s.dw σ)).1
        (ls.site.tgt.win σ' (s.dw σ)).2.1 (ls.site.tgt.win σ' (s.dw σ)).2.2 0 hi
        (by rw [hwins]; simp [Win.placed]) k hk
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have h1 := (hset k hk).2
      rw [Nat.zero_add, Expr2.xfBitsZ_of_lt hxw hk] at h1
      exact h1.trans (hxb st.boolAt k hk)
    · refine ⟨?_, (hset k hk).1⟩
      obtain ⟨v, hv, hdv⟩ := hsh.driven (ls.site.tgt.win σ' (s.dw σ)).1
        ⟨i, (ls.site.tgt.win σ' (s.dw σ)).2.1, (ls.site.tgt.win σ' (s.dw σ)).2.2,
          _, _, hi, by rw [hwins]; exact List.mem_singleton.mpr rfl⟩
      refine ⟨v, hv, ?_⟩
      have hD := declWidth_eq hdecl' (ls.site.tgt.win σ' (s.dw σ)).1
      have hfn : (s.find (ls.site.tgt.win σ' (s.dw σ)).1).isSome = true := by
        rw [Acc.win_name]
        exact find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
      rw [hD, dw_some _ (by simpa [Summary.DW] using hfn)] at hdv
      exact (Option.some.inj hdv).symm
  refine ⟨fun ls hls => LoopsN_of_reach _ _ _ (fun σ' hr => ?_),
    fun ls hls => LoopsN_of_reach _ _ _ (fun σ' hr => ?_)⟩
  · obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').1
  · obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').2

/-- The tactic's form: the valuation is the parameters zipped with the arguments, then the localparams
(`s.val args`), the environment check in a `rfl`-provable form (as `eq_view`). -/
theorem eq_viewL {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hself : s.NoSelfRead (s.val args))
    (hfrag : s.EqFragL) (hwid : s.WidthOblL (s.val args))
    (hbit : s.BitReadObl (s.val args)) (hcov : s.CoverObl (s.val args))
    {st : SvState} (hinK : s.InKnown (s.val args) st) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d')
    (heqs : CombEqs d' st) (hsh : StateShape d' st) :
    s.EqsL (s.val args) st ∧ s.Knowns (s.val args) st :=
  eq_of_summaryL hs harity h1 (Agrees_of_map hag) hok hauto hin hself hfrag hwid hbit hcov hinK hl
    hc ha heqs hsh

/-- **The equations and knownness of a design `X.sem N` with procedural `always_comb` processes, some of which
write SEVERAL windows** (the sibling of `eq_of_summaryL`: the head-window equations of every site, then one
equation per further window, and the same for knownness). The settled-state hypotheses are about the LOWERED
design `d'`; `hwithin` says the windows of one instance of a body are pairwise disjoint. -/
theorem eq_of_summaryM {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hwithin : s.DisjWithin σ)
    (hself : s.NoSelfRead σ)
    (hfrag : s.EqFragM) (hwid : s.WidthOblM σ) (hbit : s.BitReadObl σ) (hcov : s.CoverOblM σ)
    {st : SvState} (hinK : s.InKnown σ st) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d')
    (heqs : CombEqs d' st) (hsh : StateShape d' st) :
    s.EqsM σ st ∧ s.KnownsM σ st := by
  obtain ⟨M, d0, E, elems, hm, hl0, hdecl, hdd, hrel, hR, hproc, C, hdesc, hsites⟩ :=
    Summary.soundL hs harity h1 hag hok hauto hin hwithin hself
  have hGD := instantiateGD2_eq_of_lowerable hm hl
  rw [hGD, hl0] at hl
  have hd0 : d0 = d' := Option.some.inj hl
  subst hd0
  have hdecl' : d0.decls.toList = s.decls.map (DeclT.toDecl σ) := by rw [hdd]; exact hdecl
  have hik : d0.InputsKnown st := by
    intro n hn
    rw [Realized.inputNames hdecl'] at hn
    obtain ⟨v, hv, hk, hw⟩ := hinK n hn
    refine ⟨v, hv, hk, ?_⟩
    have hfn : (s.find n).isSome = true := find_isSome_of_mem (mem_declNames_of_input hn)
    rw [declWidth_eq hdecl', dw_some n (by simpa [Summary.DW] using hfn), hw]
  have hP : ∀ q ∈ s.pairs σ E elems, ∃ ls ∈ s.lsites, ∃ σ' E', ReachE ls.hdrs σ E σ' E' ∧
      q = (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) := by
    intro q hq
    unfold Summary.pairs at hq
    rw [mem_enum_E] at hq
    exact hq
  have hsite : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ∃ (t : Lhs2) (e : Expr2) (wins : List Win) (W : List (Win × Nat × PSk)),
        lowP M (instProcess2 E' elems ls.site.proc) = .assign t e ∧
        SiteLow d0 σ' (s.dw σ) t e wins W ∧
        (∃ off, (ls.site.tgt.win σ' (s.dw σ), off, rhsSk ls.site.proc ls.site.rds) ∈ W) ∧
        (∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
          ∃ off, (p.1.win σ' (s.dw σ), off, p.2) ∈ W) ∧
        (∀ a ∈ ls.site.tgt :: ls.site.more, a.win σ' (s.dw σ) ∈ wins) :=
    fun ls hls σ' E' hr =>
      site_lowLM hdecl hdecl' C hok hauto hin hwithin hself hfrag hwid hbit hsites hls hr
  -- index-level facts
  have hform : ∀ (i : Nat) (p : Process2), d0.processes[i]? = some p →
      ∃ q ∈ s.pairs σ E elems, lowP M q.2 = p := by
    intro i p hp
    have h1 : d0.processes.toList[i]? = some p := by rw [Array.getElem?_toList]; exact hp
    rw [hproc, List.getElem?_map] at h1
    cases hL : (s.pairs σ E elems)[i]? with
    | none => simp [hL] at h1
    | some q =>
        simp only [hL, Option.map_some, Option.some.injEq] at h1
        exact ⟨q, List.mem_of_getElem? hL, h1⟩
  have hex : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ∃ (i : Nat) (t : Lhs2) (e : Expr2) (wins : List Win) (W : List (Win × Nat × PSk)),
        d0.processes[i]? = some (.assign t e) ∧ SiteLow d0 σ' (s.dw σ) t e wins W ∧
        (∃ off, (ls.site.tgt.win σ' (s.dw σ), off, rhsSk ls.site.proc ls.site.rds) ∈ W) ∧
        (∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
          ∃ off, (p.1.win σ' (s.dw σ), off, p.2) ∈ W) ∧
        (∀ a ∈ ls.site.tgt :: ls.site.more, a.win σ' (s.dw σ) ∈ wins) := by
    intro ls hls σ' E' hr
    obtain ⟨t, e, wins, W, hlow, hsl, h3, h4, h5⟩ := hsite ls hls σ' E' hr
    have hmem : (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) ∈
        s.pairs σ E elems := by
      unfold Summary.pairs
      rw [mem_enum_E]
      exact ⟨ls, hls, σ', E', hr, rfl⟩
    have h2 : lowP M (instProcess2 E' elems ls.site.proc) ∈ d0.processes.toList := by
      rw [hproc]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h2
    refine ⟨i, t, e, wins, W, ?_, hsl, h3, h4, h5⟩
    rw [← Array.getElem?_toList, hi, hlow]
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl0, hacc, hkeys⟩ := hok'
  have hfindRd : ∀ ls ∈ s.lsites, ∀ a ∈ ls.site.rds, (s.find a.name).isSome = true :=
    fun ls hls a ha => find_isSome_of_mem (hnames ls hls _ (by
      simp only [TSite.names, List.mem_cons, List.mem_map]
      exact Or.inr ⟨a, List.mem_append_right _ ha, rfl⟩))
  have hfindWin : ∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: ls.site.more,
      (s.find a.name).isSome = true :=
    fun ls hls a ha => find_isSome_of_mem (hnames ls hls _ (by
      simp only [TSite.names, List.mem_cons, List.mem_map]
      rcases List.mem_cons.mp ha with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr ⟨a, List.mem_append_left _ hm, rfl⟩))
  have hxf : d0.XFree := by
    intro i t e hp
    obtain ⟨q, hq, hqp⟩ := hform i _ hp
    obtain ⟨ls, hls, σ', E', hr, rfl⟩ := hP q hq
    obtain ⟨t', e', wins, W, hlow, hsl, -⟩ := hsite ls hls σ' E' hr
    simp only at hqp
    rw [hlow] at hqp
    simp only [Process2.assign.injEq] at hqp
    obtain ⟨rfl, rfl⟩ := hqp
    exact ⟨_, hsl.2.1⟩
  have hsrc : ∀ n p, s.SrcSM σ n p → d0.Sourced n p := by
    intro n p h
    rcases h with (⟨hn, hp⟩ | ⟨b, hb, hname, hl⟩) | ⟨b, hb, a, ha, hname, hl⟩
    · left
      have hf : (s.find n).isSome = true := by
        unfold Summary.dw at hp
        rcases hfi : s.find n with _ | dt
        · simp [hfi] at hp
        · rfl
      refine ⟨?_, s.dw σ n, ?_, hp⟩
      · rw [Realized.inputNames hdecl']; exact hn
      · rw [declWidth_eq hdecl', dw_some n (by simpa [Summary.DW] using hf)]
    · right
      obtain ⟨σ2, hr2, hwin⟩ := reach_of_LoopsE _ _ _ hl
      obtain ⟨E2, hE2⟩ := Reach_ReachE E hr2
      obtain ⟨i, t, e, wins, W, hi, hsl, -, -, hall⟩ := hex b hb σ2 E2 hE2
      have hn1 : n = (b.site.tgt.win σ2 (s.dw σ)).1 := by
        rw [Acc.win_name]; exact hname.symm
      refine ⟨i, (b.site.tgt.win σ2 (s.dw σ)).2.1, (b.site.tgt.win σ2 (s.dw σ)).2.2,
        ⟨_, _, hi, ?_⟩, hwin.1, hwin.2⟩
      rw [hsl.1, hn1]
      exact hall b.site.tgt (List.mem_cons_self ..)
    · right
      obtain ⟨σ2, hr2, hwin⟩ := reach_of_LoopsE _ _ _ hl
      obtain ⟨E2, hE2⟩ := Reach_ReachE E hr2
      obtain ⟨i, t, e, wins, W, hi, hsl, -, -, hall⟩ := hex b hb σ2 E2 hE2
      have hn1 : n = (a.win σ2 (s.dw σ)).1 := by
        rw [Acc.win_name]; exact hname.symm
      refine ⟨i, (a.win σ2 (s.dw σ)).2.1, (a.win σ2 (s.dw σ)).2.2,
        ⟨_, _, hi, ?_⟩, hwin.1, hwin.2⟩
      rw [hsl.1, hn1]
      exact hall a (List.mem_cons_of_mem _ ha)
  have hcv : d0.Covered := by
    intro i t e hp r hr
    obtain ⟨q, hq, hqp⟩ := hform i _ hp
    obtain ⟨r0, hr0, hD, -⟩ := hdesc q hq
    have hlp : lowP M q.2 = r0 := by simp [lowP, hr0]
    rw [hlp] at hqp
    have hrm : r ∈ q.1.rd := by
      rcases hD with ⟨e', hpe, hrd, -⟩ | ⟨e', hpe, hrd, -⟩ <;>
        (rw [hqp] at hpe
         simp only [Process2.assign.injEq] at hpe
         obtain ⟨-, rfl⟩ := hpe
         exact hrd r hr)
    obtain ⟨ls, hls, σ', E', hrch, rfl⟩ := hP q hq
    simp only [LSite.inst, List.mem_map] at hrm
    obtain ⟨a, ha, rfl⟩ := hrm
    have hco := (Loops.all_iff _ _ _).mp (hcov ls hls) σ' (ReachE_Reach hrch) a ha
    cases a with
    | whole n =>
        have hfn : (s.find n).isSome = true := hfindRd ls hls _ ha
        simp only [Acc.rd, ReadWin.Covered]
        refine ⟨s.dw σ n, ?_, dw_pos hfn, fun k hk => ?_⟩
        · rw [declWidth_eq hdecl', dw_some n (by simpa [Summary.DW] using hfn)]
        · have h : d0.Sourced n (0 + k) := hsrc _ _ (hco k hk)
          simpa using h
    | bit n x => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | cell1 n x => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | row n w r' => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | cell2 n w r' c => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | part1 n h l => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | part2 n w r' h l => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
  -- the knownness of a window of the lowered target, and the equation of a placed window
  have hknown : ∀ (i : Nat) (t : Lhs2) (e : Expr2) (wins : List Win) (W : List (Win × Nat × PSk))
      (σ' : String → Int), d0.processes[i]? = some (.assign t e) →
      SiteLow d0 σ' (s.dw σ) t e wins W → ∀ wn ∈ wins, (s.find wn.1).isSome = true →
        ∀ k, k < wn.2.2 → (∃ v, SvState.lookup st wn.1 = some v ∧ v.width = s.dw σ wn.1) ∧
          KnownBit st wn.1 (wn.2.1 + k) := by
    intro i t e wins W σ' hi hsl wn hwn hfn k hk
    obtain ⟨off, hpl⟩ := Win.exists_mem_placed hwn
    obtain ⟨hwins, -, -⟩ := hsl
    refine ⟨?_, (CombKnown.settled hc ha hxf hcv heqs hsh hik i t e wn.1 wn.2.1 wn.2.2 off hi
      (by rw [hwins]; exact hpl) k hk).1⟩
    obtain ⟨v, hv, hdv⟩ := hsh.driven wn.1 ⟨i, wn.2.1, wn.2.2, t, e, hi, by rw [hwins]; exact hwn⟩
    refine ⟨v, hv, ?_⟩
    have hD := declWidth_eq hdecl' wn.1
    rw [hD, dw_some _ (by simpa [Summary.DW] using hfn)] at hdv
    exact (Option.some.inj hdv).symm
  have hbits : ∀ (i : Nat) (t : Lhs2) (e : Expr2) (wins : List Win) (W : List (Win × Nat × PSk))
      (σ' : String → Int), d0.processes[i]? = some (.assign t e) →
      SiteLow d0 σ' (s.dw σ) t e wins W → ∀ x ∈ W, ∀ k, k < x.1.2.2 →
        st.boolAt x.1.1 (x.1.2.1 + k) = x.2.2.bit σ' (s.dw σ) x.1.2.2 st.boolAt k := by
    intro i t e wins W σ' hi hsl x hx k hk
    obtain ⟨hwins, hxw, hW⟩ := hsl
    obtain ⟨hpl, hb⟩ := hW x hx
    have hbd := Win.le_sumWidth_of_mem_placed hpl
    have h1 := (CombKnown.settled hc ha hxf hcv heqs hsh hik i t e x.1.1 x.1.2.1 x.1.2.2 x.2.1 hi
      (by rw [hwins]; exact hpl) k hk).2
    rw [Expr2.xfBitsZ_of_lt (j := x.2.1 + k) hxw (by omega)] at h1
    exact h1.trans (hb st.boolAt k hk)
  have hmain : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      s.EqSiteL σ σ' st ls ∧ s.KnownSite σ σ' st ls ∧
      (∀ p ∈ ls.site.more.zip (procSks ls.site.proc ls.site.rds).tail,
        ∀ k, k < (p.1.win σ' (s.dw σ)).2.2 →
          st.boolAt (p.1.win σ' (s.dw σ)).1 ((p.1.win σ' (s.dw σ)).2.1 + k) =
            p.2.bit σ' (s.dw σ) (p.1.win σ' (s.dw σ)).2.2 st.boolAt k) ∧
      (∀ a ∈ ls.site.more, ∀ k, k < (a.win σ' (s.dw σ)).2.2 →
        (∃ v, SvState.lookup st (a.win σ' (s.dw σ)).1 = some v ∧
          v.width = s.dw σ (a.win σ' (s.dw σ)).1) ∧
        KnownBit st (a.win σ' (s.dw σ)).1 ((a.win σ' (s.dw σ)).2.1 + k)) := by
    intro ls hls σ' E' hr
    obtain ⟨i, t, e, wins, W, hi, hsl, ⟨offh, hxh⟩, hfur, hall⟩ := hex ls hls σ' E' hr
    refine ⟨fun k hk => hbits i t e wins W σ' hi hsl _ hxh k hk,
      fun k hk => hknown i t e wins W σ' hi hsl _ (hall _ (List.mem_cons_self ..))
        (by rw [Acc.win_name]; exact hfindWin ls hls _ (List.mem_cons_self ..)) k hk, ?_, ?_⟩
    · intro p hp k hk
      obtain ⟨off, hx⟩ := hfur p hp
      exact hbits i t e wins W σ' hi hsl _ hx k hk
    · intro a ha k hk
      exact hknown i t e wins W σ' hi hsl _ (hall a (List.mem_cons_of_mem _ ha))
        (by rw [Acc.win_name]; exact hfindWin ls hls _ (List.mem_cons_of_mem _ ha)) k hk
  refine ⟨⟨fun ls hls => LoopsN_of_reach _ _ _ (fun σ' hr => ?_), ?_⟩,
    ⟨fun ls hls => LoopsN_of_reach _ _ _ (fun σ' hr => ?_), ?_⟩⟩
  · obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').1
  · intro ls hls p hp
    refine LoopsN_of_reach _ _ _ (fun σ' hr => ?_)
    obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').2.2.1 p hp
  · obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').2.1
  · intro ls hls a ha
    refine LoopsN_of_reach _ _ _ (fun σ' hr => ?_)
    obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').2.2.2 a ha

/-- The tactic's form of `eq_of_summaryM` (as `eq_viewL` is of `eq_of_summaryL`). -/
theorem eq_viewLM {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args))
    (hwithin : s.DisjWithin (s.val args))
    (hself : s.NoSelfRead (s.val args))
    (hfrag : s.EqFragM) (hwid : s.WidthOblM (s.val args))
    (hbit : s.BitReadObl (s.val args)) (hcov : s.CoverOblM (s.val args))
    {st : SvState} (hinK : s.InKnown (s.val args) st) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d')
    (heqs : CombEqs d' st) (hsh : StateShape d' st) :
    s.EqsM (s.val args) st ∧ s.KnownsM (s.val args) st :=
  eq_of_summaryM hs harity h1 (Agrees_of_map hag) hok hauto hin hwithin hself hfrag hwid hbit hcov hinK
    hl hc ha heqs hsh

/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombEq.rhsSk_of_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms rhsSk_of_ne

/-- info: 'LeanModels.Sv.CombEq.fragOkP_of_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms fragOkP_of_ne

/-- info: 'LeanModels.Sv.CombEq.partsRd_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partsRd_len

/-- info: 'LeanModels.Sv.CombEq.rhsRds_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhsRds_len

/-- info: 'LeanModels.Sv.CombEq.ptr_rds_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptr_rds_len

/-- info: 'LeanModels.Sv.CombEq.ptr_sk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptr_sk_eq

/-- info: 'LeanModels.Sv.CombEq.ptr_sk_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptr_sk_leaves

/-- info: 'LeanModels.Sv.CombEq.instExpr2_gate_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instExpr2_gate_none

/-- info: 'LeanModels.Sv.CombEq.cond_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cond_shape

/-- info: 'LeanModels.Sv.CombEq.ptr_low_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptr_low_shape

/-- info: 'LeanModels.Sv.CombEq.psk_xfOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psk_xfOk

/-- info: 'LeanModels.Sv.CombEq.psk_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psk_bit

/-- info: 'LeanModels.Sv.CombEq.psk_low_xfWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psk_low_xfWidth

/-- info: 'LeanModels.Sv.CombEq.psk_low_xfBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psk_low_xfBits

/-- info: 'LeanModels.Sv.CombEq.xfWidth_concat_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms xfWidth_concat_one

/-- info: 'LeanModels.Sv.CombEq.xfBits_concat_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xfBits_concat_one

/-- info: 'LeanModels.Sv.CombEq.lowerProcs_push_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerProcs_push_unsupported

/-- info: 'LeanModels.Sv.CombEq.instantiateGD2_eq_of_lowerable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instantiateGD2_eq_of_lowerable

/-- info: 'LeanModels.Sv.CombEq.instantiate2_ok_of_lowerable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instantiate2_ok_of_lowerable

/-- info: 'LeanModels.Sv.CombEq.declsL_of_lowerable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms declsL_of_lowerable

/-- info: 'LeanModels.Sv.CombEq.declsL_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms declsL_view

/-- info: 'LeanModels.Sv.CombEq.site_lowL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms site_lowL

/-- info: 'LeanModels.Sv.CombEq.eq_of_summaryL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_summaryL

/-- info: 'LeanModels.Sv.CombEq.eq_viewL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_viewL

/-! ## Axiom pins for the lemmas of the second fragment (WP-G S2)

`#pin_axioms` is silent when every named constant depends on at most `propext`, `Classical.choice` and
`Quot.sound`, and an error naming the constant and the axiom otherwise (`sorryAx` included). It stands
for one `#print axioms` pin per lemma; the lemmas below are the ones WP-G S2 added to `CombViewThm`,
`CombEqBase`, `CombEqShape` and `CombProc`. -/

#pin_axioms CombView.binOk_cases CombView.rdsOf?_binary CombView.rdsOf?_unary
  CombView.rdsOf?_ternary CombView.rdsOf?_reduce CombView.RdOK.unary CombView.RdOK.reduce
  CombView.RdOK.logical CombView.RdOK.ternary CombView.ie_lnot CombView.ie_bnot_some
  CombView.ie_bnot_none CombView.ie_bnot_cases CombView.ie_ternary_some CombView.ie_ternary_none
  CombView.ie_ternary_cases CombView.ie_land CombView.ie_lor CombView.ie_reduce CombView.ie_eq_cases
  CombView.ie_ne_cases CombView.ie_eq CombView.ie_ne CombView.sw_lnot CombView.sw_bnot
  CombView.sw_land CombView.sw_lor CombView.sw_eq CombView.sw_ne CombView.sw_reduce
  CombView.sw_ternary CombView.rm_bnot CombView.rm_lnot CombView.rm_land CombView.rm_lor
  CombView.rm_eq CombView.rm_ne CombView.rm_reduce CombView.rm_ternary

#pin_axioms rdsOf?_len skT_leaves Sk.low_irrel Sk.selfOk_widthOk rm_leaf skT_shape
  XF.any_one XF.any_congr XF.eqv_one XF.all_congr XF.parity_congr XF.red_congr XF.eqv_congr xf_lnot
  xfb_lnot xf_red xfb_red xf_logical xfb_land xfb_lor xf_tern xfb_tern xf_eq xf_ne xfb_eq xfb_ne
  low_xf_gen

#pin_axioms CombProc.fit_idxFree

/-! The lemmas of the `case` rule (WP-G S3a). -/

#pin_axioms CombProc.listSymSubst_nil CombProc.symExec_caseItems CombProc.symExec_cases
  CombProc.anyGuard_reads CombProc.reads_caseLow CombProc.drvWins_caseItems CombProc.drvWins_cases
  CombProc.mayW_caseItems CombProc.mayW_cases CombProc.listCombViol_caseItems_ws
  CombProc.combViol_cases_ws CombProc.anyGuard_xfWidth CombProc.anyGuard_xfBits
  CombProc.caseLow_xfWidth CombProc.caseLow_xfBits CombProc.listRdW_of_reads
  CombProc.casesNoRdW_of_noRead CombProc.instStmt2_plf CombProc.instItems2_arms CombProc.mem_armRds
  CombProc.mem_arms CombProc.mem_lowArms CombProc.instPats2_simple CombProc.wfB_of_rd
  CombProc.plfr_rdOK CombProc.plfr_idxFree CombProc.plfr_tgt CombProc.subj_rdOK CombProc.arms_facts
  CombProc.arms_idx CombProc.isLitP_spec CombProc.casePats?_spec CombProc.armLeaf?_spec
  CombProc.caseArms?_spec CombProc.caseTree?_spec CombProc.caseStmt?_spec CombView.anyGuard_rdOK
  CombView.caseLow_rdOK LVec.width_mk_toArray XF.caseSel_nil XF.caseSel_cons XF.val_congr
  XF.eqv_eq_true_iff XF.testBit_nat_boolAt XF.caseSel_table XF.caseSel_bv XF.caseSel_out armRcnt_plfr itemsRcnt_arms
  caseSkItems_arms plfr_leaves pskArmLeaves_arms mem_ptrArmsSk foldl_fixed caseWidth2_eq
  instPats2_lits mem_items_arms plfr_low_shape lowArms_shape pskArms_xfOk caseBitAux_pskArms

/-! ## Axiom pins for the lemmas of default-then-override (WP-G S3b) -/

#pin_axioms stmtRcntL_append stmtRcntL_base ovrSk_append listSk_snoc listSk_nonovr ptr_sk_both
  CombProc.instStmts2_append CombProc.low_isOvr CombProc.acc_rd_pos CombProc.ovrStmt?_spec
  CombProc.ovrFold?_spec

/-! ## Axiom pins for the lemmas of a body of several windows (WP-G S1b, gate d1) -/

#pin_axioms ovrSk_cons_ovr ovrSk_stop ovrSk_append_stop stmtsP_shape stmtsP_rcnt spanOvr_append
  windowSksF_segs procSks_multi rhsSk_multi placed_bound placedSegs_placed placedSegs_bound
  mem_placedSegs catBits_cons_head catBits_cons_tail parts_bits mem_zip_map mem_of_zip_map
  site_lowL_single site_lowL_multi site_lowLM eq_of_summaryM eq_viewLM CombView.multi_lowers
  CombView.siteCtx_of_reach

/-! ## Axiom pins for the shared cores of the proof halves (WP-G consolidation, Tier B) -/

#pin_axioms CombView.mem_insts_of_map_fst CombView.desc_facts CombView.realized_comb_core
  CombView.realized_acyclic_core CombView.pairs_ctx CombView.pairs_desc_site CombView.fams_expand2W
  CombView.sound_prefix CombView.realized_comb CombView.realized_acyclic CombView.pairs_desc
  CombView.fams_expand2 CombView.Summary.sound CombView.Summary.soundL

end CombEq
end LeanModels.Sv
