import Lean.Elab.Command
import Lean.Util.CollectAxioms
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

## Soundness story

Nothing is trusted. The skeleton is a plain function of the template and the site's reads; the theorems below
say it describes the tree the instantiation builds (`ptr_low_shape`) and that the lowered expression evaluates to
its Boolean reading, using only the same x-free fragment lemmas as `sv_equations` (`low_xfWidth`, `low_xfBits`)
and the tree lemmas of G2.1. COPY NOTE: `cond_shape`, `skT_selfWidth` are the `gate_shape` proof with the
context `none` of an `if` condition; `PSk` is `Sk` with a choice node (`G22-NOTE.md`, section 3).
-/

namespace LeanModels.Sv
namespace CombEq
open CombView

/-! ## The skeleton -/

/-- The shape of a right-hand side of a procedural site: a leaf is the skeleton of one assignment's right-hand
side, `ite` a choice on the first bit of a gate-tree condition, `blk` a `begin … end`. -/
inductive PSk where
  | leaf (sk : Sk)
  | ite (c : Sk) (a b : PSk)
  | blk (a : PSk)

/-- Bit `k` of the skeleton: a choice is the `if` rule (the condition's bit 0 is `1`). -/
def PSk.bit (σ : String → Int) (dw : String → Nat) (rd : String → Nat → Bool) : PSk → Nat → Bool
  | .leaf sk, k => sk.bit σ dw rd k
  | .ite c a b, k => if c.bit σ dw rd 0 then a.bit σ dw rd k else b.bit σ dw rd k
  | .blk a, k => a.bit σ dw rd k

/-- The tree the instantiation builds for the skeleton at target width `tw` (conditions are one bit). -/
def PSk.low (σ : String → Int) (tw : Nat) : PSk → CombProc.PTree
  | .leaf sk => .leaf (sk.low σ tw)
  | .ite c a b => .ite (c.low σ 1) (a.low σ tw) (b.low σ tw)
  | .blk a => .blk (a.low σ tw)

/-- Every leaf operand is as wide as the target, every condition operand one bit. -/
def PSk.WidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : PSk → Prop
  | .leaf sk => sk.WidthOk σ dw tw
  | .ite c a b => c.WidthOk σ dw 1 ∧ a.WidthOk σ dw tw ∧ b.WidthOk σ dw tw
  | .blk a => a.WidthOk σ dw tw

/-- The access leaves, conditions first (the order of the site's read list). -/
def PSk.leaves : PSk → List Acc
  | .leaf sk => sk.leaves
  | .ite c a b => c.leaves ++ a.leaves ++ b.leaves
  | .blk a => a.leaves

/-- Literals and fills carry no `x`/`z`. -/
def PSk.knownB : PSk → Bool
  | .leaf sk => sk.knownB
  | .ite c a b => c.knownB && a.knownB && b.knownB
  | .blk a => a.knownB

/-! ## From the template -/

/-- Number of access leaves of the parts of a concatenation (literals take none). -/
def pcnt : List PExpr → Nat
  | [] => 0
  | p :: ps => (match p with | .lit _ => 0 | _ => 1) + pcnt ps

/-- Number of access leaves `skRhs` consumes. -/
def rcnt : PExpr → Nat
  | .fill _ => 0
  | .concat ps => pcnt ps
  | v => cnt v

mutual
/-- Number of access leaves the skeleton of a statement consumes. -/
def stmtRcnt : PStmt → Nat
  | .blockingAssign _ v => rcnt v
  | .blockingAssignL _ v => rcnt v
  | .ifStmt c a (some b) => cnt c + stmtRcnt a + stmtRcnt b
  | .block ss => stmtRcntL ss
  | _ => 0
termination_by structural s => s

def stmtRcntL : List PStmt → Nat
  | [s] => stmtRcnt s
  | _ => 0
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
  | _ => .leaf (.fill .l0)
termination_by structural s => s

def stmtSkL (as : List Acc) : List PStmt → PSk
  | [s] => .blk (stmtSk as s)
  | _ => .leaf (.fill .l0)
termination_by structural ss => ss
end

/-- The skeleton of the right-hand side of a process: an `always_comb` body, or the single assignment. -/
def rhsSk : PProcess → List Acc → PSk
  | .alwaysComb b, as => stmtSk as b
  | p, as => .leaf (skRhs (rhsOf p) as)

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
def ptrSk : CombProc.PTR → PSk
  | .leafL _ v rs => .leaf (skRhs v rs)
  | .leafW _ v rs => .leaf (skRhs v rs)
  | .ite c rc a b => .ite (skT c rc) (ptrSk a) (ptrSk b)
  | .blk a => .blk (ptrSk a)

open CombProc in
theorem partsRd_len {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRd? ds ps = .ok rs → rs.length = pcnt ps
  | [], rs, h => by simp [partsRd?] at h; subst h; simp [pcnt]
  | p :: ps, rs, h => by
      simp only [partsRd?] at h
      rcases hp : partRd? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRd? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          have ih := partsRd_len ps rb hq
          by_cases hpl : ∃ v, p = .lit v
          · obtain ⟨v, rfl⟩ := hpl
            have hra : ra = [] := by simpa [partRd?] using hp.symm
            subst hra
            simp [pcnt, ih]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            rw [partRd?_of_ne hnl] at hp
            obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
            have hp1 : (match p with | .lit _ => 0 | _ => 1) = 1 := by
              cases p <;> first | rfl | exact absurd rfl (hnl _)
            simp [pcnt, hp1, ih, Nat.add_comm]

theorem rhsRds_len {ds : List DeclT} {v : PExpr} {rs : List Acc}
    (h : rhsRds? ds v = .ok rs) (hf : fragOk v = true) : rs.length = rcnt v := by
  by_cases hfill : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hfill
    simp only [rhsRds?, Except.ok.injEq] at h
    subst h
    simp [rcnt]
  by_cases hcat : ∃ ps, v = .concat ps
  · obtain ⟨ps, rfl⟩ := hcat
    have h' : partsRd? ds ps = .ok rs := by simpa [rhsRds?, rdsOf?] using h
    simpa [rcnt] using partsRd_len ps rs h'
  · have hn1 : ∀ b, v ≠ .fill b := fun b h => hfill ⟨b, h⟩
    have hn2 : ∀ ps, v ≠ .concat ps := fun ps h => hcat ⟨ps, h⟩
    rw [rhsRds?_of_ne hn1] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    have hr : rcnt v = cnt v := by
      cases v <;> first | rfl | exact absurd rfl (hn1 _) | exact absurd rfl (hn2 _)
    rw [hr]
    exact rdsOf?_len v rs h hf

open CombProc in
/-- The read list of a recognized tree has the length the statement's skeleton consumes. -/
theorem ptr_rds_len {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → ptr.rds.length = stmtRcnt ptr.pt.toPStmt
  | .leafL t v rs, hok => by
      simpa [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt] using rhsRds_len hok.2.1 hok.2.2
  | .leafW n v rs, hok => by
      simpa [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt] using rhsRds_len hok.2.1 hok.2.2
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      have h1 := rdsOf?_len c rc hc hg
      have h2 := ptr_rds_len a ha
      have h3 := ptr_rds_len b hb
      simp [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt, h1, h2, h3, Nat.add_assoc]
  | .blk a, hok => by
      simpa [PTR.rds, PTR.pt, PT.toPStmt, stmtRcnt, stmtRcntL] using ptr_rds_len a hok

open CombProc in
/-- **The skeleton computed from the flat read list is the annotated tree's.** -/
theorem ptr_sk_eq {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → stmtSk ptr.rds ptr.pt.toPStmt = ptrSk ptr
  | .leafL t v rs, _ => by simp [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk]
  | .leafW n v rs, _ => by simp [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk]
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      have h1 := rdsOf?_len c rc hc hg
      have h2 := ptr_rds_len a ha
      have e1 : (rc ++ a.rds ++ b.rds).take (cnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' h1
      have e2 : (rc ++ a.rds ++ b.rds).drop (cnt c) = a.rds ++ b.rds := by
        rw [List.append_assoc]; exact List.drop_left' h1
      have e3 : (a.rds ++ b.rds).take (stmtRcnt a.pt.toPStmt) = a.rds := List.take_left' h2
      have e4 : (a.rds ++ b.rds).drop (stmtRcnt a.pt.toPStmt) = b.rds := List.drop_left' h2
      simp only [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, ptrSk, e1, e2, e3, e4]
      rw [ptr_sk_eq a ha, ptr_sk_eq b hb]
  | .blk a, hok => by
      simp only [PTR.rds, PTR.pt, PT.toPStmt, stmtSk, stmtSkL, ptrSk]
      rw [ptr_sk_eq a hok]

open CombProc in
/-- The skeleton's access leaves are exactly the reads. -/
theorem ptr_sk_leaves {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (ptrSk ptr).leaves = ptr.rds
  | .leafL t v rs, hok => by
      simpa [ptrSk, PTR.rds, PSk.leaves] using skRhs_leaves hok.2.1 hok.2.2
  | .leafW n v rs, hok => by
      simpa [ptrSk, PTR.rds, PSk.leaves] using skRhs_leaves hok.2.1 hok.2.2
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩ => by
      simp [ptrSk, PTR.rds, PSk.leaves, skT_leaves c rc hc hg, ptr_sk_leaves a ha,
        ptr_sk_leaves b hb]
  | .blk a, hok => by
      simpa [ptrSk, PTR.rds, PSk.leaves] using ptr_sk_leaves a hok

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

/-- An expression of the fragment whose skeleton fits `tw` has self-determined width `tw`
(WP-G S2: a corollary of `skT_shape`). -/
theorem skT_selfWidth (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (skT v rs).WidthOk σ dw tw →
        selfWidth2 E elems v = some tw :=
  fun v rs h hf hacc tw hw => (skT_shape C hdw v rs h hf hacc tw hw).1

/-- **A condition instantiates to its skeleton at width one** (self-determined: the context is `none`; WP-G S2:
a corollary of `skT_shape`, so the conditions are the expressions of the fragment, `!`, `&&`, `==`, ... included). -/
theorem cond_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → (skT v rs).WidthOk σ dw 1 →
        instExpr2 E elems none v = (skT v rs).low σ 1 :=
  fun v rs h hf hacc hw => (skT_shape C hdw v rs h hf hacc 1 hw).2.2.1

end cond

/-! ## The instantiated tree is the skeleton's -/

section tree
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

open CombProc in
/-- **`PT.low` of an annotated tree is the lowering of its skeleton**: leaves through `rhs_shape`, conditions
through `cond_shape`. -/
theorem ptr_low_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) → ∀ tw,
      (ptrSk ptr).WidthOk σ dw tw → ptr.pt.low E elems tw = (ptrSk ptr).low σ tw
  | .leafL t v rs, hok, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [rhs_shape C hdw hok.2.1 hok.2.2 hacc hw]
  | .leafW n v rs, hok, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [rhs_shape C hdw hok.2.1 hok.2.2 hacc hw]
  | .ite c rc a b, ⟨⟨hc, hg⟩, ha, hb⟩, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [cond_shape C hdw c rc hc hg (fun x hx => hacc x (by simp [PTR.rds, hx])) hw.1,
        ptr_low_shape C hdw a ha (fun x hx => hacc x (by simp [PTR.rds, hx])) tw hw.2.1,
        ptr_low_shape C hdw b hb (fun x hx => hacc x (by simp [PTR.rds, hx])) tw hw.2.2]
  | .blk a, hok, hacc, tw, hw => by
      simp only [ptrSk, PSk.WidthOk] at hw
      simp only [PTR.pt, PT.low, ptrSk, PSk.low]
      rw [ptr_low_shape C hdw a hok hacc tw hw]

end tree

/-! ## The lowered tree is in the x-free fragment, with the skeleton's Boolean reading -/

/-- The tree of a skeleton is in the x-free fragment at the target width. -/
theorem psk_xfOk {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat} :
    ∀ (p : PSk), p.knownB = true → p.WidthOk σ dw tw → (∀ a ∈ p.leaves, LeafOk m σ dw a) →
      (p.low σ tw).xfOk m tw
  | .leaf sk, hk, hw, hL => by
      simpa [PSk.low, CombProc.PTree.xfOk] using low_xfWidth sk hk hw hL
  | .ite c a b, hk, hw, hL => by
      simp only [PSk.knownB, Bool.and_eq_true] at hk
      simp only [PSk.WidthOk] at hw
      refine ⟨?_, psk_xfOk a hk.1.2 hw.2.1 (fun x hx => hL x (by simp [PSk.leaves, hx])),
        psk_xfOk b hk.2 hw.2.2 (fun x hx => hL x (by simp [PSk.leaves, hx]))⟩
      exact low_xfWidth (tw := 1) c hk.1.1 hw.1 (fun x hx => hL x (by simp [PSk.leaves, hx]))
  | .blk a, hk, hw, hL => by
      simpa [PSk.low, CombProc.PTree.xfOk] using
        psk_xfOk a (by simpa [PSk.knownB] using hk) (by simpa [PSk.WidthOk] using hw)
          (fun x hx => hL x (by simpa [PSk.leaves] using hx))

/-- … and its Boolean reading (`PTree.bit`) is the skeleton's. -/
theorem psk_bit {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) :
    ∀ (p : PSk), p.knownB = true → p.WidthOk σ dw tw → (∀ a ∈ p.leaves, LeafOk m σ dw a) →
      ∀ k, k < tw → (p.low σ tw).bit m env k = p.bit σ dw env k
  | .leaf sk, hk, hw, hL, k, hk' => by
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit]
      exact low_xfBits env sk hk hw hL k hk'
  | .ite c a b, hk, hw, hL, k, hk' => by
      simp only [PSk.knownB, Bool.and_eq_true] at hk
      simp only [PSk.WidthOk] at hw
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit]
      rw [low_xfBits (tw := 1) env c hk.1.1 hw.1 (fun x hx => hL x (by simp [PSk.leaves, hx])) 0
          (by omega),
        psk_bit env a hk.1.2 hw.2.1 (fun x hx => hL x (by simp [PSk.leaves, hx])) k hk',
        psk_bit env b hk.2 hw.2.2 (fun x hx => hL x (by simp [PSk.leaves, hx])) k hk']
  | .blk a, hk, hw, hL, k, hk' => by
      simp only [PSk.low, CombProc.PTree.bit, PSk.bit]
      exact psk_bit env a (by simpa [PSk.knownB] using hk) (by simpa [PSk.WidthOk] using hw)
        (fun x hx => hL x (by simpa [PSk.leaves] using hx)) k hk'

/-- The lowered expression of the whole tree (`PTree.low`) has the target width. -/
theorem psk_low_xfWidth {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (p : PSk) (hk : p.knownB = true) (hw : p.WidthOk σ dw tw)
    (hL : ∀ a ∈ p.leaves, LeafOk m σ dw a) : ((p.low σ tw).low tw).xfWidth m = some tw :=
  CombProc.low_xfWidth m tw _ (psk_xfOk p hk hw hL)

/-- … and its Boolean reading is the skeleton's. -/
theorem psk_low_xfBits {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) (p : PSk) (hk : p.knownB = true) (hw : p.WidthOk σ dw tw)
    (hL : ∀ a ∈ p.leaves, LeafOk m σ dw a) (k : Nat) (hk' : k < tw) :
    ((p.low σ tw).low tw).xfBits m env k = p.bit σ dw env k := by
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
  ∀ ls ∈ s.lsites, fragOkP ls.site.proc = true ∧ (rhsSk ls.site.proc ls.site.rds).knownB = true

instance : Decidable s.EqFragL := by unfold EqFragL; infer_instance

/-- Operand widths equal the target width (conditions: one bit). -/
def WidthOblL (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
    (rhsSk ls.site.proc ls.site.rds).WidthOk σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2

/-- **The equations of one site**: the Boolean bits of its target window are the skeleton's bits. -/
def EqSiteL (σ σ' : String → Int) (st : SvState) (ls : LSite) : Prop :=
  ∀ k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
    st.boolAt (ls.site.tgt.win σ' (s.dw σ)).1 ((ls.site.tgt.win σ' (s.dw σ)).2.1 + k) =
      (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) st.boolAt k

/-- The netlist view: every site's equations, at every valuation of its loops. -/
def EqsL (σ : String → Int) (st : SvState) : Prop :=
  ∀ ls ∈ s.lsites, LoopsN ls.hdrs σ fun σ' => s.EqSiteL σ σ' st ls

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
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2' := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  rw [h2] at h2'
  exact Res.ok.inj h2'

/-- The tactic's form of `declsL_of_lowerable` (valuation `s.val args`). -/
theorem declsL_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) {d' : Design2}
    (hl : (d.instantiateGD2 args).lowerComb = some d') :
    (d.instantiateGD2 args).decls.toList = s.decls.map (DeclT.toDecl (s.val args)) :=
  declsL_of_lowerable hs h1 (Agrees_of_map hag) hok hl

open CombProc in
/-- **The instantiated process of a site lowers to an assign with the skeleton's Boolean reading**, for an
assign site and for a procedural site alike. -/
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
        e.xfBits d' env k = (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) env k := by
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
  rcases siteOfP?_cases hp with hp0 | ⟨b, tg, ptr, rfl, htree, hst⟩
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
    have hw' : (skRhs (rhsOf ls.site.proc) ls.site.rds).WidthOk σ' (s.dw σ)
        (ls.site.tgt.win σ' (s.dw σ)).2.2 := by
      simpa [rhsSk_of_ne hne, PSk.WidthOk] using hw
    have hshape := proc_shape C' hdw hp0 hso hf hw'
    have hleaves := site_sk hp0 hf
    have hlv : ∀ a ∈ (skRhs (rhsOf ls.site.proc) ls.site.rds).leaves, LeafOk d' σ' (s.dw σ) a :=
      fun a ha => hleaf a (by rwa [hleaves] at ha)
    refine ⟨ls.site.tgt.lhs σ',
      (skRhs (rhsOf ls.site.proc) ls.site.rds).low σ' (ls.site.tgt.win σ' (s.dw σ)).2.2,
      ?_, hwins, low_xfWidth _ hk hw' hlv, ?_⟩
    · unfold lowP
      rw [hshape] <;> rfl
    · intro env k hk'
      rw [rhsSk_of_ne hne]
      exact low_xfBits env _ hk hw' hlv k hk'
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
    have hself1 := (Loops.all_iff _ _ _).mp (hself ls hls (by rw [hproc]; rfl)) σ' (ReachE_Reach hr)
    have hself' : ∀ a ∈ ptr.rds,
        (a.rd σ').overlaps (ls.site.tgt.win σ' (s.dw σ)) = false :=
      fun a ha => hself1 a (by rw [hrds]; exact ha)
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
      .concat #[((ptrSk ptr).low σ' (ls.site.tgt.win σ' (s.dw σ)).2.2).low
        (ls.site.tgt.win σ' (s.dw σ)).2.2], ?_, wins_concat_win d' _, ?_, ?_⟩
    · simp only [lowP, hproc2, hL, hlow, Option.getD_some]
    · exact xfWidth_concat_one (psk_low_xfWidth _ hkn hwk hlv)
    · intro env k hk'
      rw [xfBits_concat_one, psk_low_xfBits env _ hkn hwk hlv k hk', hsk]

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
    Summary.soundL hs harity h1 hag hok hauto hin hself
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
          e.xfBits d0 env k = (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) env k :=
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
          e.xfBits d0 env k = (rhsSk ls.site.proc ls.site.rds).bit σ' (s.dw σ) env k := by
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
      exact Or.inr ⟨a, ha, rfl⟩))
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
    (hag : s.params.map (fun n => env.vals.lookup n) =
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

/-- info: 'LeanModels.Sv.CombEq.instExpr2_gate_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instExpr2_gate_none

/-- info: 'LeanModels.Sv.CombEq.skT_selfWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms skT_selfWidth

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

open Lean Elab Command in
/-- `#pin_axioms c₁ c₂ …`: an error unless every named constant depends on at most `propext`,
`Classical.choice` and `Quot.sound`; silent when it does. -/
elab "#pin_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwErrorAt id m!"'{n}' depends on the axiom '{a}'"

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

#pin_axioms rdsOf?_len skT_leaves Sk.low_irrel Sk.selfOk_widthOk rm_leaf skT_shape gate_shape
  XF.any_one XF.any_congr XF.eqv_one XF.all_congr XF.parity_congr XF.red_congr XF.eqv_congr xf_lnot
  xfb_lnot xf_red xfb_red xf_logical xfb_land xfb_lor xf_tern xfb_tern xf_eq xf_ne xfb_eq xfb_ne
  low_xf_gen

#pin_axioms CombProc.fit_idxFree

end CombEq
end LeanModels.Sv
