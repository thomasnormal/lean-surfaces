import LeanModels.Sv.CombViewMain
import LeanModels.Sv.CombKnownThm
import LeanModels.Sv.CombWord

/-!
# `sv_equations`, stage 1: the skeleton of a right-hand side, its Boolean reading, its lowering

Stage 2 of `docs/sv-comb-design.md`. `CombView*.lean` (lane M) gives, for a design in the fragment of
`PDesign.summary`, the footprints of every process of `X.sem N` and the obligations that make them
sound. This file adds what the EQUATIONS need: what the instantiated right-hand side of each
site actually IS, and what its Boolean value is.

## The skeleton `Sk`

A site of the summary stores its target (`Acc`), its read accesses in left-to-right leaf order
(`TSite.rds`) and the template process (`TSite.proc`). The right-hand side is, up to its leaves,
one of four shapes:

* a **gate tree**: `&`, `|`, `^` (left-associated exactly as the SV writes them) over literals and
  access leaves,
* a **concatenation** of literals and access leaves,
* a bare **fill** `'0` / `'1`,
* (a literal or a single access are gate trees with no gate).

`skRhs v rds` reads that shape off the template `v`, taking one access of `rds` per leaf in order
(`cnt` leaves per subtree). It is a plain structural function on closed data, so `simp` evaluates it
on the summary's literal sites without ever running the recognizer again.

* `Sk.bit σ dw rd k` — the Boolean bit `k` of the skeleton over a bit environment `rd`
  (`rd n i` = bit `i` of signal `n`); the expression shape of the SV is preserved
  (principle 10: `(a && b) || (c && (a ^^ b))`, `^` left-associated).
* `Sk.low σ dw tw` — the `Expr2` that `instantiate2` builds for it (`fitExpr2` at the target width
  `tw`): gates over `slice (ident n) lo w` leaves.
* `Sk.WidthOk` — the width obligation: every operand is exactly as wide as the target (otherwise
  `fitExpr2` inserts a `resize`, which this stage does not model).

## What is proved here

* `leaf_eq`: an access leaf instantiates to `accExpr` (the slice the access promises), and has
  its promised self-width;
* `gate_shape` / `concat_shape` / `rhs_shape`: `fitExpr2 E elems (some tw) v = (skRhs v rds).low σ dw tw`;
* `proc_shape`: `instProcess2 E elems proc = .assign (tgt.lhs σ) ((skRhs …).low σ dw tw)` for a site;
* `low_xfWidth` / `low_xfBits`: the lowered expression is in the x-free fragment of
  `CombKnownBits.lean` at width `tw` and its `Expr2.xfBits` is `Sk.bit`.
-/

namespace LeanModels.Sv
namespace CombEq
open CombView

/-! ## The skeleton -/

/-- A part of a concatenation: a literal or one access. -/
inductive Part where
  | lit (v : LVec)
  | rd (a : Acc)
  /-- WP-B2 gate 4c: a replication `{c{v}}` of a sized literal, `{c{a}}` of one access that is not a whole signal
  (the count affine, non-negative: an obligation of `InRangeObl`). -/
  | replit (c : Aff) (v : LVec)
  | reprd (c : Aff) (a : Acc)

/-- The bitwise gates of the fragment. -/
inductive Gate where
  | and
  | or
  | xor

def Gate.op : Gate → BinOp
  | .and => .and
  | .or => .or
  | .xor => .xor

/-- The shape of a right-hand side of the fragment. -/
inductive Sk where
  | lit (v : LVec)
  | rd (a : Acc)
  | gate (g : Gate) (l r : Sk)
  | cat (ps : List Part)
  | fill (b : Logic)
  /-- `~a` (WP-G S2): bitwise, context-determined. -/
  | bnot (a : Sk)
  /-- `!a`: logical, a 1-bit result over a self-determined operand. -/
  | lnot (a : Sk)
  /-- A reduction `|a`, `&a`, `^a`, `~|a`, `~&a`, `~^a`: 1 bit, self-determined operand. -/
  | red (op : RedOp) (a : Sk)
  /-- `l && r`, `l || r`: 1 bit, self-determined operands. -/
  | land (l r : Sk)
  | lor (l r : Sk)
  /-- `c ? a : b`: the condition is a self-determined 1-bit value, the arms are context-determined. -/
  | tern (c a b : Sk)
  /-- A comparison `l op r` (WP-G S2d for `==`, `!=`; WP-B2 gate 2b for the six): 1 bit. The operands are
  context-determined at the wider of their natural widths. -/
  | cmp (op : CmpOp) (l r : Sk)
  /-- A `Resize` marker (WP-B2) around a sized literal or ONE access: zero extension to the CONTEXT width. -/
  | ext (p : Part)
  /-- `l + r`, `l - r` (WP-B2): context-determined, the carry survives up to the context width. -/
  | add (l r : Sk)
  | sub (l r : Sk)
  /-- `l * r` (WP-B2): context-determined like `+`, the product taken modulo `2^` the context width. -/
  | mul (l r : Sk)
  /-- An unsized integer constant (WP-B2 gate 2b): 32 bits wide on its own, materialized at the context width. -/
  | const (v : Int)
  /-- A constant of the instance (WP-B2 gate 4b, `R`): a genvar named as a shift amount, `a << i`. Like `const`
  it is 32 bits wide on its own and reads nothing; its value is `a.eval σ`, so that the skeleton stays
  independent of the valuation. -/
  | cref (a : Aff)
  /-- A replication `{c{x}}` of a literal or one access (WP-B2 gate 4c), as an operand or a whole right-hand side:
  rigid, `c * w` bits wide. A replication INSIDE a concatenation is a `Part`; the same lowering. -/
  | rep (p : Part)
  /-- A `Resize` marker around an OPERATION (WP-B2 gate 2b): a truncation, or a zero extension of a result that
  does not follow the context (a comparison). `pr` says the operation follows a wider context
  (`PExpr.ctxPropagates`), decided when the skeleton is built. -/
  | rsz (pr : Bool) (p : Sk)
  /-- A run-time shift `l << r` (`dir = true`) or `l >> r` (WP-B2 gate 3): the left operand is context-determined
  (extended to the context BEFORE the shift, by zeros, or by its sign bit when `sg`: `1 << s`, the unsized constant is a
  signed integer), the amount self-determined and unsigned, and it never widens the result. A signed `>>` is not built
  (`sg = false` whenever `dir = false`). -/
  | sh (dir : Bool) (sg : Bool) (l r : Sk)
  /-- A signed comparison of two signed signals of one width (IEEE 1800-2023 §11.4.4, §11.8.1): one bit, the operands
  ordered as two's-complement integers. The operands are accesses (the recognizer reads `a < b` of two whole signed
  signals declared with the same dimensions, `rdsOfW?`). -/
  | scmp (op : CmpOp) (a b : Acc)

/-- The order comparisons (`<`, `<=`, `>`, `>=`): the ones the signed comparison node evaluates (`evalPure2`'s `scmp`
arm gives x for the others). -/
def _root_.LeanModels.Sv.CombView.CmpOp.ord : CmpOp → Bool
  | .eq | .ne => false
  | _ => true

/-- A signed comparison of two bit functions of width `w`, read as two's-complement integers (`BitVec.slt`/`sle`). -/
def scmpBit (op : CmpOp) (w : Nat) (f g : Nat → Bool) : Bool :=
  match op with
  | .lt => BitVec.slt (XF.bv w f) (XF.bv w g)
  | .le => BitVec.sle (XF.bv w f) (XF.bv w g)
  | .gt => BitVec.slt (XF.bv w g) (XF.bv w f)
  | .ge => BitVec.sle (XF.bv w g) (XF.bv w f)
  | .eq => XF.bv w f == XF.bv w g
  | .ne => XF.bv w f != XF.bv w g

/-! The four order arms of `scmpBit` as rewrite rules. The tactics rewrite with these rather than unfold `scmpBit`, so the
width argument is normalized while it is still an argument of `scmpBit` (a `Nat`), before it becomes the index of a
`BitVec` type, where `simp` cannot rewrite it. -/
theorem scmpBit_lt (w : Nat) (f g : Nat → Bool) : scmpBit .lt w f g = BitVec.slt (XF.bv w f) (XF.bv w g) := rfl
theorem scmpBit_le (w : Nat) (f g : Nat → Bool) : scmpBit .le w f g = BitVec.sle (XF.bv w f) (XF.bv w g) := rfl
theorem scmpBit_gt (w : Nat) (f g : Nat → Bool) : scmpBit .gt w f g = BitVec.slt (XF.bv w g) (XF.bv w f) := rfl
theorem scmpBit_ge (w : Nat) (f g : Nat → Bool) : scmpBit .ge w f g = BitVec.sle (XF.bv w g) (XF.bv w f) := rfl

/-- The skeleton of a gate over two skeletons (`gateOf` only produces `&`, `|`, `^`). -/
def mkGate : BinOp → Sk → Sk → Sk
  | .and, l, r => .gate .and l r
  | .or, l, r => .gate .or l r
  | .xor, l, r => .gate .xor l r
  | _, _, _ => .fill .l0

/-- The skeleton of a context-determined binary operator (`mkGate` plus `+` and `-`). -/
def mkOpW : BinOp → Sk → Sk → Sk
  | .add, l, r => .add l r
  | .sub, l, r => .sub l r
  | b, l, r => mkGate b l r

/-- Number of access leaves of the parts of a concatenation (literals take none). -/
def pcnt : List PExpr → Nat
  | [] => 0
  | p :: ps => (match p with | .lit _ => 0 | .repl _ (.concat [.lit _]) => 0 | _ => 1) + pcnt ps

/-- Number of access leaves of a gate tree. -/
def cnt : PExpr → Nat
  | .lit _ => 0
  | .binary _ l r => cnt l + cnt r
  | .unary _ a => cnt a
  | .reduce _ a => cnt a
  | .ternary c t e => cnt c + cnt t + cnt e
  | .int _ => 0
  | .paramRef _ _ => 0
  | .genvarRef _ => 0
  | .repl _ (.concat [.lit _]) => 0
  | .concat ps => pcnt ps
  | .signedResize _ e =>
      match e with
      | .lit _ => 0
      | .int _ => 0
      | _ => 1
  | .resize _ e =>
      match e with
      | .lit _ => 0
      | .int _ => 0
      | .binary _ l r => cnt l + cnt r
      | .unary _ a => cnt a
      | .reduce _ a => cnt a
      | .ternary c t f => cnt c + cnt t + cnt f
      | .concat ps => pcnt ps
      | _ => 1
  | _ => 1

/-- The parts of a concatenation: a literal part is itself, every other part takes the next access. -/
def partsT : List PExpr → List Acc → List Part
  | [], _ => []
  | p :: ps, as =>
      match p with
      | .lit v => .lit v :: partsT ps as
      | .repl c (.concat [.lit v]) => .replit (repAff c) v :: partsT ps as
      | .repl c _ => .reprd (repAff c) (as.headD (.whole "")) :: partsT ps (as.drop 1)
      | _ => .rd (as.headD (.whole "")) :: partsT ps (as.drop 1)

/-- The gate-tree skeleton of `v`, taking one access of `as` per leaf, left to right (a concatenation is the
skeleton `.cat` of its parts: the same node as the top-level concatenation, WP-B2 gate 3b). -/
def skT : PExpr → List Acc → Sk
  | .lit v, _ => .lit v
  | .binary op l r, as =>
      match gateOf op with
      | some g => mkGate g (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
      | none =>
          match op with
          | .land => .land (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .lor => .lor (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .eq => .cmp .eq (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .ne => .cmp .ne (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .lt => .cmp .lt (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .le => .cmp .le (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .gt => .cmp .gt (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .ge => .cmp .ge (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .add => .add (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 .sub => .sub (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .mul => .mul (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
          | .m0 (.shl false) =>
              .sh true false (match l with | .resize _ x => skT x (as.take (cnt l)) | x => skT x (as.take (cnt l)))
                (skT r (as.drop (cnt l)))
          | .m0 (.shl true) =>
              .sh true true
                (match l with | .signedResize _ x => skT x (as.take (cnt l)) | x => skT x (as.take (cnt l)))
                (skT r (as.drop (cnt l)))
          | .m0 (.shr false) =>
              .sh false false
                (match l with | .resize _ x => skT x (as.take (cnt l)) | x => skT x (as.take (cnt l)))
                (skT r (as.drop (cnt l)))
          | .slt => .scmp .lt (as.headD (.whole "")) ((as.drop 1).headD (.whole ""))
          | .sle => .scmp .le (as.headD (.whole "")) ((as.drop 1).headD (.whole ""))
          | .sgt => .scmp .gt (as.headD (.whole "")) ((as.drop 1).headD (.whole ""))
          | .sge => .scmp .ge (as.headD (.whole "")) ((as.drop 1).headD (.whole ""))
          | _ => .fill .l0
  | .unary op a, as =>
      match op with
      | .m0 .bnot => .bnot (skT a as)
      | .m0 .lnot => .lnot (skT a as)
      | _ => .fill .l0
  | .reduce op a, as => .red op (skT a as)
  | .ternary c t e, as =>
      .tern (skT c (as.take (cnt c))) (skT t ((as.drop (cnt c)).take (cnt t)))
        (skT e ((as.drop (cnt c)).drop (cnt t)))
  | .int v, _ => .const v
  | .genvarRef g, _ => .cref (Aff.var g)
  | .paramRef n none, _ => .cref (Aff.var n)
  | .repl c (.concat [.lit v]), _ => .rep (.replit (repAff c) v)
  | .repl c _, as => .rep (.reprd (repAff c) (as.headD (.whole "")))
  | .concat ps, as => .cat (partsT ps as)
  | .resize _ e, as =>
      match e with
      | .lit v => .ext (.lit v)
      | .ident _ => .ext (.rd (as.headD (.whole "")))
      | .bitSel .. => .ext (.rd (as.headD (.whole "")))
      | .arrayElem .. => .ext (.rd (as.headD (.whole "")))
      | .arrayPart .. => .ext (.rd (as.headD (.whole "")))
      | .partSel .. => .ext (.rd (as.headD (.whole "")))
      | .binary op _ _ =>
          match op with
          | .m0 .and | .m0 .or | .m0 .xor | .m0 .add | .m0 .sub | .mul | .m0 (.shl _) | .m0 (.shr false) =>
              .rsz true (skT e as)
          | _ => .rsz false (skT e as)
      | .unary op _ =>
          match op with
          | .m0 .bnot => .rsz true (skT e as)
          | _ => .rsz false (skT e as)
      | .ternary .. => .rsz true (skT e as)
      | _ => .rsz false (skT e as)
  | _, as => .rd (as.headD (.whole ""))

/-- The skeleton of a whole right-hand side. -/
def skRhs (v : PExpr) (as : List Acc) : Sk :=
  match v with
  | .fill b => .fill b
  | .concat ps => .cat (partsT ps as)
  | v => skT v as

/-- The right-hand side of a template process. -/
def rhsOf : PProcess → PExpr
  | .assign _ v => v
  | .assignL _ v => v
  | _ => .int 0

/-- Gate trees: literals, gates and access leaves, no concatenation or fill inside. -/
def fragG : PExpr → Bool
  | .lit _ => true
  | .binary _ l r => fragG l && fragG r
  | .unary _ a => fragG a
  | .reduce _ a => fragG a
  | .ternary c t e => fragG c && fragG t && fragG e
  | .concat _ => false
  | .fill _ => false
  | .resize _ a => fragG a
  | _ => true

/-- The word-level reading of "a gate tree" (WP-B2 gate 3b): as `fragG`, but a concatenation (of literals and
accesses: `partsRd?` has checked its parts) is accepted at the CONTEXT-determined positions of `rdsOfW?` (an operand of a
word-level operator, an arm of `?:`, the operand of `~`, under a `Resize` marker). The self-determined positions (`&&`,
`||`, `!`, the reductions, the condition of `?:`) keep `fragG`, so the v1 theorems apply to them unchanged. -/
def fragW : PExpr → Bool
  | .lit _ => true
  | .binary op l r => if selfOpW op then fragG l && fragG r else fragW l && fragW r
  | .unary op a => match op with | .m0 .lnot => fragG a | _ => fragW a
  | .reduce _ a => fragG a
  | .ternary c t e => fragG c && fragW t && fragW e
  | .concat _ => true
  | .fill _ => false
  | .resize _ a => fragW a
  | _ => true

theorem fragW_bin_ctx {op : SymBinOp} {l r : PExpr} (hs : selfOpW op = false)
    (h : fragW (.binary op l r) = true) : fragW l = true ∧ fragW r = true := by
  simpa [fragW, hs] using h

theorem fragW_bin_self {op : SymBinOp} {l r : PExpr} (hs : selfOpW op = true)
    (h : fragW (.binary op l r) = true) : fragG l = true ∧ fragG r = true := by
  simpa [fragW, hs] using h

/-- The right-hand sides `sv_equations` reads: a fill, or an expression of the word-level fragment (a concatenation
included). -/
def fragOk : PExpr → Bool
  | .fill _ => true
  | v => fragW v

/-- WP-B2 gates 4b and 4c: a leaf of an `always_comb` body is a right-hand side of the fragment that names no constant
of the instance (a genvar shift amount) and replicates nothing (the count is a constant of the instance): the proc
chain does not carry the scope. -/
def fragOkL (v : PExpr) : Bool := fragOk v && noConst v && v.scmpPairs.isEmpty

theorem fragOkL_spec {v : PExpr} (h : fragOkL v = true) :
    fragOk v = true ∧ v.cnames = [] ∧ v.rcounts = [] := by
  unfold fragOkL at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, (noConst_spec v h.1.2).1, (noConst_spec v h.1.2).2⟩

/-- An `always_comb` leaf compares no signed signals (the procedural route reads signed comparisons nowhere yet). -/
theorem fragOkL_scmp {v : PExpr} (h : fragOkL v = true) : v.scmpPairs = [] := by
  unfold fragOkL at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.2

/-- … so the width fact of its signed comparisons holds vacuously. -/
theorem fragOkL_weq {v : PExpr} {DW : String → Option Nat} (h : fragOkL v = true) :
    ∀ p ∈ v.scmpPairs, DW p.1 = DW p.2 := by
  rw [fragOkL_scmp h]; simp

theorem fragOkL_co {v : PExpr} {σ : String → Int} {ns : List String} (h : fragOkL v = true) : ConstOK σ ns v := by
  obtain ⟨-, h1, h2⟩ := fragOkL_spec h
  refine ⟨fun n hn => ?_, fun c hc => ?_⟩
  · rw [h1] at hn; simp at hn
  · rw [h2] at hc; simp at hc

/-! ## Boolean reading -/

/-- Bit `k` of an access over a bit environment (`rd n i` = bit `i` of signal `n`). -/
def accBit (σ : String → Int) (rd : String → Nat → Bool) (a : Acc) (k : Nat) : Bool :=
  rd a.name (Acc.lo σ a + k)

def Part.wid (σ : String → Int) (dw : String → Nat) : Part → Nat
  | .lit v => v.width
  | .rd a => (a.win σ dw).2.2
  | .replit c v => (c.eval σ).toNat * v.width
  | .reprd c a => (c.eval σ).toNat * Acc.wid σ a

def Part.bit (σ : String → Int) (rd : String → Nat → Bool) : Part → Nat → Bool
  | .lit v => fun k => v.boolAt k
  | .rd a => fun k => accBit σ rd a k
  | .replit _ v => fun k => v.boolAt (k % v.width)
  | .reprd _ a => fun k => accBit σ rd a (k % Acc.wid σ a)

/-- A concatenation: parts in source order, the first part most significant. -/
def catBit (σ : String → Int) (dw : String → Nat) (rd : String → Nat → Bool) :
    List Part → Nat → Bool
  | [], _ => false
  | p :: ps, k =>
      if k < (ps.map (Part.wid σ dw)).sum then catBit σ dw rd ps k
      else p.bit σ rd (k - (ps.map (Part.wid σ dw)).sum)

/-- The self-determined (natural) width of a skeleton, `selfWidth2` of its expression: a gate, `+`, `-` or
conditional has the widest of its operands (`Sk.SelfOk` / `Sk.WidthOk` say they agree where the v1 reading
needs it), a marker the width of its operand, the 1-bit operators width 1. -/
def Sk.width (σ : String → Int) (dw : String → Nat) : Sk → Nat
  | .lit v => v.width
  | .rd a => (a.win σ dw).2.2
  | .gate _ l r => max (l.width σ dw) (r.width σ dw)
  | .cat ps => (ps.map (Part.wid σ dw)).sum
  | .rep p => p.wid σ dw
  | .fill _ => 0
  | .bnot a => a.width σ dw
  | .lnot _ => 1
  | .red _ _ => 1
  | .land _ _ => 1
  | .lor _ _ => 1
  | .tern _ a b => max (a.width σ dw) (b.width σ dw)
  | .cmp _ _ _ => 1
  | .ext p => p.wid σ dw
  | .add l r => max (l.width σ dw) (r.width σ dw)
  | .sub l r => max (l.width σ dw) (r.width σ dw)
  | .mul l r => max (l.width σ dw) (r.width σ dw)
  | .const _ => 32
  | .cref _ => 32
  | .rsz _ p => p.width σ dw
  | .sh _ _ l _ => l.width σ dw
  | .scmp _ _ _ => 1

/-- Bit `k` of the skeleton. -/
def Sk.bit (σ : String → Int) (dw : String → Nat) (rd : String → Nat → Bool) : Sk → Nat → Bool
  | .lit v, k => v.boolAt k
  | .rd a, k => accBit σ rd a k
  | .gate .and l r, k => l.bit σ dw rd k && r.bit σ dw rd k
  | .gate .or l r, k => l.bit σ dw rd k || r.bit σ dw rd k
  | .gate .xor l r, k => l.bit σ dw rd k ^^ r.bit σ dw rd k
  | .cat ps, k => catBit σ dw rd ps k
  | .rep p, k => p.bit σ rd k
  | .fill b, _ => b == Logic.l1
  | .bnot a, k => !(a.bit σ dw rd k)
  | .lnot a, _ => !(XF.any (a.width σ dw) (a.bit σ dw rd))
  | .red op a, _ => XF.red op (a.width σ dw) (a.bit σ dw rd)
  | .land l r, _ =>
      XF.any (l.width σ dw) (l.bit σ dw rd) && XF.any (r.width σ dw) (r.bit σ dw rd)
  | .lor l r, _ =>
      XF.any (l.width σ dw) (l.bit σ dw rd) || XF.any (r.width σ dw) (r.bit σ dw rd)
  | .tern c a b, k => if c.bit σ dw rd 0 then a.bit σ dw rd k else b.bit σ dw rd k
  | .cmp .eq l r, _ => XF.eqv (l.width σ dw) (l.bit σ dw rd) (r.bit σ dw rd)
  | .cmp .ne l r, _ => !XF.eqv (l.width σ dw) (l.bit σ dw rd) (r.bit σ dw rd)
  | .cmp .lt l r, _ => decide (XF.val (l.bit σ dw rd) (l.width σ dw) < XF.val (r.bit σ dw rd) (l.width σ dw))
  | .cmp .le l r, _ => decide (XF.val (l.bit σ dw rd) (l.width σ dw) ≤ XF.val (r.bit σ dw rd) (l.width σ dw))
  | .cmp .gt l r, _ => decide (XF.val (l.bit σ dw rd) (l.width σ dw) > XF.val (r.bit σ dw rd) (l.width σ dw))
  | .cmp .ge l r, _ => decide (XF.val (l.bit σ dw rd) (l.width σ dw) ≥ XF.val (r.bit σ dw rd) (l.width σ dw))
  -- the word-level nodes are read by `Sk.bitC` (they need the context width); `Sk.WidthOk` is false for them
  | .ext _, _ => false
  | .add _ _, _ => false
  | .sub _ _, _ => false
  | .mul _ _, _ => false
  | .const _, _ => false
  | .cref _, _ => false
  | .rsz _ _, _ => false
  | .sh _ _ _ _, _ => false
  | .scmp _ _ _, _ => false

/-! ## Lowering -/

/-- The expression an access instantiates to. -/
def accExpr (σ : String → Int) : Acc → Expr2
  | .whole n => .ident n
  | .bit n a => .slice (.ident n) (Acc.lo σ (.bit n a)) (Acc.wid σ (.bit n a))
  | .cell1 n a => .slice (.ident n) (Acc.lo σ (.cell1 n a)) (Acc.wid σ (.cell1 n a))
  | .row n w r => .slice (.ident n) (Acc.lo σ (.row n w r)) (Acc.wid σ (.row n w r))
  | .cell2 n w r c => .slice (.ident n) (Acc.lo σ (.cell2 n w r c)) (Acc.wid σ (.cell2 n w r c))
  | .part1 n hi lo => .slice (.ident n) (Acc.lo σ (.part1 n hi lo)) (Acc.wid σ (.part1 n hi lo))
  | .part2 n w r hi lo =>
      .slice (.ident n) (Acc.lo σ (.part2 n w r hi lo)) (Acc.wid σ (.part2 n w r hi lo))

def Part.expr (σ : String → Int) : Part → Expr2
  | .lit v => .lit v
  | .rd a => accExpr σ a
  | .replit c v => .repl (c.eval σ).toNat (.concat #[.lit v])
  | .reprd c a => .repl (c.eval σ).toNat (.concat #[accExpr σ a])

/-- The expression `instantiate2` builds for the skeleton at target width `tw`. `tw` is read only by `.fill`; the
operands of the self-determined operators (`!`, reductions, `&&`, `||`, `==`, the `?:` condition) are lowered
at the dummy width `0` (they contain no `.fill`: `Sk.SelfOk`, `Sk.low_irrel`). -/
def Sk.low (σ : String → Int) (dw : String → Nat) (tw : Nat) : Sk → Expr2
  | .lit v => .lit v
  | .rd a => accExpr σ a
  | .gate g l r => .binary g.op (l.low σ dw tw) (r.low σ dw tw)
  | .cat ps => .concat (ps.map (Part.expr σ)).toArray
  | .rep p => p.expr σ
  | .fill b => .lit (LVec.replicate tw b)
  | .bnot a => .unary .bnot (a.low σ dw tw)
  | .lnot a => .unary .lnot (a.low σ dw 0)
  | .red op a => .reduce op (a.low σ dw 0)
  | .land l r => .logical true (l.low σ dw 0) (r.low σ dw 0)
  | .lor l r => .logical false (l.low σ dw 0) (r.low σ dw 0)
  | .tern c a b => .ternary (c.low σ dw 0) (a.low σ dw tw) (b.low σ dw tw)
  | .cmp op l r =>
      .binary op.ex (l.low σ dw (max (l.width σ dw) (r.width σ dw))) (r.low σ dw (max (l.width σ dw) (r.width σ dw)))
  | .ext p => .resize tw (p.expr σ)
  | .add l r => .binary .add (l.low σ dw tw) (r.low σ dw tw)
  | .sub l r => .binary .sub (l.low σ dw tw) (r.low σ dw tw)
  | .mul l r => .binary .mul (l.low σ dw tw) (r.low σ dw tw)
  | .const v => .lit (LVec.ofInt tw v)
  | .cref a => .lit (LVec.ofInt tw (a.eval σ))
  | .rsz true p =>
      if p.width σ dw < tw then p.low σ dw tw else .resize tw (p.low σ dw (p.width σ dw))
  | .rsz false p => .resize tw (p.low σ dw (p.width σ dw))
  | .scmp op a b => .scmp op.ex (accExpr σ a) (accExpr σ b)
  | .sh d sg l r =>
      let L := if max tw (l.width σ dw) = l.width σ dw then l.low σ dw (l.width σ dw)
        else if sg then .resizeSigned (max tw (l.width σ dw)) (l.low σ dw (l.width σ dw))
        else .resize (max tw (l.width σ dw)) (l.low σ dw (l.width σ dw))
      let E := Expr2.binary (if d then BinOp.shl sg else BinOp.shr sg) L (r.low σ dw (r.width σ dw))
      if max tw (l.width σ dw) ≤ tw then E else .resize tw E

/-- A skeleton in a self-determined position (WP-G S2): no `.fill`, and every gate, comparison and
conditional has operands of one width (the arms of a `?:` agree, its condition is one bit). -/
def Sk.SelfOk (σ : String → Int) (dw : String → Nat) : Sk → Prop
  | .lit _ => True
  | .rd _ => True
  | .gate _ l r => l.SelfOk σ dw ∧ r.SelfOk σ dw ∧ l.width σ dw = r.width σ dw
  | .cat _ => True
  | .rep _ => True
  | .fill _ => False
  | .bnot a => a.SelfOk σ dw
  | .lnot a => a.SelfOk σ dw
  | .red _ a => a.SelfOk σ dw
  | .land l r => l.SelfOk σ dw ∧ r.SelfOk σ dw
  | .lor l r => l.SelfOk σ dw ∧ r.SelfOk σ dw
  | .tern c a b =>
      c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.SelfOk σ dw ∧ b.SelfOk σ dw ∧ a.width σ dw = b.width σ dw
  | .cmp _ l r => l.SelfOk σ dw ∧ r.SelfOk σ dw ∧ l.width σ dw = r.width σ dw
  | .ext _ => False
  | .add _ _ => False
  | .sub _ _ => False
  | .mul _ _ => False
  | .const _ => False
  | .cref _ => False
  | .rsz _ _ => False
  | .sh _ _ _ _ => False
  | .scmp _ _ _ => False

/-- Every operand is exactly as wide as the target (no `resize` is inserted); the self-determined operands
of `!`, reductions, `&&`, `||`, `==`, `!=` and the `?:` condition are consistent among themselves, and the
1-bit operators sit at width one. -/
def Sk.WidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : Sk → Prop
  | .lit v => v.width = tw
  | .rd a => (a.win σ dw).2.2 = tw
  | .gate _ l r => l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw
  | .cat ps => (ps.map (Part.wid σ dw)).sum = tw
  | .rep p => p.wid σ dw = tw
  | .fill _ => True
  | .bnot a => a.WidthOk σ dw tw
  | .lnot a => tw = 1 ∧ a.SelfOk σ dw
  | .red _ a => tw = 1 ∧ a.SelfOk σ dw
  | .land l r => tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw
  | .lor l r => tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw
  | .tern c a b =>
      c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.WidthOk σ dw tw ∧ b.WidthOk σ dw tw
  | .cmp _ l r => tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw ∧ l.width σ dw = r.width σ dw
  | .ext _ => False
  | .add _ _ => False
  | .sub _ _ => False
  | .mul _ _ => False
  | .const _ => False
  | .cref _ => False
  | .rsz _ _ => False
  | .sh _ _ _ _ => False
  | .scmp _ _ _ => False

/-- The access leaves. -/
def partLeaves : List Part → List Acc
  | [] => []
  | .lit _ :: ps => partLeaves ps
  | .rd a :: ps => a :: partLeaves ps
  | .replit _ _ :: ps => partLeaves ps
  | .reprd _ a :: ps => a :: partLeaves ps

def Sk.leaves : Sk → List Acc
  | .lit _ => []
  | .rd a => [a]
  | .gate _ l r => l.leaves ++ r.leaves
  | .cat ps => partLeaves ps
  | .rep p => partLeaves [p]
  | .fill _ => []
  | .bnot a => a.leaves
  | .lnot a => a.leaves
  | .red _ a => a.leaves
  | .land l r => l.leaves ++ r.leaves
  | .lor l r => l.leaves ++ r.leaves
  | .tern c a b => c.leaves ++ a.leaves ++ b.leaves
  | .cmp _ l r => l.leaves ++ r.leaves
  | .ext p => partLeaves [p]
  | .add l r => l.leaves ++ r.leaves
  | .sub l r => l.leaves ++ r.leaves
  | .mul l r => l.leaves ++ r.leaves
  | .const _ => []
  | .cref _ => []
  | .rsz _ p => p.leaves
  | .sh _ _ l r => l.leaves ++ r.leaves
  | .scmp _ a b => [a, b]

/-- A replicated access is never a whole signal (the recognizer refuses it: its width is the declared one, which
`Part.wid` does not read), and `partKnown` checks it, so the x-free layer can use `win` for its width. -/
def _root_.LeanModels.Sv.CombView.Acc.isWhole : Acc → Bool
  | .whole _ => true
  | _ => false

/-- Literals and fills carry no `x`/`z`. -/
def partKnown : List Part → Bool
  | [] => true
  | .lit v :: ps => v.knownB && partKnown ps
  | .rd _ :: ps => partKnown ps
  | .replit _ v :: ps => v.knownB && partKnown ps
  | .reprd _ a :: ps => !a.isWhole && partKnown ps

def Sk.knownB : Sk → Bool
  | .lit v => v.knownB
  | .rd _ => true
  | .gate _ l r => l.knownB && r.knownB
  | .cat ps => partKnown ps
  | .rep p => partKnown [p]
  | .fill b => b.isKnown
  | .bnot a => a.knownB
  | .lnot a => a.knownB
  | .red _ a => a.knownB
  | .land l r => l.knownB && r.knownB
  | .lor l r => l.knownB && r.knownB
  | .tern c a b => c.knownB && a.knownB && b.knownB
  | .cmp _ l r => l.knownB && r.knownB
  | .ext p => partKnown [p]
  | .add l r => l.knownB && r.knownB
  | .sub l r => l.knownB && r.knownB
  | .mul l r => l.knownB && r.knownB
  | .const _ => true
  | .cref _ => true
  | .rsz _ p => p.knownB
  | .sh _ _ l r => l.knownB && r.knownB
  | .scmp op _ _ => op.ord

/-! ## Self-determined skeletons (WP-G S2) -/

/-- `Sk.low` reads its width argument only at a `.fill`: a skeleton in a self-determined position has none. -/
theorem Sk.low_irrel (σ : String → Int) (dw : String → Nat) :
    ∀ (sk : Sk), sk.SelfOk σ dw → ∀ t1 t2, sk.low σ dw t1 = sk.low σ dw t2
  | .lit _, _, _, _ => rfl
  | .rd _, _, _, _ => rfl
  | .gate g l r, h, t1, t2 => by
      simp only [Sk.low, Sk.low_irrel σ dw l h.1 t1 t2, Sk.low_irrel σ dw r h.2.1 t1 t2]
  | .cat _, _, _, _ => rfl
  | .rep _, _, _, _ => rfl
  | .fill _, h, _, _ => by simp [Sk.SelfOk] at h
  | .bnot a, h, t1, t2 => by simp only [Sk.low, Sk.low_irrel σ dw a h t1 t2]
  | .lnot _, _, _, _ => rfl
  | .red _ _, _, _, _ => rfl
  | .land _ _, _, _, _ => rfl
  | .lor _ _, _, _, _ => rfl
  | .tern c a b, h, t1, t2 => by
      simp only [Sk.low, Sk.low_irrel σ dw a h.2.2.1 t1 t2, Sk.low_irrel σ dw b h.2.2.2.1 t1 t2]
  | .cmp _ _ _, _, _, _ => rfl
  | .ext _, h, _, _ => by simp [Sk.SelfOk] at h
  | .add _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .sub _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .mul _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .const _, h, _, _ => by simp [Sk.SelfOk] at h
  | .cref _, h, _, _ => by simp [Sk.SelfOk] at h
  | .rsz _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .sh _ _ _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .scmp _ _ _, h, _, _ => by simp [Sk.SelfOk] at h

/-- A self-determined skeleton is well formed at its own width. -/
theorem Sk.selfOk_widthOk (σ : String → Int) (dw : String → Nat) :
    ∀ (sk : Sk), sk.SelfOk σ dw → sk.WidthOk σ dw (sk.width σ dw)
  | .lit _, _ => rfl
  | .rd _, _ => rfl
  | .gate g l r, h => by
      have e : max (l.width σ dw) (r.width σ dw) = l.width σ dw := by rw [h.2.2]; exact Nat.max_self _
      have h1 := Sk.selfOk_widthOk σ dw l h.1
      have h2 := Sk.selfOk_widthOk σ dw r h.2.1
      rw [← h.2.2] at h2
      show l.WidthOk σ dw (max (l.width σ dw) (r.width σ dw)) ∧ r.WidthOk σ dw (max (l.width σ dw) (r.width σ dw))
      rw [e]; exact ⟨h1, h2⟩
  | .cat _, _ => rfl
  | .rep _, _ => rfl
  | .fill _, h => by simp [Sk.SelfOk] at h
  | .bnot a, h => Sk.selfOk_widthOk σ dw a h
  | .lnot _, h => ⟨rfl, h⟩
  | .red _ _, h => ⟨rfl, h⟩
  | .land _ _, h => ⟨rfl, h.1, h.2⟩
  | .lor _ _, h => ⟨rfl, h.1, h.2⟩
  | .tern c a b, h => by
      have e : max (a.width σ dw) (b.width σ dw) = a.width σ dw := by rw [h.2.2.2.2]; exact Nat.max_self _
      have h1 := Sk.selfOk_widthOk σ dw a h.2.2.1
      have h2 := Sk.selfOk_widthOk σ dw b h.2.2.2.1
      rw [← h.2.2.2.2] at h2
      show c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.WidthOk σ dw (max (a.width σ dw) (b.width σ dw)) ∧
        b.WidthOk σ dw (max (a.width σ dw) (b.width σ dw))
      rw [e]; exact ⟨h.1, h.2.1, h1, h2⟩
  | .cmp _ _ _, h => ⟨rfl, h.1, h.2.1, h.2.2⟩
  | .ext _, h => by simp [Sk.SelfOk] at h
  | .add _ _, h => by simp [Sk.SelfOk] at h
  | .sub _ _, h => by simp [Sk.SelfOk] at h
  | .mul _ _, h => by simp [Sk.SelfOk] at h
  | .const _, h => by simp [Sk.SelfOk] at h
  | .cref _, h => by simp [Sk.SelfOk] at h
  | .rsz _ _, h => by simp [Sk.SelfOk] at h
  | .sh _ _ _ _, h => by simp [Sk.SelfOk] at h
  | .scmp _ _ _, h => by simp [Sk.SelfOk] at h

/-! ## The word-level reading (WP-B2): `+`, `-`, the `Resize` marker

The v1 definitions above (`Sk.bit`, `Sk.WidthOk`, `Sk.SelfOk`, `Sk.width`) stay as they are: the `always_comb`
chain (`CombProc*.lean`) is built on them with their exact meaning, and for the new nodes they say `False` /
`false`. The word-level reading is a parallel set of names, which gate 2 merges with the old ones:

* `Sk.width` — the NATURAL (self-determined) width, a max over the operands (`selfWidth2`, `rigidMax2` of the
  expression); the context-determined operators have a natural width below the context when an operand is a marker;
* `Sk.WidthOkC σ dw tw` — every context-determined operand fits the context `tw`: a bare access exactly, a marker at
  most; the self-determined operands are v1 skeletons (`Sk.SelfOk`, no marker, no `+`/`-`);
* `Sk.bitC σ dw tw rd` — bit `k` at the CONTEXT width `tw`, which `+` and `-` read (the carry survives up to `tw`);
  the self-determined operands are read by the v1 `Sk.bit` (they contain no word-level node). -/

/-- A marker at the root. -/
def Sk.isExt : Sk → Bool
  | .ext _ => true
  | .rsz _ _ => true
  | _ => false

/-- The widest operand that can carry `x`/`z` bits (`rigidMax2` of the expression): constants carry none. -/
def Sk.maxO : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

def Sk.rmax (σ : String → Int) (dw : String → Nat) : Sk → Option Nat
  | .lit v => some v.width
  | .rd a => some (a.win σ dw).2.2
  | .gate _ l r => Sk.maxO (l.rmax σ dw) (r.rmax σ dw)
  | .cat ps => some (ps.map (Part.wid σ dw)).sum
  | .rep p => some (p.wid σ dw)
  | .fill _ => none
  | .bnot a => a.rmax σ dw
  | .lnot _ => some 1
  | .red _ _ => some 1
  | .land _ _ => some 1
  | .lor _ _ => some 1
  | .tern _ a b => Sk.maxO (a.rmax σ dw) (b.rmax σ dw)
  | .cmp _ _ _ => some 1
  | .ext p => some (p.wid σ dw)
  | .add l r => Sk.maxO (l.rmax σ dw) (r.rmax σ dw)
  | .sub l r => Sk.maxO (l.rmax σ dw) (r.rmax σ dw)
  | .mul l r => Sk.maxO (l.rmax σ dw) (r.rmax σ dw)
  | .const _ => none
  | .cref _ => none
  | .rsz _ p => p.rmax σ dw
  | .sh _ _ l _ => some (l.width σ dw)
  | .scmp _ _ _ => some 1

/-- The rigid width of a concatenation: the sum of its parts (a rewrite rule of the tactics' normal form: the width obligation
of a marker around a concatenation that is an operand of `+`/`-` reads `Sk.rok`). -/
theorem Sk.rmax_cat (σ : String → Int) (dw : String → Nat) (ps : List Part) :
    Sk.rmax σ dw (.cat ps) = some (ps.map (Part.wid σ dw)).sum := rfl

/-- `ctxOpWidth2` is the rigid-width maximum. -/
theorem ctxOpWidth2_eq (env : IEnv) (elems : List (String × Nat)) (l r : PExpr) :
    ctxOpWidth2 env elems l r = Sk.maxO (rigidMax2 env elems l) (rigidMax2 env elems r) := by
  unfold ctxOpWidth2
  rcases rigidMax2 env elems l with _ | a <;> rcases rigidMax2 env elems r with _ | b <;> rfl

/-- `rigidMax2` of a context-determined binary operator is `ctxOpWidth2`. -/
theorem rm_ctx (env : IEnv) (elems : List (String × Nat)) (b : BinOp)
    (hb : b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub) (l r : PExpr) :
    rigidMax2 env elems (.binary (.m0 b) l r) = ctxOpWidth2 env elems l r := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rm_tern_maxO (env : IEnv) (elems : List (String × Nat)) (c t f : PExpr) :
    rigidMax2 env elems (.ternary c t f) = Sk.maxO (rigidMax2 env elems t) (rigidMax2 env elems f) := by
  simp only [rigidMax2]
  rcases rigidMax2 env elems t with _ | a <;> rcases rigidMax2 env elems f with _ | b <;> rfl

theorem Sk.getD_le {o : Option Nat} {tw : Nat} (h : o.getD 0 ≤ tw) : o.getD tw ≤ tw := by
  cases o <;> simp_all

theorem Sk.maxO_getD_le {a b : Option Nat} {tw : Nat} (ha : a.getD 0 ≤ tw) (hb : b.getD 0 ≤ tw) :
    (Sk.maxO a b).getD tw ≤ tw := by
  cases a <;> cases b <;> simp_all [Sk.maxO] <;> omega

/-- The part of the add/sub contract about truncation markers: an operand whose rigid width exceeds the context makes
`instExpr2` operate at that width and truncate (a different shape, refused): reachable only through a `rsz`. -/
def Sk.rok (σ : String → Int) (dw : String → Nat) (tw : Nat) : Sk → Prop
  | .gate _ l r => l.rok σ dw tw ∧ r.rok σ dw tw
  | .bnot a => a.rok σ dw tw
  | .tern _ a b => a.rok σ dw tw ∧ b.rok σ dw tw
  | .add l r => l.rok σ dw tw ∧ r.rok σ dw tw
  | .sub l r => l.rok σ dw tw ∧ r.rok σ dw tw
  | .mul l r => l.rok σ dw tw ∧ r.rok σ dw tw
  | .rsz _ p => (p.rmax σ dw).getD 0 ≤ tw
  | .sh _ _ l _ => l.width σ dw ≤ tw
  | _ => True

/-- **The width contract of the word-level fragment**: every context-determined operand fits the context `tw`. -/
def Sk.WidthOkC (σ : String → Int) (dw : String → Nat) (tw : Nat) : Sk → Prop
  | .lit v => v.width = tw
  | .rd a => (a.win σ dw).2.2 = tw
  | .gate _ l r => l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw
  | .cat ps => (ps.map (Part.wid σ dw)).sum = tw
  | .rep p => p.wid σ dw = tw
  | .fill _ => True
  | .bnot a => a.WidthOkC σ dw tw ∧ a.rok σ dw tw
  | .lnot a => tw = 1 ∧ a.SelfOk σ dw
  | .red _ a => tw = 1 ∧ a.SelfOk σ dw
  | .land l r => tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw
  | .lor l r => tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw
  | .tern c a b =>
      c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.WidthOkC σ dw tw ∧ b.WidthOkC σ dw tw
  | .cmp _ l r =>
      tw = 1 ∧ l.WidthOkC σ dw (max (l.width σ dw) (r.width σ dw)) ∧
        r.WidthOkC σ dw (max (l.width σ dw) (r.width σ dw))
  | .ext p => p.wid σ dw ≤ tw
  | .add l r => l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw ∧ l.rok σ dw tw ∧ r.rok σ dw tw
  | .sub l r => l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw ∧ l.rok σ dw tw ∧ r.rok σ dw tw
  | .mul l r => l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw ∧ l.rok σ dw tw ∧ r.rok σ dw tw
  | .const _ => True
  | .cref _ => True
  | .rsz true p =>
      if p.width σ dw < tw then p.WidthOkC σ dw tw else p.WidthOkC σ dw (p.width σ dw)
  | .rsz false p => p.WidthOkC σ dw (p.width σ dw)
  | .sh _ _ l r => l.WidthOkC σ dw (l.width σ dw) ∧ r.WidthOkC σ dw (r.width σ dw)
  | .scmp _ a b => tw = 1 ∧ (a.win σ dw).2.2 = (b.win σ dw).2.2

/-- Bit `k` of the skeleton at the context width `tw`. The self-determined operands are read at their OWN width
(`Sk.bitC_of_selfOk`: they are v1 skeletons, whose bits do not depend on the context). -/
def Sk.bitC (σ : String → Int) (dw : String → Nat) (tw : Nat) (rd : String → Nat → Bool) :
    Sk → Nat → Bool
  | .lit v, k => v.boolAt k
  | .rd a, k => accBit σ rd a k
  | .gate .and l r, k => l.bitC σ dw tw rd k && r.bitC σ dw tw rd k
  | .gate .or l r, k => l.bitC σ dw tw rd k || r.bitC σ dw tw rd k
  | .gate .xor l r, k => l.bitC σ dw tw rd k ^^ r.bitC σ dw tw rd k
  | .cat ps, k => catBit σ dw rd ps k
  | .rep p, k => p.bit σ rd k
  | .fill b, _ => b == Logic.l1
  | .bnot a, k => !(a.bitC σ dw tw rd k)
  | .lnot a, _ => !(XF.any (a.width σ dw) (a.bitC σ dw (a.width σ dw) rd))
  | .red op a, _ => XF.red op (a.width σ dw) (a.bitC σ dw (a.width σ dw) rd)
  | .land l r, _ =>
      XF.any (l.width σ dw) (l.bitC σ dw (l.width σ dw) rd) &&
        XF.any (r.width σ dw) (r.bitC σ dw (r.width σ dw) rd)
  | .lor l r, _ =>
      XF.any (l.width σ dw) (l.bitC σ dw (l.width σ dw) rd) ||
        XF.any (r.width σ dw) (r.bitC σ dw (r.width σ dw) rd)
  | .tern c a b, k =>
      if c.bitC σ dw 1 rd 0 then a.bitC σ dw tw rd k else b.bitC σ dw tw rd k
  | .cmp .eq l r, _ =>
      XF.eqv (max (l.width σ dw) (r.width σ dw)) (l.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd)
        (r.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd)
  | .cmp .ne l r, _ =>
      !XF.eqv (max (l.width σ dw) (r.width σ dw)) (l.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd)
        (r.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd)
  | .cmp .lt l r, _ =>
      decide (XF.val (l.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)) <
        XF.val (r.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)))
  | .cmp .le l r, _ =>
      decide (XF.val (l.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)) ≤
        XF.val (r.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)))
  | .cmp .gt l r, _ =>
      decide (XF.val (l.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)) >
        XF.val (r.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)))
  | .cmp .ge l r, _ =>
      decide (XF.val (l.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)) ≥
        XF.val (r.bitC σ dw (max (l.width σ dw) (r.width σ dw)) rd) (max (l.width σ dw) (r.width σ dw)))
  | .ext p, k => XF.zext (p.wid σ dw) (p.bit σ rd) k
  | .add l r, k => XF.addBits tw (l.bitC σ dw tw rd) tw (r.bitC σ dw tw rd) k
  | .sub l r, k => XF.subBits tw (l.bitC σ dw tw rd) tw (r.bitC σ dw tw rd) k
  | .mul l r, k => XF.mulBits tw (l.bitC σ dw tw rd) tw (r.bitC σ dw tw rd) k
  | .const v, k => XF.constBit v tw k
  | .cref a, k => XF.constBit (a.eval σ) tw k
  | .rsz true p, k =>
      if p.width σ dw < tw then p.bitC σ dw tw rd k
      else XF.zext (p.width σ dw) (p.bitC σ dw (p.width σ dw) rd) k
  | .rsz false p, k => XF.zext (p.width σ dw) (p.bitC σ dw (p.width σ dw) rd) k
  | .scmp op a b, _ => scmpBit op (a.win σ dw).2.2 (fun i => accBit σ rd a i) (fun i => accBit σ rd b i)
  | .sh true false l r, k =>
      XF.shlBits (XF.zext (l.width σ dw) (l.bitC σ dw (l.width σ dw) rd)) (r.width σ dw)
        (r.bitC σ dw (r.width σ dw) rd) k
  | .sh true true l r, k =>
      XF.shlBits (XF.sext (l.width σ dw) (l.bitC σ dw (l.width σ dw) rd)) (r.width σ dw)
        (r.bitC σ dw (r.width σ dw) rd) k
  | .sh false false l r, k =>
      XF.shrBits (l.width σ dw) (l.bitC σ dw (l.width σ dw) rd) (r.width σ dw) (r.bitC σ dw (r.width σ dw) rd) k
  | .sh false true l r, k =>
      XF.shrBits (max tw (l.width σ dw)) (XF.sext (l.width σ dw) (l.bitC σ dw (l.width σ dw) rd)) (r.width σ dw)
        (r.bitC σ dw (r.width σ dw) rd) k

/-- **A v1 skeleton reads the same at every context**: `Sk.bitC` of a self-determined skeleton is its v1 `Sk.bit`. -/
theorem Sk.bitC_of_selfOk (σ : String → Int) (dw : String → Nat) (rd : String → Nat → Bool) :
    ∀ (sk : Sk), sk.SelfOk σ dw → ∀ tw k, sk.bitC σ dw tw rd k = sk.bit σ dw rd k
  | .lit _, _, _, _ => rfl
  | .rd _, _, _, _ => rfl
  | .gate g l r, h, tw, k => by
      cases g <;> simp only [Sk.bitC, Sk.bit, Sk.bitC_of_selfOk σ dw rd l h.1, Sk.bitC_of_selfOk σ dw rd r h.2.1]
  | .cat _, _, _, _ => rfl
  | .rep _, _, _, _ => rfl
  | .fill _, h, _, _ => by simp [Sk.SelfOk] at h
  | .bnot a, h, tw, k => by simp only [Sk.bitC, Sk.bit, Sk.bitC_of_selfOk σ dw rd a h]
  | .lnot a, h, tw, k => by
      simp only [Sk.bitC, Sk.bit]
      have e : a.bitC σ dw (a.width σ dw) rd = a.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd a h _ j
      rw [e]
  | .red op a, h, tw, k => by
      simp only [Sk.bitC, Sk.bit]
      have e : a.bitC σ dw (a.width σ dw) rd = a.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd a h _ j
      rw [e]
  | .land l r, h, tw, k => by
      simp only [Sk.bitC, Sk.bit]
      have e1 : l.bitC σ dw (l.width σ dw) rd = l.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd l h.1 _ j
      have e2 : r.bitC σ dw (r.width σ dw) rd = r.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd r h.2 _ j
      rw [e1, e2]
  | .lor l r, h, tw, k => by
      simp only [Sk.bitC, Sk.bit]
      have e1 : l.bitC σ dw (l.width σ dw) rd = l.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd l h.1 _ j
      have e2 : r.bitC σ dw (r.width σ dw) rd = r.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd r h.2 _ j
      rw [e1, e2]
  | .tern c a b, h, tw, k => by
      simp only [Sk.bitC, Sk.bit, Sk.bitC_of_selfOk σ dw rd c h.1, Sk.bitC_of_selfOk σ dw rd a h.2.2.1,
        Sk.bitC_of_selfOk σ dw rd b h.2.2.2.1]
  | .cmp op l r, h, tw, k => by
      have hm : max (l.width σ dw) (r.width σ dw) = l.width σ dw := by
        rw [← h.2.2]; exact Nat.max_self _
      have e1 : l.bitC σ dw (l.width σ dw) rd = l.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd l h.1 _ j
      have e2 : r.bitC σ dw (l.width σ dw) rd = r.bit σ dw rd :=
        funext fun j => Sk.bitC_of_selfOk σ dw rd r h.2.1 _ j
      cases op <;> simp only [Sk.bitC, Sk.bit, hm, e1, e2]
  | .ext _, h, _, _ => by simp [Sk.SelfOk] at h
  | .add _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .sub _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .mul _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .const _, h, _, _ => by simp [Sk.SelfOk] at h
  | .cref _, h, _, _ => by simp [Sk.SelfOk] at h
  | .rsz _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .sh _ _ _ _, h, _, _ => by simp [Sk.SelfOk] at h
  | .scmp _ _ _, h, _, _ => by simp [Sk.SelfOk] at h

section widthC
variable {σ : String → Int} {dw : String → Nat}

theorem Sk.maxO_getD (a b : Option Nat) : (Sk.maxO a b).getD 0 = max (a.getD 0) (b.getD 0) := by
  cases a <;> cases b <;> simp [Sk.maxO]

/-- The rigid width of a skeleton is at most its natural width. -/
theorem Sk.rmax_le_width : ∀ (sk : Sk), (sk.rmax σ dw).getD 0 ≤ sk.width σ dw
  | .lit _ => by simp [Sk.rmax, Sk.width]
  | .rd _ => by simp [Sk.rmax, Sk.width]
  | .gate _ l r => by
      have := Sk.rmax_le_width l; have := Sk.rmax_le_width r
      simp only [Sk.rmax, Sk.width, Sk.maxO_getD]; omega
  | .cat _ => by simp [Sk.rmax, Sk.width]
  | .rep _ => by simp [Sk.rmax, Sk.width]
  | .fill _ => by simp [Sk.rmax, Sk.width]
  | .bnot a => by simpa [Sk.rmax, Sk.width] using Sk.rmax_le_width a
  | .lnot _ => by simp [Sk.rmax, Sk.width]
  | .red _ _ => by simp [Sk.rmax, Sk.width]
  | .land _ _ => by simp [Sk.rmax, Sk.width]
  | .lor _ _ => by simp [Sk.rmax, Sk.width]
  | .tern _ a b => by
      have := Sk.rmax_le_width a; have := Sk.rmax_le_width b
      simp only [Sk.rmax, Sk.width, Sk.maxO_getD]; omega
  | .cmp _ _ _ => by simp [Sk.rmax, Sk.width]
  | .ext _ => by simp [Sk.rmax, Sk.width]
  | .add l r => by
      have := Sk.rmax_le_width l; have := Sk.rmax_le_width r
      simp only [Sk.rmax, Sk.width, Sk.maxO_getD]; omega
  | .sub l r => by
      have := Sk.rmax_le_width l; have := Sk.rmax_le_width r
      simp only [Sk.rmax, Sk.width, Sk.maxO_getD]; omega
  | .mul l r => by
      have := Sk.rmax_le_width l; have := Sk.rmax_le_width r
      simp only [Sk.rmax, Sk.width, Sk.maxO_getD]; omega
  | .const _ => by simp [Sk.rmax, Sk.width]
  | .cref _ => by simp [Sk.rmax, Sk.width]
  | .rsz _ p => by simpa [Sk.rmax, Sk.width] using Sk.rmax_le_width p
  | .sh _ _ l _ => by simp [Sk.rmax, Sk.width]
  | .scmp _ _ _ => by simp [Sk.rmax, Sk.width]

/-- The truncation-marker part of the contract holds at every context at least as wide as the skeleton. -/
theorem Sk.rok_of_width : ∀ (sk : Sk) (W : Nat), sk.width σ dw ≤ W → sk.rok σ dw W
  | .lit _, _, _ => trivial
  | .rd _, _, _ => trivial
  | .gate _ l r, W, h => by
      simp only [Sk.width, Nat.max_le] at h
      exact ⟨Sk.rok_of_width l W h.1, Sk.rok_of_width r W h.2⟩
  | .cat _, _, _ => trivial
  | .rep _, _, _ => trivial
  | .fill _, _, _ => trivial
  | .bnot a, W, h => Sk.rok_of_width a W h
  | .lnot _, _, _ => trivial
  | .red _ _, _, _ => trivial
  | .land _ _, _, _ => trivial
  | .lor _ _, _, _ => trivial
  | .tern _ a b, W, h => by
      simp only [Sk.width, Nat.max_le] at h
      exact ⟨Sk.rok_of_width a W h.1, Sk.rok_of_width b W h.2⟩
  | .cmp _ _ _, _, _ => trivial
  | .ext _, _, _ => trivial
  | .add l r, W, h => by
      simp only [Sk.width, Nat.max_le] at h
      exact ⟨Sk.rok_of_width l W h.1, Sk.rok_of_width r W h.2⟩
  | .sub l r, W, h => by
      simp only [Sk.width, Nat.max_le] at h
      exact ⟨Sk.rok_of_width l W h.1, Sk.rok_of_width r W h.2⟩
  | .mul l r, W, h => by
      simp only [Sk.width, Nat.max_le] at h
      exact ⟨Sk.rok_of_width l W h.1, Sk.rok_of_width r W h.2⟩
  | .const _, _, _ => trivial
  | .cref _, _, _ => trivial
  | .sh _ _ l _, W, h => by simpa [Sk.rok, Sk.width] using h
  | .scmp _ _ _, _, _ => trivial
  | .rsz _ p, W, h => by
      have := Sk.rmax_le_width (σ := σ) (dw := dw) p
      simp only [Sk.rok, Sk.width] at h ⊢; omega

/-- **Every rigid operand fits the context**: the number `instExpr2`'s `+ -` arm compares with the context. -/
theorem Sk.rmax_le : ∀ (sk : Sk) (tw : Nat), sk.WidthOkC σ dw tw → sk.rok σ dw tw →
    (sk.rmax σ dw).getD 0 ≤ tw
  | .lit _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h]
  | .rd _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h]
  | .gate _ l r, tw, h, hr => by
      have := Sk.rmax_le l tw h.1 hr.1; have := Sk.rmax_le r tw h.2 hr.2
      simp only [Sk.rmax, Sk.maxO_getD]; omega
  | .cat _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h]
  | .rep _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h]
  | .fill _, tw, _, _ => by simp [Sk.rmax]
  | .bnot a, tw, h, hr => by simpa [Sk.rmax] using Sk.rmax_le a tw h.1 h.2
  | .lnot _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h.1]
  | .red _ _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h.1]
  | .land _ _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h.1]
  | .lor _ _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h.1]
  | .tern _ a b, tw, h, hr => by
      have := Sk.rmax_le a tw h.2.2.1 hr.1; have := Sk.rmax_le b tw h.2.2.2 hr.2
      simp only [Sk.rmax, Sk.maxO_getD]; omega
  | .cmp _ _ _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h.1]
  | .ext _, tw, h, _ => by simpa [Sk.rmax, Sk.WidthOkC] using h
  | .add l r, tw, h, hr => by
      have := Sk.rmax_le l tw h.1 hr.1; have := Sk.rmax_le r tw h.2.1 hr.2
      simp only [Sk.rmax, Sk.maxO_getD]; omega
  | .sub l r, tw, h, hr => by
      have := Sk.rmax_le l tw h.1 hr.1; have := Sk.rmax_le r tw h.2.1 hr.2
      simp only [Sk.rmax, Sk.maxO_getD]; omega
  | .mul l r, tw, h, hr => by
      have := Sk.rmax_le l tw h.1 hr.1; have := Sk.rmax_le r tw h.2.1 hr.2
      simp only [Sk.rmax, Sk.maxO_getD]; omega
  | .const _, tw, _, _ => by simp [Sk.rmax]
  | .cref _, tw, _, _ => by simp [Sk.rmax]
  | .rsz _ p, tw, _, hr => by simpa [Sk.rmax, Sk.rok] using hr
  | .sh _ _ l _, tw, _, hr => by simpa [Sk.rmax, Sk.rok] using hr
  | .scmp _ _ _, tw, h, _ => by simp only [Sk.WidthOkC] at h; simp [Sk.rmax, h.1]

/-- The natural width is as good as the context, down to the skeleton's own width. -/
theorem Sk.WidthOkC.mono : ∀ (sk : Sk) (tw W : Nat), sk.WidthOkC σ dw tw →
    sk.width σ dw ≤ W → W ≤ tw → sk.WidthOkC σ dw W
  | .lit _, tw, W, h, h1, h2 => by simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; omega
  | .rd _, tw, W, h, h1, h2 => by simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; omega
  | .gate g l r, tw, W, h, h1, h2 => by
      simp only [Sk.width, Nat.max_le] at h1
      exact ⟨Sk.WidthOkC.mono l tw W h.1 h1.1 h2, Sk.WidthOkC.mono r tw W h.2 h1.2 h2⟩
  | .cat ps, tw, W, h, h1, h2 => by simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; omega
  | .rep p, tw, W, h, h1, h2 => by simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; omega
  | .fill _, _, _, _, _, _ => trivial
  | .bnot a, tw, W, h, h1, h2 => ⟨Sk.WidthOkC.mono a tw W h.1 h1 h2, Sk.rok_of_width a W h1⟩
  | .lnot _, tw, W, h, h1, h2 => by
      simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact ⟨by omega, h.2⟩
  | .red _ _, tw, W, h, h1, h2 => by
      simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact ⟨by omega, h.2⟩
  | .land _ _, tw, W, h, h1, h2 => by
      simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact ⟨by omega, h.2⟩
  | .lor _ _, tw, W, h, h1, h2 => by
      simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact ⟨by omega, h.2⟩
  | .tern c a b, tw, W, h, h1, h2 => by
      simp only [Sk.width, Nat.max_le] at h1
      exact ⟨h.1, h.2.1, Sk.WidthOkC.mono a tw W h.2.2.1 h1.1 h2,
        Sk.WidthOkC.mono b tw W h.2.2.2 h1.2 h2⟩
  | .cmp _ _ _, tw, W, h, h1, h2 => by
      simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact ⟨by omega, h.2⟩
  | .ext _, tw, W, h, h1, h2 => by simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact h1
  | .add l r, tw, W, h, h1, h2 => by
      simp only [Sk.width, Nat.max_le] at h1
      exact ⟨Sk.WidthOkC.mono l tw W h.1 h1.1 h2, Sk.WidthOkC.mono r tw W h.2.1 h1.2 h2,
        Sk.rok_of_width l W h1.1, Sk.rok_of_width r W h1.2⟩
  | .sub l r, tw, W, h, h1, h2 => by
      simp only [Sk.width, Nat.max_le] at h1
      exact ⟨Sk.WidthOkC.mono l tw W h.1 h1.1 h2, Sk.WidthOkC.mono r tw W h.2.1 h1.2 h2,
        Sk.rok_of_width l W h1.1, Sk.rok_of_width r W h1.2⟩
  | .mul l r, tw, W, h, h1, h2 => by
      simp only [Sk.width, Nat.max_le] at h1
      exact ⟨Sk.WidthOkC.mono l tw W h.1 h1.1 h2, Sk.WidthOkC.mono r tw W h.2.1 h1.2 h2,
        Sk.rok_of_width l W h1.1, Sk.rok_of_width r W h1.2⟩
  | .const _, _, _, _, _, _ => trivial
  | .cref _, _, _, _, _, _ => trivial
  | .sh _ _ l r, tw, W, h, h1, h2 => by simp only [Sk.WidthOkC] at h ⊢; exact h
  | .scmp _ _ _, tw, W, h, h1, h2 => by
      simp only [Sk.WidthOkC, Sk.width] at h h1 ⊢; exact ⟨by omega, h.2⟩
  | .rsz pr p, tw, W, h, h1, h2 => by
      simp only [Sk.width] at h1
      cases pr
      · simp only [Sk.WidthOkC] at h ⊢; exact h
      · simp only [Sk.WidthOkC] at h ⊢
        by_cases hc : p.width σ dw < W
        · rw [if_pos hc]; rw [if_pos (by omega)] at h
          exact Sk.WidthOkC.mono p tw W h h1 h2
        · rw [if_neg hc]
          by_cases hc' : p.width σ dw < tw
          · rw [if_pos hc'] at h
            exact Sk.WidthOkC.mono p tw (p.width σ dw) h (Nat.le_refl _) (by omega)
          · rw [if_neg hc'] at h; exact h

/-- The v1 contract puts the natural width within the context. -/
theorem Sk.widthOk_width_le : ∀ (sk : Sk) (tw : Nat), sk.WidthOk σ dw tw → sk.width σ dw ≤ tw
  | .lit _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h]
  | .rd _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h]
  | .gate _ l r, tw, h => by
      have := Sk.widthOk_width_le l tw h.1; have := Sk.widthOk_width_le r tw h.2
      simp only [Sk.width]; omega
  | .cat _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h]
  | .rep _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h]
  | .fill _, tw, _ => by simp [Sk.width]
  | .bnot a, tw, h => by simpa [Sk.width] using Sk.widthOk_width_le a tw h
  | .lnot _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h.1]
  | .red _ _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h.1]
  | .land _ _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h.1]
  | .lor _ _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h.1]
  | .tern _ a b, tw, h => by
      have := Sk.widthOk_width_le a tw h.2.2.1; have := Sk.widthOk_width_le b tw h.2.2.2
      simp only [Sk.width]; omega
  | .cmp _ _ _, tw, h => by simp only [Sk.WidthOk] at h; simp [Sk.width, h.1]
  | .ext _, _, h => h.elim
  | .add _ _, _, h => h.elim
  | .sub _ _, _, h => h.elim
  | .mul _ _, _, h => h.elim
  | .const _, _, h => h.elim
  | .cref _, _, h => h.elim
  | .rsz _ _, _, h => h.elim
  | .sh _ _ _ _, _, h => h.elim
  | .scmp _ _ _, _, h => h.elim

/-- The v1 width contract implies the word-level one (it is the same on the v1 nodes, and false on the new ones). -/
theorem Sk.WidthOk.toC : ∀ (sk : Sk) (tw : Nat), sk.WidthOk σ dw tw → sk.WidthOkC σ dw tw
  | .lit _, _, h => h
  | .rd _, _, h => h
  | .gate _ l r, tw, h => ⟨Sk.WidthOk.toC l tw h.1, Sk.WidthOk.toC r tw h.2⟩
  | .cat _, _, h => h
  | .rep _, _, h => h
  | .fill _, _, h => h
  | .bnot a, tw, h => ⟨Sk.WidthOk.toC a tw h, Sk.rok_of_width a tw (Sk.widthOk_width_le a tw h)⟩
  | .lnot _, _, h => h
  | .red _ _, _, h => h
  | .land _ _, _, h => h
  | .lor _ _, _, h => h
  | .tern c a b, tw, h => ⟨h.1, h.2.1, Sk.WidthOk.toC a tw h.2.2.1, Sk.WidthOk.toC b tw h.2.2.2⟩
  | .cmp _ l r, tw, h => by
      have hm : max (l.width σ dw) (r.width σ dw) = l.width σ dw := by
        rw [← h.2.2.2]; exact Nat.max_self _
      have h1 := Sk.WidthOk.toC l _ (Sk.selfOk_widthOk σ dw l h.2.1)
      have h2 := Sk.WidthOk.toC r _ (Sk.selfOk_widthOk σ dw r h.2.2.1)
      rw [← h.2.2.2] at h2
      exact ⟨h.1, by rw [hm]; exact h1, by rw [hm]; exact h2⟩
  | .ext _, _, h => h.elim
  | .add _ _, _, h => h.elim
  | .sub _ _, _, h => h.elim
  | .mul _ _, _, h => h.elim
  | .const _, _, h => h.elim
  | .cref _, _, h => h.elim
  | .rsz _ _, _, h => h.elim
  | .sh _ _ _ _, _, h => h.elim
  | .scmp _ _ _, _, h => h.elim

end widthC

/-- A skeleton without a word-level node (`ext`, `add`, `sub`): what the v1 recognizer `rdsOf?` produces. -/
def Sk.v1 : Sk → Bool
  | .lit _ => true
  | .rd _ => true
  | .gate _ l r => l.v1 && r.v1
  | .cat _ => true
  | .rep _ => true
  | .fill _ => false
  | .bnot a => a.v1
  | .lnot a => a.v1
  | .red _ a => a.v1
  | .land l r => l.v1 && r.v1
  | .lor l r => l.v1 && r.v1
  | .tern c a b => c.v1 && a.v1 && b.v1
  | .cmp _ l r => l.v1 && r.v1
  | .ext _ => false
  | .add _ _ => false
  | .sub _ _ => false
  | .mul _ _ => false
  | .const _ => false
  | .cref _ => false
  | .rsz _ _ => false
  | .sh _ _ _ _ => false
  | .scmp _ _ _ => false

/-- A skeleton without word-level nodes that meets the contract at `tw` is self-determined, of width `tw`. -/
theorem Sk.selfOk_of_v1 {σ : String → Int} {dw : String → Nat} :
    ∀ (sk : Sk) {tw : Nat}, sk.v1 = true → sk.WidthOkC σ dw tw → sk.SelfOk σ dw ∧ sk.width σ dw = tw
  | .lit _, _, _, h => ⟨trivial, h⟩
  | .rd _, _, _, h => ⟨trivial, h⟩
  | .gate _ l r, tw, hv, h => by
      simp only [Sk.v1, Bool.and_eq_true] at hv
      obtain ⟨hl, el⟩ := Sk.selfOk_of_v1 l hv.1 h.1
      obtain ⟨hr, er⟩ := Sk.selfOk_of_v1 r hv.2 h.2
      exact ⟨⟨hl, hr, by rw [el, er]⟩, by simp only [Sk.width, el, er]; exact Nat.max_self _⟩
  | .cat _, _, _, h => ⟨trivial, h⟩
  | .rep _, _, _, h => ⟨trivial, h⟩
  | .fill _, _, hv, _ => by simp [Sk.v1] at hv
  | .bnot a, tw, hv, h => Sk.selfOk_of_v1 a hv h.1
  | .lnot _, _, _, h => ⟨h.2, h.1.symm⟩
  | .red _ _, _, _, h => ⟨h.2, h.1.symm⟩
  | .land _ _, _, _, h => ⟨⟨h.2.1, h.2.2⟩, h.1.symm⟩
  | .lor _ _, _, _, h => ⟨⟨h.2.1, h.2.2⟩, h.1.symm⟩
  | .tern c a b, tw, hv, h => by
      simp only [Sk.v1, Bool.and_eq_true] at hv
      obtain ⟨ha, ea⟩ := Sk.selfOk_of_v1 a hv.1.2 h.2.2.1
      obtain ⟨hb, eb⟩ := Sk.selfOk_of_v1 b hv.2 h.2.2.2
      exact ⟨⟨h.1, h.2.1, ha, hb, by rw [ea, eb]⟩, by simp only [Sk.width, ea, eb]; exact Nat.max_self _⟩
  | .cmp _ l r, tw, hv, h => by
      simp only [Sk.v1, Bool.and_eq_true] at hv
      obtain ⟨hl, el⟩ := Sk.selfOk_of_v1 l hv.1 h.2.1
      obtain ⟨hr, er⟩ := Sk.selfOk_of_v1 r hv.2 h.2.2
      exact ⟨⟨hl, hr, el.trans er.symm⟩, h.1.symm⟩
  | .ext _, _, hv, _ => by simp [Sk.v1] at hv
  | .add _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .sub _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .mul _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .const _, _, hv, _ => by simp [Sk.v1] at hv
  | .cref _, _, hv, _ => by simp [Sk.v1] at hv
  | .rsz _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .sh _ _ _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .scmp _ _ _, _, hv, _ => by simp [Sk.v1] at hv

/-- On a skeleton without word-level nodes the word-level contract is the v1 one. -/
theorem Sk.WidthOkC.toV1 {σ : String → Int} {dw : String → Nat} :
    ∀ (sk : Sk) {tw : Nat}, sk.v1 = true → sk.WidthOkC σ dw tw → sk.WidthOk σ dw tw
  | .lit _, _, _, h => h
  | .rd _, _, _, h => h
  | .gate _ l r, tw, hv, h => by
      simp only [Sk.v1, Bool.and_eq_true] at hv
      exact ⟨Sk.WidthOkC.toV1 l hv.1 h.1, Sk.WidthOkC.toV1 r hv.2 h.2⟩
  | .cat _, _, _, h => h
  | .rep _, _, _, h => h
  | .fill _, _, hv, _ => by simp [Sk.v1] at hv
  | .bnot a, tw, hv, h => Sk.WidthOkC.toV1 a hv h.1
  | .lnot _, _, _, h => h
  | .red _ _, _, _, h => h
  | .land _ _, _, _, h => h
  | .lor _ _, _, _, h => h
  | .tern c a b, tw, hv, h => by
      simp only [Sk.v1, Bool.and_eq_true] at hv
      exact ⟨h.1, h.2.1, Sk.WidthOkC.toV1 a hv.1.2 h.2.2.1, Sk.WidthOkC.toV1 b hv.2 h.2.2.2⟩
  | .cmp _ l r, tw, hv, h => by
      simp only [Sk.v1, Bool.and_eq_true] at hv
      obtain ⟨hl, el⟩ := Sk.selfOk_of_v1 l hv.1 h.2.1
      obtain ⟨hr, er⟩ := Sk.selfOk_of_v1 r hv.2 h.2.2
      exact ⟨h.1, hl, hr, el.trans er.symm⟩
  | .ext _, _, hv, _ => by simp [Sk.v1] at hv
  | .add _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .sub _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .mul _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .const _, _, hv, _ => by simp [Sk.v1] at hv
  | .cref _, _, hv, _ => by simp [Sk.v1] at hv
  | .rsz _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .sh _ _ _ _, _, hv, _ => by simp [Sk.v1] at hv
  | .scmp _ _ _, _, hv, _ => by simp [Sk.v1] at hv

/-- A self-determined skeleton is well formed at its own width (word-level contract). -/
theorem Sk.selfOk_widthOkC (σ : String → Int) (dw : String → Nat) (sk : Sk) (h : sk.SelfOk σ dw) :
    sk.WidthOkC σ dw (sk.width σ dw) :=
  Sk.WidthOk.toC sk _ (Sk.selfOk_widthOk σ dw sk h)

/-! ## Simp lemmas the netlist view is normalized with -/

theorem rmN_zero_zero (W : Int) : rmN W 0 0 = 0 := by simp [rmN]

theorem rmN_zero_zero_add (W : Int) (k : Nat) : rmN W 0 0 + k = k := by
  rw [rmN_zero_zero, Nat.zero_add]

theorem rmN_zero_row (W j : Int) : rmN W 0 j = j.toNat := by simp [rmN]

theorem logic_l0_beq_l1 : (Logic.l0 == Logic.l1) = false := rfl

theorem logic_l1_beq_l1 : (Logic.l1 == Logic.l1) = true := rfl

/-- A one-bit literal `1'b0` reads `false` at every position (position `0`: the bit; beyond: absent,
so `x`, which is not a definite `1`). -/
theorem lvec_boolAt_l0 (j : Nat) : (LVec.mk #[Logic.l0]).boolAt j = false := by
  cases j <;> simp [LVec.boolAt]

theorem lvec_width_l0 : (LVec.mk #[Logic.l0]).width = 1 := rfl

theorem lvec_boolAt_l1_zero : (LVec.mk #[Logic.l1]).boolAt 0 = true := by
  simp [LVec.boolAt]

/-! ## The template side: leaf counts and leaves -/

theorem rdsOf?_len {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true → rs.length = cnt v
  | .lit _, rs, h, _ => by simp [rdsOf?] at h; subst h; simp [cnt]
  | .binary op l r, rs, h, hf => by
      simp only [fragG, Bool.and_eq_true] at hf
      obtain ⟨-, ra, rb, hl, hr, rfl⟩ := rdsOf?_binary h
      simp [cnt, rdsOf?_len l ra hl hf.1, rdsOf?_len r rb hr hf.2]
  | .unary op a, rs, h, hf => by
      obtain ⟨-, ha⟩ := rdsOf?_unary h
      simp only [fragG] at hf
      simp [cnt, rdsOf?_len a rs ha hf]
  | .ternary c t e, rs, h, hf => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOf?_ternary h
      simp only [fragG, Bool.and_eq_true] at hf
      simp [cnt, rdsOf?_len c rc hc hf.1.1, rdsOf?_len t rt ht hf.1.2, rdsOf?_len e re he hf.2,
        Nat.add_assoc]
  | .reduce op a, rs, h, hf => by
      simp only [fragG] at hf
      simp [cnt, rdsOf?_len a rs (rdsOf?_reduce h) hf]
  | .ident n, rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h; subst h; simp [cnt]
  | .bitSel b i, rs, h, _ => by
      have h' : rdsLeaf? ds (.bitSel b i) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.bitSel b i) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [cnt]
  | .partSel b pm pl, rs, h, _ => by
      have h' : rdsLeaf? ds (.partSel b pm pl) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.partSel b pm pl) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [cnt]
  | .arrayElem n is, rs, h, _ => by
      have h' : rdsLeaf? ds (.arrayElem n is) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.arrayElem n is) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [cnt]
  | .arrayPart n is m a b, rs, h, _ => by
      have h' : rdsLeaf? ds (.arrayPart n is m a b) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.arrayPart n is m a b) with m' | a'
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [cnt]
  | .concat _, _, _, hf => by simp [fragG] at hf
  | .fill _, _, _, hf => by simp [fragG] at hf
  | .paramRef .., rs, h, _ | .genvarRef .., rs, h, _ | .enumRef .., rs, h, _
  | .int .., rs, h, _
  | .resize .., rs, h, _ | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _ | .repl .., rs, h, _
  | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-- On an accepted expression the skeleton's leaves are exactly the reads. -/
theorem skT_leaves {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (skT v rs).leaves = rs
  | .lit _, rs, h, _ => by simp [rdsOf?] at h; subst h; simp [skT, Sk.leaves]
  | .binary op l r, rs, h, hf => by
      simp only [fragG, Bool.and_eq_true] at hf
      obtain ⟨hb, ra, rb, hl, hr, rfl⟩ := rdsOf?_binary h
      have hla := rdsOf?_len l ra hl hf.1
      have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
      have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
      have ihl := skT_leaves l ra hl hf.1
      have ihr := skT_leaves r rb hr hf.2
      rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [skT, gateOf, mkGate, e1, e2, Sk.leaves, ihl, ihr]
  | .unary op a, rs, h, hf => by
      obtain ⟨hop, ha⟩ := rdsOf?_unary h
      simp only [fragG] at hf
      have ih := skT_leaves a rs ha hf
      rcases hop with rfl | rfl <;> simp [skT, Sk.leaves, ih]
  | .ternary c t e, rs, h, hf => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOf?_ternary h
      simp only [fragG, Bool.and_eq_true] at hf
      have hc' := rdsOf?_len c rc hc hf.1.1
      have ht' := rdsOf?_len t rt ht hf.1.2
      have e1 : (rc ++ rt ++ re).take (cnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ re).drop (cnt c) = rt ++ re := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ re).take (cnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ re).drop (cnt t) = re := List.drop_left' ht'
      simp only [skT, e1, e2, e3, e4, Sk.leaves, skT_leaves c rc hc hf.1.1, skT_leaves t rt ht hf.1.2,
        skT_leaves e re he hf.2]
  | .reduce op a, rs, h, hf => by
      simp only [fragG] at hf
      simp [skT, Sk.leaves, skT_leaves a rs (rdsOf?_reduce h) hf]
  | .ident n, rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h; subst h; simp [skT, Sk.leaves]
  | .bitSel b i, rs, h, _ => by
      have h' : rdsLeaf? ds (.bitSel b i) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.bitSel b i) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.leaves]
  | .partSel b pm pl, rs, h, _ => by
      have h' : rdsLeaf? ds (.partSel b pm pl) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.partSel b pm pl) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.leaves]
  | .arrayElem n is, rs, h, _ => by
      have h' : rdsLeaf? ds (.arrayElem n is) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.arrayElem n is) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.leaves]
  | .arrayPart n is m a b, rs, h, _ => by
      have h' : rdsLeaf? ds (.arrayPart n is m a b) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.arrayPart n is m a b) with m' | a'
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.leaves]
  | .concat _, _, _, hf => by simp [fragG] at hf
  | .fill _, _, _, hf => by simp [fragG] at hf
  | .paramRef .., rs, h, _ | .genvarRef .., rs, h, _ | .enumRef .., rs, h, _
  | .int .., rs, h, _
  | .resize .., rs, h, _ | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _ | .repl .., rs, h, _
  | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h


/-- **The skeleton of an expression the v1 recognizer accepts has no word-level node**, whatever accesses it is
given. -/
theorem skT_v1 {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc) (as : List Acc), rdsOf? ds v = .ok rs → (skT v as).v1 = true
  | .lit _, rs, as, h => by simp [skT, Sk.v1]
  | .binary op l r, rs, as, h => by
      obtain ⟨hb, ra, rb, hl, hr, rfl⟩ := rdsOf?_binary h
      have h1 := skT_v1 l ra (as.take (cnt l)) hl
      have h2 := skT_v1 r rb (as.drop (cnt l)) hr
      rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [skT, gateOf, mkGate, Sk.v1, h1, h2]
  | .unary op a, rs, as, h => by
      obtain ⟨hop, ha⟩ := rdsOf?_unary h
      have h1 := skT_v1 a rs as ha
      rcases hop with rfl | rfl <;> simp [skT, Sk.v1, h1]
  | .ternary c t e, rs, as, h => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOf?_ternary h
      have h1 := skT_v1 c rc (as.take (cnt c)) hc
      have h2 := skT_v1 t rt ((as.drop (cnt c)).take (cnt t)) ht
      have h3 := skT_v1 e re ((as.drop (cnt c)).drop (cnt t)) he
      simp only [skT, Sk.v1, Bool.and_eq_true]
      exact ⟨⟨h1, h2⟩, h3⟩
  | .reduce op a, rs, as, h => by
      simp [skT, Sk.v1, skT_v1 a rs as (rdsOf?_reduce h)]
  | .concat _, _, _, _ => by simp [skT, Sk.v1]
  | .ident _, _, _, _ => by simp [skT, Sk.v1]
  | .bitSel _ _, _, _, _ => by simp [skT, Sk.v1]
  | .partSel _ _ _, _, _, _ => by simp [skT, Sk.v1]
  | .arrayElem _ _, _, _, _ => by simp [skT, Sk.v1]
  | .arrayPart .., _, _, _ => by simp [skT, Sk.v1]
  | .paramRef .., rs, _, h | .genvarRef .., rs, _, h | .enumRef .., rs, _, h
  | .int .., rs, _, h | .fill .., rs, _, h
  | .resize .., rs, _, h | .signedResize .., rs, _, h | .squash2 .., rs, _, h
  | .sysCall .., rs, _, h | .repl .., rs, _, h
  | .cast .., rs, _, h | .unsupported .., rs, _, h => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-! ## The template side of the word-level recognizer (WP-B2) -/

theorem rdsLeaf_ok {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : rdsLeaf? ds e = .ok rs) :
    ∃ a, rs = [a] := by
  unfold rdsLeaf? at h
  rcases hl : leafRd? ds e with m | a
  · simp [hl] at h
  · simp only [hl, Except.ok.injEq] at h
    exact ⟨a, h.symm⟩

theorem cnt_resize_op {e : PExpr} (m : Nat) (hop : e.isOpW = true) : cnt (.resize m e) = cnt e := by
  cases e <;> simp [PExpr.isOpW, cnt] at hop ⊢

/-- A marker around an accepted operation: the node carries the operand's `ctxPropagates`. -/
theorem skT_resize_op {ds : List DeclT} {e : PExpr} {rs : List Acc} (m : Nat) (as : List Acc)
    (h : rdsOfW? ds e = .ok rs) (hop : e.isOpW = true) :
    skT (.resize m e) as = .rsz e.ctxPropagates (skT e as) := by
  cases e with
  | binary op l r =>
      rcases rdsOfW?_binary h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨cm, a, b, hcm, -, -, -, -, -⟩
      · rcases ctxOpW_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | ⟨cm, rfl⟩ <;> (try cases cm) <;>
          simp [skT, gateOf, mkGate, CmpOp.ex, PExpr.ctxPropagates]
      · rcases selfOpW_cases hb with rfl | rfl <;> simp [skT, gateOf, PExpr.ctxPropagates]
      · rcases shOpW_cases hb with ⟨s, rfl⟩ | rfl <;> (try cases s) <;> simp [skT, gateOf, PExpr.ctxPropagates]
      · cases op <;> simp [scmpOp?] at hcm <;> simp [skT, gateOf, PExpr.ctxPropagates]
  | unary op a =>
      rcases rdsOfW?_unary h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [skT, PExpr.ctxPropagates]
  | ternary c t f => simp [skT, PExpr.ctxPropagates]
  | reduce op a => simp [skT, PExpr.ctxPropagates]
  | int v => simp [skT, PExpr.ctxPropagates]
  | concat ps => simp [skT, PExpr.ctxPropagates]
  | _ => simp [PExpr.isOpW] at hop

/-- A shift operand consumes the reads it has. -/
theorem shOpd_len {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shOpdRd? ds e = .ok rs) :
    rs.length = cnt e := by
  rcases shOpdRd?_cases h with ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨a, hl, rfl⟩
  · simp [cnt]
  · simp [cnt]
  · rcases leafKind_of_leafRd hl with ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m, a', b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
      simp [cnt]

/-- The amount of a shift: a genvar (a constant, no access) or a shift operand. -/
theorem shAmt_len {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shAmtRd? ds e = .ok rs) :
    rs.length = cnt e := by
  rcases shAmtRd?_cases h with ⟨g, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | h'
  · simp [cnt]
  · simp [cnt]
  · exact shOpd_len h'

theorem shLeft_len {ds : List DeclT} {s : Bool} {l : PExpr} {rs : List Acc} (h : shLeftRd? ds s l = .ok rs) :
    rs.length = cnt l := by
  obtain ⟨x, hx, hxo⟩ := shLeftRd?_cases h
  have h1 := shOpd_len hxo
  rcases hx with rfl | ⟨-, m, rfl⟩ | ⟨-, m, rfl⟩
  · exact h1
  · rcases shOpdKind hxo with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m', a, b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
      simpa [cnt] using h1
  · rcases shOpdKind hxo with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m', a, b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
      simpa [cnt] using h1

/-- **The skeleton of a recognized shift**: `skT` strips the marker from the left operand (it is transparent) and builds
`Sk.sh`; the signedness flag of the skeleton is the one of the operator. -/
theorem skT_sh {ds : List DeclT} {op : SymBinOp} {l r : PExpr} {ra rb : List Acc} (hb : shOpW op = true)
    (hl : shLeftRd? ds (shSign op) l = .ok ra) (hr : shAmtRd? ds r = .ok rb) :
    ∃ (d sg : Bool) (x : PExpr),
      ((op = .m0 (.shl sg) ∧ d = true) ∨ (op = .m0 (.shr false) ∧ d = false ∧ sg = false)) ∧
      shOpdRd? ds x = .ok ra ∧
      (l = x ∨ (sg = false ∧ ∃ m, l = .resize m x) ∨ (sg = true ∧ ∃ m, l = .signedResize m x)) ∧
      skT (.binary op l r) (ra ++ rb) = .sh d sg (skT x ra) (skT r rb) := by
  rcases shOpW_cases hb with ⟨s, rfl⟩ | rfl
  · have hl' : shLeftRd? ds s l = .ok ra := hl
    obtain ⟨x, hx, hxo⟩ := shLeftRd?_cases hl'
    have hla := shLeft_len hl'
    have e1 := List.take_left' hla (l₂ := rb)
    have e2 := List.drop_left' hla (l₂ := rb)
    rcases hx with h | ⟨hs, m, h⟩ | ⟨hs, m, h⟩
    · subst h
      cases s
      · rcases shOpdKind hxo with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ |
            ⟨n, is, m, a, b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
          exact ⟨true, false, _, Or.inl ⟨rfl, rfl⟩, hxo, Or.inl rfl, by simp [skT, gateOf, e1, e2]⟩
      · rcases shOpdKind hxo with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ |
            ⟨n, is, m, a, b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
          exact ⟨true, true, _, Or.inl ⟨rfl, rfl⟩, hxo, Or.inl rfl, by simp [skT, gateOf, e1, e2]⟩
    · subst hs; subst h
      exact ⟨true, false, _, Or.inl ⟨rfl, rfl⟩, hxo, Or.inr (Or.inl ⟨rfl, m, rfl⟩), by simp [skT, gateOf, e1, e2]⟩
    · subst hs; subst h
      exact ⟨true, true, _, Or.inl ⟨rfl, rfl⟩, hxo, Or.inr (Or.inr ⟨rfl, m, rfl⟩), by simp [skT, gateOf, e1, e2]⟩
  · have hl' : shLeftRd? ds false l = .ok ra := hl
    obtain ⟨x, hx, hxo⟩ := shLeftRd?_cases hl'
    have hla := shLeft_len hl'
    have e1 := List.take_left' hla (l₂ := rb)
    have e2 := List.drop_left' hla (l₂ := rb)
    rcases hx with h | ⟨-, m, h⟩ | ⟨hs, m, h⟩
    · subst h
      rcases shOpdKind hxo with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ |
          ⟨n, is, m, a, b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
        exact ⟨false, false, _, Or.inr ⟨rfl, rfl, rfl⟩, hxo, Or.inl rfl, by simp [skT, gateOf, e1, e2]⟩
    · subst h
      exact ⟨false, false, _, Or.inr ⟨rfl, rfl, rfl⟩, hxo, Or.inr (Or.inl ⟨rfl, m, rfl⟩),
        by simp [skT, gateOf, e1, e2]⟩
    · exact absurd hs (by simp)

theorem shOpd_leaves {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shOpdRd? ds e = .ok rs) :
    (skT e rs).leaves = rs := by
  rcases shOpdRd?_cases h with ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨a, hl, rfl⟩
  · simp [skT, Sk.leaves]
  · simp [skT, Sk.leaves]
  · rcases leafKind_of_leafRd hl with ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m, a', b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
      simp [skT, Sk.leaves]

theorem shAmt_leaves {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shAmtRd? ds e = .ok rs) :
    (skT e rs).leaves = rs := by
  rcases shAmtRd?_cases h with ⟨g, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | h'
  · simp [skT, Sk.leaves]
  · simp [skT, Sk.leaves]
  · exact shOpd_leaves h'

/-! ### Concatenation operands (WP-B2 gate 3b): the helper lemmas of the parts -/

theorem rdsLeaf_cases {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (h : rdsLeaf? ds e = .ok rs) : ∃ a, leafRd? ds e = .ok a ∧ rs = [a] := by
  unfold rdsLeaf? at h
  rcases hl : leafRd? ds e with m | a
  · simp [hl] at h
  · simp only [hl, Except.ok.injEq] at h
    exact ⟨a, rfl, h.symm⟩

theorem partRd?_of_ne {ds : List DeclT} {p : PExpr} (hp : ∀ v, p ≠ .lit v) :
    partRd? ds p = rdsLeaf? ds p := by
  cases p <;> first | rfl | exact absurd rfl (hp _)

theorem partsT_lit (v : LVec) (ps : List PExpr) (as : List Acc) :
    partsT (.lit v :: ps) as = .lit v :: partsT ps as := rfl

theorem partsT_of_ne {p : PExpr} (hp : ∀ v, p ≠ .lit v) (hr : ∀ c a, p ≠ .repl c a) (ps : List PExpr)
    (as : List Acc) :
    partsT (p :: ps) as = .rd (as.headD (.whole "")) :: partsT ps (as.drop 1) := by
  cases p <;> first | rfl | exact absurd rfl (hp _) | exact absurd rfl (hr _ _)

theorem partsT_repl_lit (c : PExpr) (v : LVec) (ps : List PExpr) (as : List Acc) :
    partsT (.repl c (.concat [.lit v]) :: ps) as = .replit (repAff c) v :: partsT ps as := rfl

theorem partsT_repl_ne (c : PExpr) {e : PExpr} (he : ∀ v, e ≠ .lit v) (ps : List PExpr) (as : List Acc) :
    partsT (.repl c (.concat [e]) :: ps) as = .reprd (repAff c) (as.headD (.whole "")) :: partsT ps (as.drop 1) := by
  cases e <;> first | rfl | exact absurd rfl (he _)

theorem cnt_repl_ne (c : PExpr) {e : PExpr} (he : ∀ v, e ≠ .lit v) : cnt (.repl c (.concat [e])) = 1 := by
  cases e <;> first | rfl | exact absurd rfl (he _)

theorem pcnt_repl_ne (c : PExpr) {e : PExpr} (he : ∀ v, e ≠ .lit v) :
    (match PExpr.repl c (.concat [e]) with | .lit _ => 0 | .repl _ (.concat [.lit _]) => 0 | _ => 1) = 1 := by
  cases e <;> first | rfl | exact absurd rfl (he _)

theorem partRdW?_of_ne {ds : List DeclT} {p : PExpr} (hp : ∀ v, p ≠ .lit v) (hr : ∀ c a, p ≠ .repl c a) :
    partRdW? ds p = rdsLeaf? ds p := by
  cases p <;> first | rfl | exact absurd rfl (hp _) | exact absurd rfl (hr _ _)

theorem partsT_leaves {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRd? ds ps = .ok rs →
      partLeaves (partsT ps rs) = rs
  | [], rs, h => by
      simp only [partsRd?, Except.ok.injEq] at h
      subst h
      simp [partsT, partLeaves]
  | p :: ps, rs, h => by
      simp only [partsRd?] at h
      rcases hp : partRd? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRd? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          by_cases hpl : ∃ v, p = .lit v
          · obtain ⟨v, rfl⟩ := hpl
            have hra : ra = [] := by simpa [partRd?] using hp.symm
            subst hra
            simp only [List.nil_append]
            rw [partsT_lit]
            simp [partLeaves, partsT_leaves ps rb hq]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            rw [partRd?_of_ne hnl] at hp
            obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
            rw [partsT_of_ne hnl (rdsLeaf_ne_repl hp)]
            simp [partLeaves, partsT_leaves ps rb hq]

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
            have hnr := rdsLeaf_ne_repl hp
            have hp1 : (match p with | .lit _ => 0 | .repl _ (.concat [.lit _]) => 0 | _ => 1) = 1 := by
              cases p <;> first | rfl | exact absurd rfl (hnl _) | exact absurd rfl (hnr _ _)
            simp [pcnt, hp1, ih, Nat.add_comm]

/-- The word-level parts (literals, accesses, replications) take the accesses of their skeleton. -/
theorem partsT_leavesW {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds ps = .ok rs →
      partLeaves (partsT ps rs) = rs
  | [], rs, h => by
      simp only [partsRdW?, Except.ok.injEq] at h
      subst h
      simp [partsT, partLeaves]
  | p :: ps, rs, h => by
      simp only [partsRdW?] at h
      rcases hp : partRdW? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRdW? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          by_cases hpl : ∃ v, p = .lit v
          · obtain ⟨v, rfl⟩ := hpl
            have hra : ra = [] := by simpa [partRdW?] using hp.symm
            subst hra
            simp only [List.nil_append]
            rw [partsT_lit]
            simp [partLeaves, partsT_leavesW ps rb hq]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            by_cases hpr : ∃ c a, p = .repl c a
            · obtain ⟨c, a, rfl⟩ := hpr
              obtain ⟨k, hk, harg⟩ := repRd?_cases hp
              rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, hnl', -⟩
              · simp only [List.nil_append]
                rw [partsT_repl_lit]
                simp [partLeaves, partsT_leavesW ps rb hq]
              · obtain ⟨x, -, rfl⟩ := rdsLeaf_cases hl
                rw [partsT_repl_ne c hnl']
                simp [partLeaves, partsT_leavesW ps rb hq]
            · have hnr : ∀ c a, p ≠ .repl c a := fun c a h => hpr ⟨c, a, h⟩
              rw [partRdW?_of_ne hnl hnr] at hp
              obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
              rw [partsT_of_ne hnl hnr]
              simp [partLeaves, partsT_leavesW ps rb hq]

theorem partsRdW_len {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds ps = .ok rs → rs.length = pcnt ps
  | [], rs, h => by simp [partsRdW?] at h; subst h; simp [pcnt]
  | p :: ps, rs, h => by
      simp only [partsRdW?] at h
      rcases hp : partRdW? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRdW? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          have ih := partsRdW_len ps rb hq
          by_cases hpl : ∃ v, p = .lit v
          · obtain ⟨v, rfl⟩ := hpl
            have hra : ra = [] := by simpa [partRdW?] using hp.symm
            subst hra
            simp [pcnt, ih]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            by_cases hpr : ∃ c a, p = .repl c a
            · obtain ⟨c, a, rfl⟩ := hpr
              obtain ⟨k, hk, harg⟩ := repRd?_cases hp
              rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, hnl', -⟩
              · simp [pcnt, ih]
              · obtain ⟨x, -, rfl⟩ := rdsLeaf_cases hl
                have hp1 := pcnt_repl_ne c hnl'
                simp [pcnt, hp1, ih, Nat.add_comm]
            · have hnr : ∀ c a, p ≠ .repl c a := fun c a h => hpr ⟨c, a, h⟩
              rw [partRdW?_of_ne hnl hnr] at hp
              obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
              have hp1 : (match p with | .lit _ => 0 | .repl _ (.concat [.lit _]) => 0 | _ => 1) = 1 := by
                cases p <;> first | rfl | exact absurd rfl (hnl _) | exact absurd rfl (hnr _ _)
              simp [pcnt, hp1, ih, Nat.add_comm]

theorem rdsOfW?_len {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfW? ds v = .ok rs → fragW v = true → rs.length = cnt v
  | .lit _, rs, h, _ => by simp [rdsOfW?] at h; subst h; simp [cnt]
  | .binary op l r, rs, h, hf => by
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ |
        ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨cm, a, b, -, rfl, rfl, -, -, rfl⟩
      · replace hf := fragW_bin_ctx (selfOpW_false_of_ctx hb) hf
        simp [cnt, rdsOfW?_len l ra hl hf.1, rdsOfW?_len r rb hr hf.2]
      · replace hf := fragW_bin_self hb hf
        simp [cnt, rdsOf?_len l ra hl hf.1, rdsOf?_len r rb hr hf.2]
      · simp [cnt, shLeft_len hl, shAmt_len hr]
      · simp [cnt]
  | .unary op a, rs, h, hf => by
      rcases rdsOfW?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · replace hf : fragW a = true := by simpa [fragW] using hf
        simp [cnt, rdsOfW?_len a rs ha hf]
      · replace hf : fragG a = true := by simpa [fragW] using hf
        simp [cnt, rdsOf?_len a rs ha hf]
  | .ternary c t e, rs, h, hf => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOfW?_ternary h
      simp only [fragW, Bool.and_eq_true] at hf
      simp [cnt, rdsOf?_len c rc hc hf.1.1, rdsOfW?_len t rt ht hf.1.2, rdsOfW?_len e re he hf.2,
        Nat.add_assoc]
  | .reduce op a, rs, h, hf => by
      simp only [fragW] at hf
      simp [cnt, rdsOf?_len a rs (rdsOfW?_reduce h) hf]
  | .resize m e, rs, h, hf => by
      rcases rdsOfW?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, hl, rfl⟩ | ⟨hop, hr⟩
      · simp [cnt]
      · cases e <;> first | exact absurd rfl (hn _) | (simp [leafRd?] at hl; done) | simp [cnt]
      · rw [cnt_resize_op m hop]
        exact rdsOfW?_len e rs hr (by simpa [fragW] using hf)
  | .int _, rs, h, _ => by simp [rdsOfW?] at h; subst h; simp [cnt]
  | .ident n, rs, h, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h; subst h; simp [cnt]
  | .bitSel b i, rs, h, _ => by
      obtain ⟨a, rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [cnt]
  | .partSel b pm pl, rs, h, _ => by
      obtain ⟨a, rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [cnt]
  | .arrayElem n is, rs, h, _ => by
      obtain ⟨a, rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [cnt]
  | .arrayPart n is m a b, rs, h, _ => by
      obtain ⟨a', rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [cnt]
  | .concat ps, rs, h, _ => by
      have h' : partsRdW? ds ps = .ok rs := by simpa [rdsOfW?] using h
      simpa [cnt] using partsRdW_len ps rs h'
  | .repl c a, rs, h, _ => by
      have h' : repRd? ds c a = .ok rs := by simpa [rdsOfW?] using h
      obtain ⟨k, hk, harg⟩ := repRd?_cases h'
      rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, hnl', -⟩
      · simp [cnt]
      · obtain ⟨x, -, rfl⟩ := rdsLeaf_cases hl
        simp [cnt_repl_ne c hnl']
  | .fill _, _, _, hf => by simp [fragW] at hf
  | .paramRef .., rs, h, _ | .genvarRef .., rs, h, _ | .enumRef .., rs, h, _
  | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _
  | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h

/-- On an accepted expression the skeleton's leaves are exactly the reads. -/
theorem skT_leavesW {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfW? ds v = .ok rs → fragW v = true →
      (skT v rs).leaves = rs
  | .lit _, rs, h, _ => by simp [rdsOfW?] at h; subst h; simp [skT, Sk.leaves]
  | .binary op l r, rs, h, hf => by
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ |
        ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨cm, a, b, hcm, rfl, rfl, -, -, rfl⟩
      · replace hf := fragW_bin_ctx (selfOpW_false_of_ctx hb) hf
        have hla := rdsOfW?_len l ra hl hf.1
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have ihl := skT_leavesW l ra hl hf.1
        have ihr := skT_leavesW r rb hr hf.2
        rcases ctxOpW_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | ⟨cm, rfl⟩ <;> (try cases cm) <;>
          simp [skT, gateOf, mkGate, CmpOp.ex, e1, e2, Sk.leaves, ihl, ihr]
      · replace hf := fragW_bin_self hb hf
        have hla := rdsOf?_len l ra hl hf.1
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have ihl := skT_leaves l ra hl hf.1
        have ihr := skT_leaves r rb hr hf.2
        rcases selfOpW_cases hb with rfl | rfl <;>
          simp [skT, gateOf, mkGate, e1, e2, Sk.leaves, ihl, ihr]
      · -- a run-time shift: the operand is a literal, a constant or one access, bare or under the marker
        obtain ⟨d, sg, x, -, hxo, -, hsk⟩ := skT_sh hb hl hr
        rw [hsk]
        simp [Sk.leaves, shOpd_leaves hxo, shAmt_leaves hr]
      · -- a signed comparison of two signed signals
        cases op <;> simp [scmpOp?] at hcm <;> simp [skT, gateOf, Sk.leaves]
  | .unary op a, rs, h, hf => by
      rcases rdsOfW?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · replace hf : fragW a = true := by simpa [fragW] using hf
        simp [skT, Sk.leaves, skT_leavesW a rs ha hf]
      · replace hf : fragG a = true := by simpa [fragW] using hf
        simp [skT, Sk.leaves, skT_leaves a rs ha hf]
  | .ternary c t e, rs, h, hf => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOfW?_ternary h
      simp only [fragW, Bool.and_eq_true] at hf
      have hc' := rdsOf?_len c rc hc hf.1.1
      have ht' := rdsOfW?_len t rt ht hf.1.2
      have e1 : (rc ++ rt ++ re).take (cnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ re).drop (cnt c) = rt ++ re := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ re).take (cnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ re).drop (cnt t) = re := List.drop_left' ht'
      simp only [skT, e1, e2, e3, e4, Sk.leaves, skT_leaves c rc hc hf.1.1, skT_leavesW t rt ht hf.1.2,
        skT_leavesW e re he hf.2]
  | .reduce op a, rs, h, hf => by
      simp only [fragW] at hf
      simp [skT, Sk.leaves, skT_leaves a rs (rdsOfW?_reduce h) hf]
  | .resize m e, rs, h, hf => by
      rcases rdsOfW?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, hl, rfl⟩ | ⟨hop, hr⟩
      · simp [skT, Sk.leaves, partLeaves]
      · cases e <;> first | exact absurd rfl (hn _) | (simp [leafRd?] at hl; done) | simp [skT, Sk.leaves, partLeaves]
      · rw [skT_resize_op m rs hr hop]
        simpa [Sk.leaves] using skT_leavesW e rs hr (by simpa [fragW] using hf)
  | .int _, rs, h, _ => by simp [rdsOfW?] at h; subst h; simp [skT, Sk.leaves]
  | .ident n, rs, h, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h; subst h; simp [skT, Sk.leaves]
  | .bitSel b i, rs, h, _ => by
      obtain ⟨a, rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [skT, Sk.leaves]
  | .partSel b pm pl, rs, h, _ => by
      obtain ⟨a, rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [skT, Sk.leaves]
  | .arrayElem n is, rs, h, _ => by
      obtain ⟨a, rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [skT, Sk.leaves]
  | .arrayPart n is m a b, rs, h, _ => by
      obtain ⟨a', rfl⟩ := rdsLeaf_ok (by simpa [rdsOfW?] using h)
      simp [skT, Sk.leaves]
  | .concat ps, rs, h, _ => by
      have h' : partsRdW? ds ps = .ok rs := by simpa [rdsOfW?] using h
      simpa [skT, Sk.leaves] using partsT_leavesW ps rs h'
  | .repl c a, rs, h, _ => by
      have h' : repRd? ds c a = .ok rs := by simpa [rdsOfW?] using h
      obtain ⟨k, hk, harg⟩ := repRd?_cases h'
      rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, hnl', -⟩
      · simp [skT, Sk.leaves, partLeaves]
      · obtain ⟨x, -, rfl⟩ := rdsLeaf_cases hl
        have : skT (.repl c (.concat [e])) [x] = .rep (.reprd (repAff c) x) := by
          cases e <;> first | rfl | exact absurd rfl (hnl' _)
        simp [this, Sk.leaves, partLeaves]
  | .fill _, _, _, hf => by simp [fragW] at hf
  | .paramRef .., rs, h, _ | .genvarRef .., rs, h, _ | .enumRef .., rs, h, _
  | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _
  | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h

end CombEq
end LeanModels.Sv
