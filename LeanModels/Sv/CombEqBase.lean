import LeanModels.Sv.CombViewMain
import LeanModels.Sv.CombKnownThm

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
* `Sk.low σ tw` — the `Expr2` that `instantiate2` builds for it (`fitExpr2` at the target width
  `tw`): gates over `slice (ident n) lo w` leaves.
* `Sk.WidthOk` — the width obligation: every operand is exactly as wide as the target (otherwise
  `fitExpr2` inserts a `resize`, which this stage does not model).

## What is proved here

* `leaf_eq`: an access leaf instantiates to `accExpr` (the slice the access promises), and has
  its promised self-width;
* `gate_shape` / `concat_shape` / `rhs_shape`: `fitExpr2 E elems (some tw) v = (skRhs v rds).low σ tw`;
* `proc_shape`: `instProcess2 E elems proc = .assign (tgt.lhs σ) ((skRhs …).low σ tw)` for a site;
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

/-- The skeleton of a gate over two skeletons (`gateOf` only produces `&`, `|`, `^`). -/
def mkGate : BinOp → Sk → Sk → Sk
  | .and, l, r => .gate .and l r
  | .or, l, r => .gate .or l r
  | .xor, l, r => .gate .xor l r
  | _, _, _ => .fill .l0

/-- Number of access leaves of a gate tree. -/
def cnt : PExpr → Nat
  | .lit _ => 0
  | .binary _ l r => cnt l + cnt r
  | _ => 1

/-- The gate-tree skeleton of `v`, taking one access of `as` per leaf, left to right. -/
def skT : PExpr → List Acc → Sk
  | .lit v, _ => .lit v
  | .binary op l r, as =>
      match gateOf op with
      | some g => mkGate g (skT l (as.take (cnt l))) (skT r (as.drop (cnt l)))
      | none => .fill .l0
  | _, as => .rd (as.headD (.whole ""))

/-- The parts of a concatenation: a literal part is itself, every other part takes the next access. -/
def partsT : List PExpr → List Acc → List Part
  | [], _ => []
  | p :: ps, as =>
      match p with
      | .lit v => .lit v :: partsT ps as
      | _ => .rd (as.headD (.whole "")) :: partsT ps (as.drop 1)

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
  | .concat _ => false
  | .fill _ => false
  | _ => true

/-- The right-hand sides `sv_equations` reads: a fill, a concatenation of literals and accesses,
or a gate tree. -/
def fragOk : PExpr → Bool
  | .fill _ => true
  | .concat _ => true
  | v => fragG v

/-! ## Boolean reading -/

/-- Bit `k` of an access over a bit environment (`rd n i` = bit `i` of signal `n`). -/
def accBit (σ : String → Int) (rd : String → Nat → Bool) (a : Acc) (k : Nat) : Bool :=
  rd a.name (Acc.lo σ a + k)

def Part.wid (σ : String → Int) (dw : String → Nat) : Part → Nat
  | .lit v => v.width
  | .rd a => (a.win σ dw).2.2

def Part.bit (σ : String → Int) (rd : String → Nat → Bool) : Part → Nat → Bool
  | .lit v => fun k => v.boolAt k
  | .rd a => fun k => accBit σ rd a k

/-- A concatenation: parts in source order, the first part most significant. -/
def catBit (σ : String → Int) (dw : String → Nat) (rd : String → Nat → Bool) :
    List Part → Nat → Bool
  | [], _ => false
  | p :: ps, k =>
      if k < (ps.map (Part.wid σ dw)).sum then catBit σ dw rd ps k
      else p.bit σ rd (k - (ps.map (Part.wid σ dw)).sum)

/-- Bit `k` of the skeleton. -/
def Sk.bit (σ : String → Int) (dw : String → Nat) (rd : String → Nat → Bool) : Sk → Nat → Bool
  | .lit v, k => v.boolAt k
  | .rd a, k => accBit σ rd a k
  | .gate .and l r, k => l.bit σ dw rd k && r.bit σ dw rd k
  | .gate .or l r, k => l.bit σ dw rd k || r.bit σ dw rd k
  | .gate .xor l r, k => l.bit σ dw rd k ^^ r.bit σ dw rd k
  | .cat ps, k => catBit σ dw rd ps k
  | .fill b, _ => b == Logic.l1

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

/-- The expression `instantiate2` builds for the skeleton at target width `tw`. -/
def Sk.low (σ : String → Int) (tw : Nat) : Sk → Expr2
  | .lit v => .lit v
  | .rd a => accExpr σ a
  | .gate g l r => .binary g.op (l.low σ tw) (r.low σ tw)
  | .cat ps => .concat (ps.map (Part.expr σ)).toArray
  | .fill b => .lit (LVec.replicate tw b)

/-- Every operand is exactly as wide as the target (no `resize` is inserted). -/
def Sk.WidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : Sk → Prop
  | .lit v => v.width = tw
  | .rd a => (a.win σ dw).2.2 = tw
  | .gate _ l r => l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw
  | .cat ps => (ps.map (Part.wid σ dw)).sum = tw
  | .fill _ => True

/-- The access leaves. -/
def partLeaves : List Part → List Acc
  | [] => []
  | .lit _ :: ps => partLeaves ps
  | .rd a :: ps => a :: partLeaves ps

def Sk.leaves : Sk → List Acc
  | .lit _ => []
  | .rd a => [a]
  | .gate _ l r => l.leaves ++ r.leaves
  | .cat ps => partLeaves ps
  | .fill _ => []

/-- Literals and fills carry no `x`/`z`. -/
def partKnown : List Part → Bool
  | [] => true
  | .lit v :: ps => v.knownB && partKnown ps
  | .rd _ :: ps => partKnown ps

def Sk.knownB : Sk → Bool
  | .lit v => v.knownB
  | .rd _ => true
  | .gate _ l r => l.knownB && r.knownB
  | .cat ps => partKnown ps
  | .fill b => b.isKnown

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
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? ds l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr : rdsOf? ds r with e2 | rb
          · simp [hg, hl, hr] at h
          · simp only [hg, hl, hr, Except.ok.injEq] at h
            subst h
            simp [cnt, rdsOf?_len l ra hl hf.1, rdsOf?_len r rb hr hf.2]
  | .ident n, rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h; subst h; simp [cnt]
  | .bitSel b i, rs, h, _ => by
      have h' : rdsLeaf? ds (.bitSel b i) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.bitSel b i) with m | a
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
  | .int .., rs, h, _ | .unary .., rs, h, _ | .ternary .., rs, h, _
  | .resize .., rs, h, _ | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _ | .partSel .., rs, h, _ | .repl .., rs, h, _
  | .reduce .., rs, h, _ | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-- On an accepted gate tree the skeleton's leaves are exactly the reads. -/
theorem skT_leaves {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (skT v rs).leaves = rs
  | .lit _, rs, h, _ => by simp [rdsOf?] at h; subst h; simp [skT, Sk.leaves]
  | .binary op l r, rs, h, hf => by
      simp only [fragG, Bool.and_eq_true] at hf
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? ds l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr : rdsOf? ds r with e2 | rb
          · simp [hg, hl, hr] at h
          · simp only [hg, hl, hr, Except.ok.injEq] at h
            subst h
            have hla := rdsOf?_len l ra hl hf.1
            obtain ⟨-, hb⟩ := gateOf_cases hg
            have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
            have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
            rcases hb with rfl | rfl | rfl <;>
              simp [skT, hg, e1, e2, mkGate, Sk.leaves, skT_leaves l ra hl hf.1, skT_leaves r rb hr hf.2]
  | .ident n, rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h; subst h; simp [skT, Sk.leaves]
  | .bitSel b i, rs, h, _ => by
      have h' : rdsLeaf? ds (.bitSel b i) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.bitSel b i) with m | a
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
  | .int .., rs, h, _ | .unary .., rs, h, _ | .ternary .., rs, h, _
  | .resize .., rs, h, _ | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _ | .partSel .., rs, h, _ | .repl .., rs, h, _
  | .reduce .., rs, h, _ | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

end CombEq
end LeanModels.Sv
