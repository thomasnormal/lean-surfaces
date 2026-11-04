import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombProcEq

/-!
# Exhaustive evaluation of a flat combinational netlist (`sv_exhaustive`): compile once, run many

The comb route's producer theorem `CombEq.eq_view` gives, for a settled state `st` of a design whose
summary is `s`, the netlist view `s.Eqs σ st`: every site's target bits are its skeleton's bits
(`Sk.bitC`) of the reads `st.boolAt`. This module COMPILES a flat summary's sites at the fixed valuation
`σ`, once, into a gate program over the bits of ONE natural number (`GSite`: a packed bit index and a gate
expression `GE` over packed bit indices), and RUNS it (`runG`): the scheme of PROVING.md §12, made generic.

Why compile: interpreting the skeletons directly costs the kernel hundreds to thousands of steps per gate
(string-keyed widths and layout, `Int` window arithmetic), on every input; measured at G-E0, over 20 minutes
for the 113-gate S-box on 256 inputs, where the gate list takes 10.5 s. The compiled program is the gate list.
(`X.sem` itself, `PDesign.instantiateGD2`, does not reduce in the kernel; the summary does.)

The API is for CONES: a program is any list of compiled bits; nothing assumes all of a design's sites or
all of its outputs.
-/

namespace LeanModels.Sv.Exh

open CombView CombEq

/-! ## The gate program -/

/-- A gate expression over the bits of a packed environment. -/
inductive GE where
  | bit (j : Nat)
  | const (b : Bool)
  | not (a : GE)
  | and (a b : GE)
  | or (a b : GE)
  | xor (a b : GE)
  | ite (c a b : GE)
  /-- A WORD-level table lookup: bit `n` of the bitmap `bits` (one bit per word, `lutT`), `n` the word of the
  packed bits `base .. base+w-1` (bit 0 first). -/
  | lut (base w bits : Nat)
deriving DecidableEq, Repr

/-- The value of a gate expression, given the packed bits `f`. -/
def GE.eval (f : Nat → Bool) : GE → Bool
  | .bit j => f j
  | .const b => b
  | .not a => !a.eval f
  | .and a b => a.eval f && b.eval f
  | .or a b => a.eval f || b.eval f
  | .xor a b => a.eval f ^^ b.eval f
  | .ite c a b => if c.eval f then a.eval f else b.eval f
  | .lut base w bits => bits.testBit (XF.val (fun i => f (base + i)) w)

/-- The packed bits a gate expression reads. -/
def GE.bits : GE → List Nat
  | .bit j => [j]
  | .const _ => []
  | .not a => a.bits
  | .and a b | .or a b | .xor a b => a.bits ++ b.bits
  | .ite c a b => c.bits ++ a.bits ++ b.bits
  | .lut base w _ => (List.range w).map (base + ·)

/-- One compiled bit: packed bit `out` gets the value of `e`. -/
structure GSite where
  out : Nat
  e : GE
deriving DecidableEq, Repr

/-- **The packed run** of a program (the target bits start `0`). -/
def runG : List GSite → Nat → Nat
  | [], e => e
  | g :: gs, e => runG gs (if g.e.eval e.testBit then e ||| 2 ^ g.out else e)

/-! ## The compiler (the bitwise fragment) -/

/-- Bit `i` of `n`: its packed bit, inside the declared width only (a read past it is refused). -/
def bitG (dw off : String → Nat) (n : String) (i : Nat) : Option GE := if i < dw n then some (.bit (off n + i)) else none

/-- Bit `k` of a skeleton at the context width `tw`, compiled; `none` outside the bitwise fragment
(`& | ^ ~`, literals and constants, access bits inside the declared widths). -/
def _root_.LeanModels.Sv.CombEq.Sk.compile (σ : String → Int) (dw off : String → Nat) :
    Sk → Nat → Nat → Option GE
  | .lit v, _, k => some (.const (v.boolAt k))
  | .rd a, _, k => bitG dw off a.name (Acc.lo σ a + k)
  | .gate g l r, tw, k => do
      let a ← l.compile σ dw off tw k
      let b ← r.compile σ dw off tw k
      some (match g with | .and => .and a b | .or => .or a b | .xor => .xor a b)
  | .fill b, _, _ => some (.const (b == Logic.l1))
  | .bnot a, tw, k => (a.compile σ dw off tw k).map .not
  | .const v, tw, k => some (.const (XF.constBit v tw k))
  | _, _, _ => none

/-- One arm of a `case` over literals as a table entry (one pattern, of width `w`). -/
def armOf (w : Nat) : List LVec × Sk → Option (Nat × Nat)
  | ([p], .lit v) => if p.width = w then some (p.nat, v.nat) else none
  | _ => none

/-- The arms of a `case` over literals as a table of numbers. -/
def tblOf (w : Nat) : List (List LVec × Sk) → Option (List (Nat × Nat))
  | [] => some []
  | e :: its => (armOf w e).bind fun q => (tblOf w its).map (q :: ·)

/-- `x` with bit `p` set to `b`. -/
def setB (x p : Nat) (b : Bool) : Nat := if x.testBit p == b then x else x ^^^ 2 ^ p

/-- Bit `k` of the lookup in `t` (the first entry whose key matches, else `d`) for each of the words `0 .. N-1`, as
the bits of ONE number: built in one pass over the table (the kernel never scans it per input). -/
def lutT (k d N : Nat) : List (Nat × Nat) → Nat
  | [] => if d.testBit k then 2 ^ N - 1 else 0
  | (p, v) :: rest => setB (lutT k d N rest) p (v.testBit k)

/-- A `case` of an access (at most 16 bits) over literals, compiled: a word-level table lookup (`GE.lut`). -/
def casesG (σ : String → Int) (dw off : String → Nat) (s : Sk) (its : List (List LVec × Sk)) (d : Sk) (k : Nat) :
    Option GE :=
  match s, d with
  | .rd a, .lit dv => if Acc.lo σ a + (a.win σ dw).2.2 ≤ dw a.name ∧ (a.win σ dw).2.2 ≤ 16 then
      (tblOf (a.win σ dw).2.2 its).map fun t =>
        .lut (off a.name + Acc.lo σ a) (a.win σ dw).2.2 (lutT k dv.nat (2 ^ (a.win σ dw).2.2) t)
    else none
  | _, _ => none

/-- Bit `k` of a procedural skeleton at the width `tw`, compiled: an `if` to `ite`, a `case` by `casesG`. -/
def _root_.LeanModels.Sv.CombEq.PSk.compile (σ : String → Int) (dw off : String → Nat) :
    PSk → Nat → Nat → Option GE
  | .leaf sk, tw, k => sk.compile σ dw off tw k
  | .ite c a b, tw, k | .ovr c a b, tw, k => (c.compile σ dw off 1 0).bind fun gc =>
      (a.compile σ dw off tw k).bind fun ga => (b.compile σ dw off tw k).map (.ite gc ga ·)
  | .blk a, tw, k => a.compile σ dw off tw k
  | .cases s its d, _, k => casesG σ dw off s its d k

/-- Bits `0 .. c-1` of a skeleton at the width `tw`, compiled, written at packed bits `o + k`. -/
def bitsG (σ : String → Int) (dw off : String → Nat) (sk : PSk) (o tw : Nat) : Nat → Option (List GSite)
  | 0 => some []
  | c + 1 => do
      let gs ← bitsG σ dw off sk o tw c
      let g ← sk.compile σ dw off tw c
      some (gs ++ [⟨o + c, g⟩])

/-- The compiled bits of one plain site at the valuation `σ` (refused unless its window is declared). -/
def siteG (s : Summary) (σ : String → Int) (off : String → Nat) (ls : LSite) : Option (List GSite) :=
  let W := ls.site.tgt.win σ (s.dw σ)
  if ls.hdrs.isEmpty && decide (W.2.1 + W.2.2 ≤ s.dw σ W.1) then
    bitsG σ (s.dw σ) off (rhsSk ls.site.proc ls.site.rds) (off W.1 + W.2.1) W.2.2 W.2.2
  else none

/-- **The compiled program** of the sites `ord` (positions in `s.lsites`), in that order. -/
def compileNet (s : Summary) (σ : String → Int) (off : String → Nat) : List Nat → Option (List GSite)
  | [] => some []
  | i :: ord => do
      let ls ← s.lsites[i]?
      let gs ← siteG s σ off ls
      let rest ← compileNet s σ off ord
      some (gs ++ rest)

/-- The layout from offset `o`: the declarations in order, each after the widths of those before it. -/
def layoutR (σ : String → Int) : Nat → List DeclT → List (String × Nat)
  | _, [] => []
  | o, d :: ds => (d.name, o) :: layoutR σ (o + d.width σ) ds

/-- **The layout** of the declared names (disjoint windows by construction, `layout_inj`). -/
def layout (s : Summary) (σ : String → Int) (n : String) : Nat := ((layoutR σ 0 s.decls).lookup n).getD 0

end LeanModels.Sv.Exh
