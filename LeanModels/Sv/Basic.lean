/-!
# SV 4-state value core (`LeanModels.Sv`)

The normative 4-state value types and operator library of
`docs/sv-design-m0.md` ("4-state value core"). Everything downstream — the
interpreter in `Semantics.lean` AND the proofs — calls exactly these named
functions; there is no second copy of any operator table.

Conventions:
* `LVec.bits` is **LSB-first**: `bits[0]` is bit 0 (the SV `v[0]`).
* `Logic.lz` behaves exactly like `Logic.lx` in every operator except the
  case-equality family (`===`/`!==`), per IEEE 1800-2017 (the LRM).
* Operators whose SV result is a single bit (`== != === !== < <= > >= !`)
  return `Logic`; the interpreter lifts with `LVec.ofLogic` where an
  expression value is needed. Whole-vector operators return `LVec`.
* M0 restricts sources to same-width operands (the extractor emits resolved
  widths and marks mismatches `Unsupported`). The functions here are still
  total: on a width mismatch the binary ones fall back to an all-x result of
  the larger width (documented per function). This fallback is
  out-of-contract behavior — no theorem should rely on it.

All facts below were verified on Xcelium 24.03 per the design contract.
-/

namespace LeanModels.Sv

/-- 4-state scalar value, IEEE 1800-2017 §6.3.1: `0`, `1`, `x` (unknown),
`z` (high impedance). `z` behaves as `x` in every operator below except the
case-equality family (`===`/`!==`). -/
inductive Logic where
  | l0
  | l1
  | lx
  | lz
deriving Repr, BEq, DecidableEq, Inhabited

namespace Logic

/-- `true` iff the bit is a definite `0`/`1` (not `x`/`z`). -/
def isKnown : Logic → Bool
  | l0 | l1 => true
  | lx | lz => false

/-- Parse one SV binary digit (`0 1 x X z Z`). -/
def ofChar? : Char → Option Logic
  | '0' => some l0
  | '1' => some l1
  | 'x' | 'X' => some lx
  | 'z' | 'Z' => some lz
  | _ => none

/-- Display char (`0 1 x z`), matching simulator `%b` output. -/
def toChar : Logic → Char
  | l0 => '0'
  | l1 => '1'
  | lx => 'x'
  | lz => 'z'

/-- Bitwise AND, IEEE 1800-2017 §11.4.8: `0 & any = 0`, `1 & 1 = 1`,
else `x` (`z` acts as `x`). -/
def and : Logic → Logic → Logic
  | l0, _ => l0
  | _, l0 => l0
  | l1, l1 => l1
  | _, _ => lx

/-- Bitwise OR, IEEE 1800-2017 §11.4.8: `1 | any = 1`, `0 | 0 = 0`,
else `x` (`z` acts as `x`). -/
def or : Logic → Logic → Logic
  | l1, _ => l1
  | _, l1 => l1
  | l0, l0 => l0
  | _, _ => lx

/-- Bitwise XOR, IEEE 1800-2017 §11.4.8: any `x`/`z` operand bit gives `x`,
else ordinary xor. -/
def xor : Logic → Logic → Logic
  | l0, l0 => l0
  | l0, l1 => l1
  | l1, l0 => l1
  | l1, l1 => l0
  | _, _ => lx

/-- Bitwise negation `~`, IEEE 1800-2017 §11.4.8: `~0 = 1`, `~1 = 0`,
`~x = ~z = x`. -/
def not : Logic → Logic
  | l0 => l1
  | l1 => l0
  | _ => lx

/-- Conditional-operator bit merge, IEEE 1800-2017 §11.4.11: when the
condition of `c ? a : b` is ambiguous both arms are evaluated and combined
bit by bit — equal *known* bits are kept, every other combination
(differing, or any `x`/`z`, including `z`-vs-`z`) is `x`. -/
def merge : Logic → Logic → Logic
  | l0, l0 => l0
  | l1, l1 => l1
  | _, _ => lx

end Logic

/-- A 4-state vector. `bits` is **LSB-first**: `bits[0]` is bit 0 (SV `v[0]`).
The SV declaration `logic [W-1:0] v` gives `bits.size = W`; a scalar `logic`
is width 1. -/
structure LVec where
  bits : Array Logic
deriving Repr, BEq, DecidableEq, Inhabited

namespace LVec

/-- Bit width. -/
def width (v : LVec) : Nat := v.bits.size

/-- Lift a single bit to a width-1 vector (how the interpreter turns the
`Logic`-valued operators `== != === !== < <= > >= !` into expression values). -/
def ofLogic (b : Logic) : LVec := ⟨#[b]⟩

/-- Constant vector of width `w`. -/
def replicate (w : Nat) (b : Logic) : LVec := ⟨.replicate w b⟩

/-- All-`x` vector of width `w` — the LRM startup value of every variable
without an initializer (§6.8), and the collapsed result of arithmetic on
unknowns (§11.4.3). -/
def xVec (w : Nat) : LVec := replicate w .lx

/-- Vector of width `w` holding `n % 2^w` (bit `i` = `n.testBit i`). -/
def ofNat (w n : Nat) : LVec := ⟨.ofFn (n := w) fun i => if n.testBit i then .l1 else .l0⟩

/-- Embed a known `BitVec`. -/
def ofBitVec {w : Nat} (b : BitVec w) : LVec := ofNat w b.toNat

/-- Parse a binary digit string written MSB-first (as in SV source:
`"1x"` = 2'b1x). Underscore separators are skipped. Returns `none` on any
other character. Width = number of digits (no padding — see `ofBinLit?`). -/
def ofString? (s : String) : Option LVec := do
  let mut bits : Array Logic := #[]
  for c in s.toList.reverse do  -- reverse: source is MSB-first, `bits` LSB-first
    if c == '_' then
      continue
    bits := bits.push (← Logic.ofChar? c)
  return ⟨bits⟩

/-- Test/dev convenience: `LVec.lit "1x"` is 2'b1x. Invalid strings give the
empty vector — use only with literal constant strings. -/
def lit (s : String) : LVec := (ofString? s).getD ⟨#[]⟩

/-- A binary digit string extended/truncated to an explicit width, following
the SV based-literal rule (§5.7.1): if the literal is narrower than `w` it is
left-extended with `0` when its leading (most significant) digit is `0`/`1`,
with `x` when it is `x`, with `z` when it is `z`; if wider, the low `w` bits
are kept. Used by JSON ingestion for `Literal` nodes. -/
def ofBinLit? (w : Nat) (s : String) : Option LVec := do
  let v ← ofString? s
  if v.width ≥ w then
    return ⟨v.bits.extract 0 w⟩
  let pad : Logic :=
    match v.bits.back? with  -- back of LSB-first array = most significant digit
    | some .lx => .lx
    | some .lz => .lz
    | _ => .l0
  return ⟨v.bits ++ Array.replicate (w - v.width) pad⟩

/-- Display MSB-first with `x`/`z` chars, matching simulator `%b` output
(width 0 gives `""`). -/
def toBinString (v : LVec) : String :=
  String.ofList (v.bits.toList.reverse.map Logic.toChar)

/-- `true` iff every bit is a definite `0`/`1`. -/
def allKnown (v : LVec) : Bool := v.bits.all Logic.isKnown

/-- Unsigned value, *treating any `x`/`z` bit as 0* — meaningful only when
`allKnown`; use `toNat?`/`known?` outside this file. -/
def toNat (v : LVec) : Nat :=
  v.bits.foldr (fun b acc => 2 * acc + (if b == .l1 then 1 else 0)) 0

/-- Unsigned value if fully known, else `none`. -/
def toNat? (v : LVec) : Option Nat :=
  if v.allKnown then some v.toNat else none

/-- The contract's `LVec.known? : LVec → Option (BitVec w)`: the `BitVec`
image of a fully-known vector (`bv_decide` automation lives on this side),
`none` if any bit is `x`/`z`. -/
def known? (v : LVec) : Option (BitVec v.width) :=
  if v.allKnown then some (BitVec.ofNat v.width v.toNat) else none

/-! ### Bitwise operators (per-bit tables, §11.4.8) -/

/-- Zip two same-width vectors bit by bit; width mismatch (out of contract,
see module docstring) gives all-x at the larger width. -/
def zipWith (f : Logic → Logic → Logic) (a b : LVec) : LVec :=
  if a.width = b.width then ⟨Array.zipWith f a.bits b.bits⟩
  else xVec (max a.width b.width)

/-- Vector `&` (per-bit `Logic.and`). -/
def and (a b : LVec) : LVec := zipWith Logic.and a b

/-- Vector `|` (per-bit `Logic.or`). -/
def or (a b : LVec) : LVec := zipWith Logic.or a b

/-- Vector `^` (per-bit `Logic.xor`). -/
def xor (a b : LVec) : LVec := zipWith Logic.xor a b

/-- Vector `~` (per-bit `Logic.not`). -/
def not (a : LVec) : LVec := ⟨a.bits.map Logic.not⟩

/-! ### Arithmetic (whole-vector x-collapse, §11.4.3)

If ANY bit of either operand is `x`/`z`, the ENTIRE result is `x` — never a
bit-precise carry through unknowns (Xcelium-confirmed). -/

/-- Result width of a binary arithmetic op: the common width; `max` of the
two on an (out-of-contract) mismatch. -/
def arithWidth (a b : LVec) : Nat := max a.width b.width

/-- Vector `+` (mod `2^w`), §11.4.3: any unknown bit collapses the whole
result to x. -/
def add (a b : LVec) : LVec :=
  match a.toNat?, b.toNat? with
  | some x, some y => ofNat (arithWidth a b) (x + y)
  | _, _ => xVec (arithWidth a b)

/-- Vector `-` (mod `2^w`), §11.4.3 collapse rule as `add`. -/
def sub (a b : LVec) : LVec :=
  let w := arithWidth a b
  match a.toNat?, b.toNat? with
  | some x, some y => ofNat w (x + (2 ^ w - y))
  | _, _ => xVec w

/-- Vector `*` (mod `2^w`), §11.4.3 collapse rule as `add`. (In the M0
normative operator tables but not in the M0 expression tier — the extractor
does not emit it; provided for completeness.) -/
def mul (a b : LVec) : LVec :=
  match a.toNat?, b.toNat? with
  | some x, some y => ofNat (arithWidth a b) (x * y)
  | _, _ => xVec (arithWidth a b)

/-- Unary `-`: two's complement (mod `2^w`) with the §11.4.3 collapse rule. -/
def neg (a : LVec) : LVec :=
  match a.toNat? with
  | some x => ofNat a.width (2 ^ a.width - x)
  | none => xVec a.width

/-! ### Relational operators (§11.4.4)

Unsigned comparison; result is one bit, and any `x`/`z` bit in either
operand makes it `x` (the 1-bit case of the arithmetic collapse). -/

/-- Relational-op skeleton: `cmp` on the unsigned values when both operands
are fully known, else `x`. Width mismatch compares the unsigned values (each
of its own width) — out of contract, cannot arise from the M0 extractor. -/
def relOp (cmp : Nat → Nat → Bool) (a b : LVec) : Logic :=
  match a.toNat?, b.toNat? with
  | some x, some y => if cmp x y then .l1 else .l0
  | _, _ => .lx

/-- `<` (§11.4.4). -/
def lt (a b : LVec) : Logic := relOp (· < ·) a b

/-- `<=` (§11.4.4). -/
def le (a b : LVec) : Logic := relOp (· ≤ ·) a b

/-- `>` (§11.4.4). -/
def gt (a b : LVec) : Logic := relOp (· > ·) a b

/-- `>=` (§11.4.4). -/
def ge (a b : LVec) : Logic := relOp (· ≥ ·) a b

/-! ### Equality (§11.4.5) -/

/-- Logical equality `==`, §11.4.5 (Xcelium-confirmed): the result is `0`
(definite) if SOME bit position has both bits known and unequal; otherwise
`x` if any `x`/`z` appears anywhere; otherwise `1`. NOT "any x → x":
`(2'b1x == 2'b00) = 0` because bit 1 is a definite mismatch. Width mismatch
(out of contract): `x`. -/
def eqLogical (a b : LVec) : Logic :=
  if a.width ≠ b.width then .lx
  else
    let pairs := Array.zip a.bits b.bits
    if pairs.any fun (x, y) => x.isKnown && y.isKnown && x != y then .l0
    else if (a.allKnown && b.allKnown : Bool) then .l1
    else .lx

/-- Logical inequality `!=` = negation of `eqLogical` (so the definite-
mismatch case gives a definite `1`). -/
def neLogical (a b : LVec) : Logic := (eqLogical a b).not

/-- Case equality `===`, §11.4.5: exact 4-state match (`x` ≠ `z`!), always a
definite `0`/`1`. Width mismatch: `0`. -/
def eqCase (a b : LVec) : Logic := if a == b then .l1 else .l0

/-- Case inequality `!==`. -/
def neCase (a b : LVec) : Logic := (eqCase a b).not

/-! ### Truthiness, logical negation, conditional (§12.4, §11.4.7, §11.4.11) -/

/-- `if (c)` truthiness, §12.4 (Xcelium-confirmed): true iff `c` has at
least one `l1` bit. All-zero OR unknown-only (`1'bx`, `1'bz`, `2'b0x`, …)
takes the else branch — X-optimism; an absent else is a no-op, so a
latch-style `if` with an x condition HOLDS its target. `2'b1x` is true (the
value is nonzero no matter what x is). -/
def condTrue (c : LVec) : Bool := c.bits.any (· == .l1)

/-- `true` iff every bit is a definite `0` (the definitely-false case). -/
def isKnownZero (c : LVec) : Bool := c.bits.all (· == .l0)

/-- Logical negation `!c`, §11.4.7: `1` iff `c` is all-known-zero, `0` iff
`c` has some `l1` bit, else `x`. (So `!2'b1x = 0` but `!2'b0x = x`.) -/
def lnot (c : LVec) : Logic :=
  if c.condTrue then .l0
  else if c.isKnownZero then .l1
  else .lx

/-- Bit-by-bit merge of the two arms of a conditional with ambiguous
condition, §11.4.11: per-bit `Logic.merge` (equal known bits kept, all else
`x`). Width mismatch (out of contract): all-x at the larger width. -/
def merge (a b : LVec) : LVec := zipWith Logic.merge a b

/-- Full conditional `c ? a : b`, §11.4.11 — different from `if`! Some `l1`
bit in `c`: `a`. All-known-zero `c`: `b`. Ambiguous `c` (no `l1`, some
`x`/`z`): `merge a b`. -/
def ternary (c a b : LVec) : LVec :=
  if c.condTrue then a
  else if c.isKnownZero then b
  else merge a b

/-! ### Concatenation (§11.4.12) -/

/-- `{msb, lsb}`: `msb` becomes the high bits. LSB-first representation
makes this `lsb.bits ++ msb.bits`. -/
def concat (msb lsb : LVec) : LVec := ⟨lsb.bits ++ msb.bits⟩

/-- `{p₀, p₁, …, pₙ}` with parts in **source order** (`p₀` is the most
significant), §11.4.12. Result width is the sum of the part widths. -/
def concatMany (parts : Array LVec) : LVec :=
  parts.foldl (fun acc p => ⟨p.bits ++ acc.bits⟩) ⟨#[]⟩

end LVec

/-! ## Unit tests (`#guard`) — every normative table row

Sources: docs/sv-design-m0.md "4-state value core" (Xcelium-verified). -/

section Tests
open Logic

-- Logic.and: full 16-entry table (0&any=0, 1&1=1, else x; z as x)
#guard Logic.and l0 l0 == l0
#guard Logic.and l0 l1 == l0
#guard Logic.and l0 lx == l0
#guard Logic.and l0 lz == l0
#guard Logic.and l1 l0 == l0
#guard Logic.and l1 l1 == l1
#guard Logic.and l1 lx == lx
#guard Logic.and l1 lz == lx
#guard Logic.and lx l0 == l0
#guard Logic.and lx l1 == lx
#guard Logic.and lx lx == lx
#guard Logic.and lx lz == lx
#guard Logic.and lz l0 == l0
#guard Logic.and lz l1 == lx
#guard Logic.and lz lx == lx
#guard Logic.and lz lz == lx

-- Logic.or: full table (1|any=1, 0|0=0, else x; z as x)
#guard Logic.or l0 l0 == l0
#guard Logic.or l0 l1 == l1
#guard Logic.or l0 lx == lx
#guard Logic.or l0 lz == lx
#guard Logic.or l1 l0 == l1
#guard Logic.or l1 l1 == l1
#guard Logic.or l1 lx == l1
#guard Logic.or l1 lz == l1
#guard Logic.or lx l0 == lx
#guard Logic.or lx l1 == l1
#guard Logic.or lx lx == lx
#guard Logic.or lx lz == lx
#guard Logic.or lz l0 == lx
#guard Logic.or lz l1 == l1
#guard Logic.or lz lx == lx
#guard Logic.or lz lz == lx

-- Logic.xor: full table (any x/z → x)
#guard Logic.xor l0 l0 == l0
#guard Logic.xor l0 l1 == l1
#guard Logic.xor l0 lx == lx
#guard Logic.xor l0 lz == lx
#guard Logic.xor l1 l0 == l1
#guard Logic.xor l1 l1 == l0
#guard Logic.xor l1 lx == lx
#guard Logic.xor l1 lz == lx
#guard Logic.xor lx l0 == lx
#guard Logic.xor lx l1 == lx
#guard Logic.xor lx lx == lx
#guard Logic.xor lx lz == lx
#guard Logic.xor lz l0 == lx
#guard Logic.xor lz l1 == lx
#guard Logic.xor lz lx == lx
#guard Logic.xor lz lz == lx

-- Logic.not
#guard Logic.not l0 == l1
#guard Logic.not l1 == l0
#guard Logic.not lx == lx
#guard Logic.not lz == lx

-- Logic.merge (§11.4.11): equal known kept, all else x (z-vs-z is x!)
#guard Logic.merge l0 l0 == l0
#guard Logic.merge l1 l1 == l1
#guard Logic.merge l0 l1 == lx
#guard Logic.merge l1 l0 == lx
#guard Logic.merge l0 lx == lx
#guard Logic.merge lx lx == lx
#guard Logic.merge lz lz == lx
#guard Logic.merge l1 lz == lx

-- Construction / display round-trips (LSB-first: bits[0] = bit 0)
#guard LVec.lit "1x" == ⟨#[lx, l1]⟩
#guard (LVec.ofNat 4 11).toBinString == "1011"
#guard (LVec.lit "1_01x").toBinString == "101x"
#guard (LVec.lit "1011").toNat? == some 11
#guard (LVec.lit "10z1").toNat? == none
#guard (⟨#[l0, l1]⟩ : LVec).known? == some 2#2
#guard (⟨#[lx, l1]⟩ : LVec).known? == none
#guard (LVec.ofBitVec (0xAB : BitVec 8)).toBinString == "10101011"
#guard LVec.xVec 3 == LVec.lit "xxx"
#guard (LVec.ofBinLit? 8 "0").map LVec.toBinString == some "00000000"  -- '0 at width 8
#guard (LVec.ofBinLit? 4 "x").map LVec.toBinString == some "xxxx"      -- x-extension
#guard (LVec.ofBinLit? 4 "z1").map LVec.toBinString == some "zzz1"    -- z-extension
#guard (LVec.ofBinLit? 4 "10").map LVec.toBinString == some "0010"    -- 0-extension
#guard (LVec.ofBinLit? 2 "0110").map LVec.toBinString == some "10"    -- truncate keeps low bits
#guard LVec.ofBinLit? 4 "0b1" == none                                  -- invalid digit

-- Vector bitwise
#guard LVec.and (.lit "01xz") (.lit "1111") == .lit "01xx"
#guard LVec.and (.lit "01xz") (.lit "0000") == .lit "0000"
#guard LVec.or (.lit "01xz") (.lit "0000") == .lit "01xx"
#guard LVec.or (.lit "01xz") (.lit "1111") == .lit "1111"
#guard LVec.xor (.lit "01xz") (.lit "1010") == .lit "11xx"
#guard LVec.not (.lit "01xz") == .lit "10xx"

-- Arithmetic: whole-vector x-collapse (§11.4.3) — NEVER bit-precise carry
#guard LVec.add (.lit "0x") (.lit "01") == .lit "xx"
#guard LVec.add (.lit "1z") (.lit "01") == .lit "xx"
#guard LVec.add (.lit "10000000") (.lit "0000000x") == LVec.xVec 8  -- one x bit → ALL 8 x
#guard LVec.add (.lit "11") (.lit "01") == .lit "00"                -- 3+1 wraps mod 4
#guard LVec.add (.lit "0101") (.lit "0011") == .lit "1000"          -- 5+3=8
#guard LVec.sub (.lit "00") (.lit "01") == .lit "11"                -- 0-1 wraps
#guard LVec.sub (.lit "1000") (.lit "0011") == .lit "0101"          -- 8-3=5
#guard LVec.sub (.lit "0x") (.lit "01") == .lit "xx"
#guard LVec.mul (.lit "10") (.lit "11") == .lit "10"                -- 2*3=6 mod 4=2
#guard LVec.mul (.lit "1x") (.lit "01") == .lit "xx"
#guard LVec.neg (.lit "01") == .lit "11"                            -- -1 = 3 (2 bits)
#guard LVec.neg (.lit "00") == .lit "00"
#guard LVec.neg (.lit "10") == .lit "10"                            -- -2 = 2 (2 bits)
#guard LVec.neg (.lit "1z") == .lit "xx"

-- Relational (§11.4.4): 1-bit result, any x/z → x
#guard LVec.lt (.lit "01") (.lit "10") == l1
#guard LVec.lt (.lit "10") (.lit "01") == l0
#guard LVec.lt (.lit "0x") (.lit "10") == lx
#guard LVec.le (.lit "10") (.lit "10") == l1
#guard LVec.le (.lit "11") (.lit "10") == l0
#guard LVec.le (.lit "z1") (.lit "11") == lx
#guard LVec.gt (.lit "10") (.lit "01") == l1
#guard LVec.gt (.lit "01") (.lit "10") == l0
#guard LVec.gt (.lit "1x") (.lit "00") == lx  -- even though 1x > 00 for any x!
#guard LVec.ge (.lit "10") (.lit "10") == l1
#guard LVec.ge (.lit "01") (.lit "10") == l0
#guard LVec.ge (.lit "01") (.lit "1z") == lx

-- Logical equality (§11.4.5): definite-mismatch-else-x
#guard LVec.neLogical (.lit "1x") (.lit "00") == l1  -- (2'b1x != 0) = 1: bit 1 definitely differs
#guard LVec.eqLogical (.lit "1x") (.lit "00") == l0
#guard LVec.eqLogical (.lit "0x") (.lit "00") == lx  -- (2'b0x == 0) = x: ambiguous
#guard LVec.neLogical (.lit "0x") (.lit "00") == lx
#guard LVec.eqLogical (.lit "10") (.lit "10") == l1
#guard LVec.eqLogical (.lit "10") (.lit "11") == l0
#guard LVec.neLogical (.lit "10") (.lit "11") == l1
#guard LVec.eqLogical (.lit "1z") (.lit "10") == lx  -- z as x: ambiguous match
#guard LVec.eqLogical (.lit "z") (.lit "x") == lx

-- Case equality (§11.4.5): exact 4-state match, always definite; x ≠ z
#guard LVec.eqCase (.lit "1x") (.lit "1x") == l1
#guard LVec.eqCase (.lit "1x") (.lit "1z") == l0
#guard LVec.eqCase (.lit "z") (.lit "x") == l0
#guard LVec.neCase (.lit "z") (.lit "x") == l1
#guard LVec.eqCase (.lit "10") (.lit "10") == l1
#guard LVec.neCase (.lit "10") (.lit "10") == l0

-- if-condition truthiness (§12.4): true iff some l1 bit
#guard LVec.condTrue (.lit "1") == true
#guard LVec.condTrue (.lit "0") == false
#guard LVec.condTrue (.lit "x") == false   -- if (1'bx) takes else
#guard LVec.condTrue (.lit "z") == false   -- if (1'bz) takes else
#guard LVec.condTrue (.lit "1x") == true   -- 2'b1x is definitely nonzero
#guard LVec.condTrue (.lit "0x") == false
#guard LVec.condTrue (.lit "00") == false

-- Logical negation ! (§11.4.7)
#guard LVec.lnot (.lit "00") == l1
#guard LVec.lnot (.lit "01") == l0
#guard LVec.lnot (.lit "0x") == lx
#guard LVec.lnot (.lit "1x") == l0   -- definitely nonzero
#guard LVec.lnot (.lit "z") == lx

-- Ternary (§11.4.11): different from if!
#guard LVec.ternary (.lit "1") (.lit "1010") (.lit "1001") == .lit "1010"
#guard LVec.ternary (.lit "0") (.lit "1010") (.lit "1001") == .lit "1001"
#guard LVec.ternary (.lit "x") (.lit "1010") (.lit "1001") == .lit "10xx"  -- merge
#guard LVec.ternary (.lit "z") (.lit "1010") (.lit "1001") == .lit "10xx"
#guard LVec.ternary (.lit "0x") (.lit "1010") (.lit "1001") == .lit "10xx" -- ambiguous → merge
#guard LVec.ternary (.lit "1x") (.lit "1010") (.lit "1001") == .lit "1010" -- 1 bit → TRUE arm
#guard LVec.ternary (.lit "x") (.lit "1010") (.lit "1010") == .lit "1010"  -- equal arms survive

-- Concatenation (§11.4.12): {msb, lsb}
#guard LVec.concat (.lit "10") (.lit "01") == .lit "1001"
#guard (LVec.concat (.lit "10") (.lit "01")).width == 4
#guard LVec.concatMany #[.lit "10", .lit "01"] == .lit "1001"          -- source order, p₀ most significant
#guard LVec.concatMany #[.lit "1", .lit "0x", .lit "z"] == .lit "10xz"
#guard LVec.concatMany #[] == ⟨#[]⟩

-- Width-0 sanity
#guard (⟨#[]⟩ : LVec).condTrue == false
#guard LVec.add ⟨#[]⟩ ⟨#[]⟩ == ⟨#[]⟩

end Tests

end LeanModels.Sv
