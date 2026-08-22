import LeanModels.Core.Basic

/-!
# The C value model (`LeanModels.C`) — M2 inch 1

Fixed-width integer values and the arithmetic on them, per
`docs/c-semantics-design.md` §1. **This file has no world, no memory and
no interpreter**: it is the value layer alone, so the one decision that
cannot be retrofitted can be landed and gated before anything is built on
it.

**THE DECISION THIS FILE EXISTS FOR: unsigned WRAPS, signed REFUSES —
and the corpus needs both in adjacent operands.** Measured
(`docs/c-tier-charter.md` §2.2): `mix64` (sunfish.c L191-195) is
`x *= 0xff51afd7ed558ccdULL`, deliberate unsigned wraparound that C
DEFINES, while the same file's 327 overflow-capable signed sites are
undefined at the boundary and must refuse. A model that blurred the two
would be wrong about the corpus's hottest sort key.

Widths come from the ABSTRACT profile (`docs/c-profile.json`), not from a
host: 8 facts, satisfied by both development hosts, checkable on any
third by `harness/c_profile_probe.py --check`.

The stored value is always the MATHEMATICAL integer, in range for its
type. That invariant is what makes "did this overflow?" decidable rather
than conventional, and every rule below re-establishes it.
-/

namespace LeanModels.C.C23

/-! ## Integer types -/

/-- A C integer type: signedness and width in bits. `char`'s signedness
is a PROFILE fact (`char_signed`), depended on because
`CLS[(int)p->b[j]]` indexes a 128-entry table by a board byte. -/
structure IntTy where
  signed : Bool
  bits : Nat
deriving Repr, Inhabited, BEq, DecidableEq

namespace IntTy

/-- The profile's widths (`docs/c-profile.json`: `char_bit_8`, `int_32`,
`long_64`). The corpus's 10 integer types collapse onto these. -/
def char_ : IntTy := ⟨true, 8⟩          -- signed on both hosts, and depended on
def uchar : IntTy := ⟨false, 8⟩
def short_ : IntTy := ⟨true, 16⟩
def ushort : IntTy := ⟨false, 16⟩
def int_ : IntTy := ⟨true, 32⟩
def uint : IntTy := ⟨false, 32⟩
def long_ : IntTy := ⟨true, 64⟩
def ulong : IntTy := ⟨false, 64⟩

/-- `2 ^ bits`, the modulus. -/
def modulus (t : IntTy) : Int := (2 : Int) ^ t.bits

def minVal (t : IntTy) : Int :=
  if t.signed then -((2 : Int) ^ (t.bits - 1)) else 0

def maxVal (t : IntTy) : Int :=
  if t.signed then (2 : Int) ^ (t.bits - 1) - 1 else (2 : Int) ^ t.bits - 1

/-- Is `v` representable in `t`? -/
def inRange (t : IntTy) (v : Int) : Bool :=
  t.minVal ≤ v && v ≤ t.maxVal

/-- Reduce into range modulo 2^bits, two's-complement. This is C's
DEFINED behavior for unsigned types, and — since C23 §6.3.1.3 — for
conversion into a signed type as well. It is NOT how signed arithmetic
overflow behaves; that refuses. -/
def wrap (t : IntTy) (v : Int) : Int :=
  let m := t.modulus
  let r := v % m
  let r := if r < 0 then r + m else r      -- Int.emod can be negative
  if t.signed && r > t.maxVal then r - m else r

end IntTy

/-! ## Undefined behavior, as a named cause -/

/-- The UB classes this layer can raise. Each is a REFUSAL, never a
value, and — per `docs/c-semantics-design.md` §3.1 — **it never
retires: it is the product.** -/
inductive UB where
  | signedOverflow (op : String) (ty : IntTy) (v : Int)
  | divideByZero (op : String)
  | divideOverflow            -- `INT_MIN / -1`: the quotient is unrepresentable
  | shiftCountTooLarge (count : Int) (bits : Nat)
  | shiftCountNegative (count : Int)
  | shiftNegativeOperand (v : Int)
  | shiftOverflow (v : Int) (count : Int) (ty : IntTy)
deriving Repr, Inhabited, BEq

/-- The result of a value-level operation: an answer, or a loud refusal
with its cause. Total — there is no third outcome at this layer, because
fuel and the world do not exist here. -/
inductive CRes (α : Type) where
  | ok (value : α)
  | ub (cause : UB)
deriving Repr, Inhabited, BEq

namespace CRes

def bind : CRes α → (α → CRes β) → CRes β
  | .ok a, f => f a
  | .ub c, _ => .ub c

def isOk : CRes α → Bool
  | .ok _ => true
  | .ub _ => false

end CRes

/-! ## Values -/

/-- A C value at this layer. Pointers arrive with the memory model
(inch 2); `undef` is an indeterminate value that reached a use, which
every consumer refuses. -/
inductive CVal where
  | int (ty : IntTy) (v : Int)
  | undef
deriving Repr, Inhabited, BEq

/-! ## Arithmetic — where the split lives

Each operation computes the MATHEMATICAL result first, then decides by
signedness: unsigned reduces modulo, signed refuses out of range. -/

/-- Close a mathematical result into `t`: wrap if unsigned, refuse if
signed and out of range. **This function IS the decision.** -/
def close (op : String) (t : IntTy) (v : Int) : CRes CVal :=
  if t.inRange v then .ok (.int t v)
  else if t.signed then .ub (.signedOverflow op t v)
  else .ok (.int t (t.wrap v))

def addOp (t : IntTy) (a b : Int) : CRes CVal := close "+" t (a + b)
def subOp (t : IntTy) (a b : Int) : CRes CVal := close "-" t (a - b)
def mulOp (t : IntTy) (a b : Int) : CRes CVal := close "*" t (a * b)
def negOp (t : IntTy) (a : Int) : CRes CVal := close "-" t (-a)

/-- C truncates toward zero (§6.5.5), which is `Int.tdiv`, NOT Lean's
`/` on `Int` (that floors). Getting this wrong is the `pyfloordiv`
divergence class the ctwin README names as #1, from the other side. -/
def divOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b == 0 then .ub (.divideByZero "/")
  else if t.signed && a == t.minVal && b == -1 then .ub .divideOverflow
  else close "/" t (Int.tdiv a b)

/-- The remainder pairs with `tdiv`: `a % b` has the sign of `a`. -/
def modOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b == 0 then .ub (.divideByZero "%")
  else if t.signed && a == t.minVal && b == -1 then .ub .divideOverflow
  else close "%" t (Int.tmod a b)

/-- `<<`: the count must be in `[0, bits)`, the left operand must be
non-negative when signed, and a signed result must be representable
(C23 §6.5.7). All four failures are distinct causes. -/
def shlOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b < 0 then .ub (.shiftCountNegative b)
  else if b ≥ (t.bits : Int) then .ub (.shiftCountTooLarge b t.bits)
  else if t.signed && a < 0 then .ub (.shiftNegativeOperand a)
  else
    let r := a * (2 : Int) ^ b.toNat
    if t.signed && !t.inRange r then .ub (.shiftOverflow a b t)
    else close "<<" t r

/-- `>>`: the count is constrained the same way. On a non-negative
operand this is division by a power of two; the corpus has **zero signed
right shifts** (measured), so the negative-operand arm is
implementation-defined territory the profile records and nothing
depends on — it is arithmetic here, matching both hosts. -/
def shrOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b < 0 then .ub (.shiftCountNegative b)
  else if b ≥ (t.bits : Int) then .ub (.shiftCountTooLarge b t.bits)
  else close ">>" t (Int.fdiv a ((2 : Int) ^ b.toNat))

/-- Integer conversion. **Always defined**, both directions: to unsigned
by modulo since C89, to signed by two's-complement wrap since C23
§6.3.1.3. Under C17 the second was implementation-defined, which is why
the `-std=c23` pin is load-bearing rather than a formality — `VM_VAL`
(sunfish.c L652) depends on it for the move ordering. -/
def convert (to : IntTy) (v : Int) : CVal := .int to (to.wrap v)

/-! ## Gates

The boundary cases `docs/c-semantics-design.md` §7 names for this inch.
They are the decision, executed. -/

-- unsigned WRAPS: UINT_MAX + 1 = 0, defined
#guard mulOp IntTy.uint 1 1 == .ok (.int IntTy.uint 1)
#guard addOp IntTy.uint 4294967295 1 == .ok (.int IntTy.uint 0)
#guard subOp IntTy.uint 0 1 == .ok (.int IntTy.uint 4294967295)

-- ...and the 64-bit wrap `mix64` actually performs
#guard (mulOp IntTy.ulong 0x9e3779b97f4a7c15 0xff51afd7ed558ccd).isOk

-- signed REFUSES: INT_MAX + 1 is undefined, not wrapped
#guard addOp IntTy.int_ 2147483647 1 == .ub (.signedOverflow "+" IntTy.int_ 2147483648)
#guard subOp IntTy.int_ (-2147483648) 1 == .ub (.signedOverflow "-" IntTy.int_ (-2147483649))
#guard !(mulOp IntTy.int_ 2147483647 2).isOk
#guard !(negOp IntTy.int_ (-2147483648)).isOk
-- ...but stays quiet inside the range
#guard addOp IntTy.int_ 2147483646 1 == .ok (.int IntTy.int_ 2147483647)

-- division: both UB arms, and truncation toward zero
#guard divOp IntTy.int_ 1 0 == .ub (.divideByZero "/")
#guard modOp IntTy.int_ 1 0 == .ub (.divideByZero "%")
#guard divOp IntTy.int_ (-2147483648) (-1) == .ub .divideOverflow
#guard divOp IntTy.int_ (-7) 2 == .ok (.int IntTy.int_ (-3))   -- C truncates; Lean's / would floor to -4
#guard modOp IntTy.int_ (-7) 2 == .ok (.int IntTy.int_ (-1))   -- sign of the dividend

-- shifts: the four distinct causes
#guard shlOp IntTy.int_ 1 32 == .ub (.shiftCountTooLarge 32 32)
#guard shlOp IntTy.int_ 1 (-1) == .ub (.shiftCountNegative (-1))
#guard shlOp IntTy.int_ (-1) 1 == .ub (.shiftNegativeOperand (-1))
#guard !(shlOp IntTy.int_ 2147483647 1).isOk
#guard shlOp IntTy.int_ 1 12 == .ok (.int IntTy.int_ 4096)      -- `1 << 12`, sunfish.c L411
#guard shlOp IntTy.uint 1 31 == .ok (.int IntTy.uint 2147483648)

-- conversion is ALWAYS defined, both directions
#guard convert IntTy.int_ 0x80000000 == .int IntTy.int_ (-2147483648)  -- C23 §6.3.1.3; VM_VAL
#guard convert IntTy.uint (-1) == .int IntTy.uint 4294967295           -- since C89
#guard convert IntTy.char_ 200 == .int IntTy.char_ (-56)               -- signed char, per the profile
#guard convert IntTy.uchar (-56) == .int IntTy.uchar 200

-- the range invariant the whole model rests on
#guard IntTy.int_.minVal == -2147483648 && IntTy.int_.maxVal == 2147483647
#guard IntTy.uint.maxVal == 4294967295 && IntTy.uint.minVal == 0
#guard IntTy.char_.minVal == -128 && IntTy.char_.maxVal == 127
#guard IntTy.ulong.maxVal == 18446744073709551615

end LeanModels.C.C23
