import LeanModels.Core.Basic

/-!
# §6.2.5 / §6.2.6 / §6.3.1 — values and integer arithmetic — M2 inch 1

Fixed-width integer values and the arithmetic on them, per
`docs/c-semantics-design.md` §1. **This file has no world, no memory and
no interpreter**: it is the value layer alone, so the one decision that
cannot be retrofitted can be landed and gated before anything is built on
it.

**Every rule below cites C23 (N3220) by clause and paragraph, and every
refusal names its Annex J.2 index.** The convention, and the layout law
that puts this file where the standard puts types and conversions, is
`docs/c23-spec-mirror.md`. N3220 is the freely available final working
draft; its numbering is the published standard's, and this repository
paraphrases and cites rather than transcribing.

**Warning to anyone carrying a citation in from C17: §6.5 was
RENUMBERED.** A new §6.5.1 "General" shifts all seventeen operator
subclauses down by one, so division is §6.5.6 (C17 §6.5.5) and shifts are
§6.5.8 (C17 §6.5.7). The full table is `docs/c23-spec-mirror.md` §4.2.

Citations to a SUPERSEDED edition always carry the edition tag
immediately before the section sign (`C17 §x.y.z`), never bare. An
untagged `§` in this namespace is C23 (N3220) by
construction, so a scanner can classify every citation without parsing
the prose around it.

**THE DECISION THIS FILE EXISTS FOR: unsigned WRAPS, signed REFUSES —
and the corpus needs both in adjacent operands.** Measured
(`docs/c-tier-charter.md` §2.2): `mix64` (sunfish.c L191-195) is
`x *= 0xff51afd7ed558ccdULL`, deliberate unsigned wraparound that C
DEFINES, while the same file's 327 overflow-capable signed sites are
undefined at the boundary and must refuse. A model that blurred the two
would be wrong about the corpus's hottest sort key.

The widths below are the ones the ABSTRACT profile
(`docs/c-profile.json`) records — 8 facts, satisfied by both development
hosts and checkable on any third by `harness/c_profile_probe.py --check`.

**They are hand-transcribed literals, and the profile is their CITATION
rather than their SOURCE.** Nothing generated `⟨true, 32⟩` from the JSON,
and until this landing nothing compared the two: `--check` gates a HOST
against the JSON via clang, and never reads a Lean file. That gap is now
closed by `harness/c_profile_probe.py --check-lean`, which parses these
`IntTy` definitions and fails loudly if a width here disagrees with the
profile fact it claims to follow. The claim is still a transcription; it
is simply a CHECKED one.

The stored value is always the MATHEMATICAL integer, in range for its
type. That invariant is what makes "did this overflow?" decidable rather
than conventional, and every rule below re-establishes it.
-/

namespace LeanModels.C.C23

/-! ## §6.2.5 Types -/

/-- A C integer type: signedness and width in bits.

C23 (N3220) §6.2.5p4-p9: the standard signed integer types and their
corresponding unsigned types. This surface carries the pair
(signedness, width) because §6.2.6.2 makes width and signedness the only
things the value rules depend on.

`char`'s signedness is a PROFILE fact — `char_signed`, answering
**`J.3.5(5)`** ("which of `signed char` or `unsigned char` has the same
range, representation and behavior as plain `char`", §6.2.5, §6.3.1.1).
It is depended on because `CLS[(int)p->b[j]]` indexes a 128-entry table
by a board byte. -/
structure IntTy where
  signed : Bool
  bits : Nat
deriving Repr, Inhabited, BEq, DecidableEq

namespace IntTy

/-- The profile's widths (`docs/c-profile.json`: `char_bit_8` answering
**`J.3.5(1)`**, and `int_32`/`long_64` answering **`J.3.14(1)`** — the
values of the `<limits.h>`/`<stdint.h>` macros; C23's J.3.6 has no entry
for integer SIZES at all). The corpus's 10 integer types collapse onto
these. -/
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

/-- C23 §6.2.6.2p2-p3 with §6.2.6.2p6 NOTE 2: a signed type's minimum is
`-2^(N-1)` because **C23 mandates two's complement** — the one place the
`-std=c23` pin is genuinely load-bearing for this file, since C17
permitted sign-magnitude and ones' complement as well. The auditable
trace of the mandate is that C17's J.3 integers list had five entries and
C23's `J.3.6` has four: the deleted one is the sign-representation item.

**This is THE edition-sensitive definition in this file** — 1 of 11 in
the value layer. `docs/family-architecture.md` §1.3 previously nominated
`convert` for that role; `convert` is implementation-defined in every
edition and pinned by the profile, whereas `minVal`'s `-2^(N-1)` is
simply WRONG for two of the three representations C17 permitted. Both
lanes verified the swap against the drafts before propagating it. -/
def minVal (t : IntTy) : Int :=
  if t.signed then -((2 : Int) ^ (t.bits - 1)) else 0

def maxVal (t : IntTy) : Int :=
  if t.signed then (2 : Int) ^ (t.bits - 1) - 1 else (2 : Int) ^ t.bits - 1

/-- Is `v` representable in `t`? -/
def inRange (t : IntTy) (v : Int) : Bool :=
  t.minVal ≤ v && v ≤ t.maxVal

/-- Reduce into range modulo `2^bits`, two's complement.

C23 §6.3.1.3p2: conversion TO an unsigned type is defined as reduction
modulo `2^N`, and has been since C89. That direction needs no profile
fact and is not in Annex J at all.

The SIGNED direction is a different question and this function is not the
place it is answered — see `convert`. And neither direction is how signed
arithmetic OVERFLOW behaves: that refuses (`close`). -/
def wrap (t : IntTy) (v : Int) : Int :=
  let m := t.modulus
  let r := v % m
  let r := if r < 0 then r + m else r      -- Int.emod can be negative
  if t.signed && r > t.maxVal then r - m else r

end IntTy

/-! ## Undefined behavior, as a named cause -/

/-- The UB classes this layer can raise. Each is a REFUSAL, never a
value, and — per `docs/c-semantics-design.md` §3.1 — **it never
retires: it is the product.**

Every constructor names its **Annex J.2 index**. In C23 J.2 is a NUMBERED
list, entries `(1)`-`(221)`; in C17 and C11 it was unnumbered bullets, so
`J.2(35)` is a citation form this version of the standard made possible.
The index is the checklist coordinate and the clause is where the rule
lives — both are given because Annex J is informative and, in at least
one place, wrong (`docs/c23-spec-mirror.md` §3.3). -/
inductive UB where
  /-- **`J.2(35)`**, §6.5.1p5: an exceptional condition occurs during the
  evaluation of an expression — the result is not in the range of
  representable values for its type. (C17 §6.5p5.) -/
  | signedOverflow (op : String) (ty : IntTy) (v : Int)
  /-- **`J.2(41)`**, §6.5.6p6: the second operand of `/` or `%` is zero. -/
  | divideByZero (op : String)
  /-- **`J.2(35)`**, §6.5.1p5 again, reached through §6.5.6p6's remark
  that `INT_MIN / -1` is not representable. A DISTINCT constructor
  because the two arms retire the same way but diagnose differently. -/
  | divideOverflow            -- `INT_MIN / -1`: the quotient is unrepresentable
  /-- **`J.2(48)`**, §6.5.8p3: shifted by an amount ≥ the width of the
  promoted left operand. -/
  | shiftCountTooLarge (count : Int) (bits : Nat)
  /-- **`J.2(48)`**, §6.5.8p3: shifted by a negative amount. -/
  | shiftCountNegative (count : Int)
  /-- **`J.2(49)`**, §6.5.8p4: `<<` whose promoted left operand has
  signed type and negative value. -/
  | shiftNegativeOperand (v : Int)
  /-- **`J.2(49)`**, §6.5.8p4: `<<` whose result is not representable in
  the promoted signed type. -/
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

/-! ### §6.2.5p20 — pointer values

A pointer is a VALUE, so it lives here rather than in the memory model.
`docs/c-semantics-design.md` §1.1 always said `CVal` had three
constructors; inch 2 built the object store first and inch 3 is the first
consumer that must actually *produce* a pointer (array-to-pointer decay,
405 sites), so this is where the constructor arrives. -/

/-- The identity of an object. An index into the memory model's store,
but NEVER an address: nothing converts it to an integer, which is what
keeps provenance un-loseable. Measured: the corpus has zero
integer↔pointer casts. -/
abbrev ObjId := Nat

/-- A pointer value: which object, and how many bytes into it.

C23 §6.3.2.3p3: a null pointer constant converts to a null pointer, which
"is guaranteed to compare unequal to a pointer to any object or
function". Here `obj = none` **IS** the null pointer — not offset 0 of a
distinguished object, so no arithmetic can accidentally reach one. -/
structure Ptr where
  obj : Option ObjId
  off : Int
deriving Repr, Inhabited, BEq, DecidableEq

namespace Ptr

/-- C23 §6.3.2.3p3: the null pointer. -/
def null : Ptr := ⟨none, 0⟩

def isNull (p : Ptr) : Bool := p.obj.isNone

/-- C23 §6.5.4.2p3 and §6.3.2.1p3 produce the SAME value for an object:
`&x` and the decay of `x` both designate its first byte. One definition
with two spellings, because the standard defines them that way
(§6.5.4.2p3's `&*p == p` identity) and because pretending they differ
would double every lemma about them. -/
def toObject (o : ObjId) : Ptr := ⟨some o, 0⟩

end Ptr

/-- A C value. `undef` is an indeterminate value that reached a use,
which every consumer refuses. -/
inductive CVal where
  | int (ty : IntTy) (v : Int)
  | ptr (p : Ptr)
  | undef
deriving Repr, Inhabited, BEq

/-! ## §6.5.6-§6.5.8 Arithmetic — where the split lives

Each operation computes the MATHEMATICAL result first, then decides by
signedness: unsigned reduces modulo (§6.2.5p11), signed refuses out of
range (§6.5.1p5). Additive and multiplicative operators are §6.5.6 and
§6.5.7; shifts are §6.5.8. -/

/-- Close a mathematical result into `t`: wrap if unsigned, refuse if
signed and out of range. **This function IS the decision.**

C23 §6.5.1p5 — "if an exceptional condition occurs during the evaluation
of an expression (that is, if the result is not mathematically defined or
not in the range of representable values for its type), the behavior is
undefined" — is the hook the signed arm hangs on (**`J.2(35)`**). The
unsigned arm never reaches it: §6.2.5p11 makes unsigned arithmetic
modular by definition, so no exceptional condition arises and there is
nothing to refuse.

**The asymmetry is the standard's, not a modeling choice.** -/
def close (op : String) (t : IntTy) (v : Int) : CRes CVal :=
  if t.inRange v then .ok (.int t v)
  else if t.signed then .ub (.signedOverflow op t v)
  else .ok (.int t (t.wrap v))

def addOp (t : IntTy) (a b : Int) : CRes CVal := close "+" t (a + b)
def subOp (t : IntTy) (a b : Int) : CRes CVal := close "-" t (a - b)
def mulOp (t : IntTy) (a b : Int) : CRes CVal := close "*" t (a * b)
def negOp (t : IntTy) (a : Int) : CRes CVal := close "-" t (-a)

/-- C23 §6.5.6p7: the quotient is "the algebraic quotient with any
fractional part discarded" — footnote 104 calls this *truncation toward
zero*. That is `Int.tdiv`, NOT Lean's `/` on `Int`, which FLOORS.

§6.5.6p6: a zero second operand is undefined (**`J.2(41)`**), and the
same paragraph is why `INT_MIN / -1` refuses — its quotient is not
representable, so §6.5.1p5's exceptional condition applies
(**`J.2(35)`**).

Getting the truncation wrong is the `pyfloordiv` divergence class the
ctwin README names as #1, met here from the C side.

*(Citation note: C17 §6.5.5. C23's inserted §6.5.1 "General" shifted
it.)* -/
def divOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b == 0 then .ub (.divideByZero "/")
  else if t.signed && a == t.minVal && b == -1 then .ub .divideOverflow
  else close "/" t (Int.tdiv a b)

/-- C23 §6.5.6p7: the remainder pairs with the truncating quotient, so
`(a/b)*b + a%b == a` and `a % b` takes the sign of `a`. Same two UB arms
as `divOp` — **`J.2(41)`** for the zero divisor, **`J.2(35)`** for
`INT_MIN % -1`. -/
def modOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b == 0 then .ub (.divideByZero "%")
  else if t.signed && a == t.minVal && b == -1 then .ub .divideOverflow
  else close "%" t (Int.tmod a b)

/-- `<<`, C23 §6.5.8 (C17 §6.5.7).

§6.5.8p3 — the count must be non-negative and less than the width of the
promoted left operand, else undefined (**`J.2(48)`**).
§6.5.8p4 — if the promoted left operand has signed type, its value must
be non-negative AND the result must be representable, else undefined
(**`J.2(49)`**).

All four failures are distinct causes, because a refusal a human cannot
act on is a refusal that has not done its job. -/
def shlOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b < 0 then .ub (.shiftCountNegative b)
  else if b ≥ (t.bits : Int) then .ub (.shiftCountTooLarge b t.bits)
  else if t.signed && a < 0 then .ub (.shiftNegativeOperand a)
  else
    let r := a * (2 : Int) ^ b.toNat
    if t.signed && !t.inRange r then .ub (.shiftOverflow a b t)
    else close "<<" t r

/-- `>>`, C23 §6.5.8. The count is constrained exactly as for `<<`
(§6.5.8p3, **`J.2(48)`**).

§6.5.8p5: on a non-negative signed value, or an unsigned one, the result
is the quotient by `2^count`. **On a NEGATIVE signed value the result is
implementation-defined** — not undefined — so it is a profile question,
not a refusal. The profile answers it with `arithmetic_right_shift`,
whose Annex J home is **`J.3.6(4)`** ("the results of some bitwise
operations on signed integers"), a catch-all that does not name shifts;
§6.5.8p5 is the precise citation.

The corpus has **zero signed right shifts** (measured: all 6 `>>` sites
are on `uint64_t`), so the fact is recorded and deliberately NOT depended
on. `Int.fdiv` floors, which is the arithmetic-shift answer both hosts
give. -/
def shrOp (t : IntTy) (a b : Int) : CRes CVal :=
  if b < 0 then .ub (.shiftCountNegative b)
  else if b ≥ (t.bits : Int) then .ub (.shiftCountTooLarge b t.bits)
  else close ">>" t (Int.fdiv a ((2 : Int) ^ b.toNat))

/-! ### §6.5.11-§6.5.13 — the bitwise operators

`&`, `^` and `|` act on the OBJECT REPRESENTATION, so they are defined
through the unsigned residue and closed back into the type. Under C23
this is fully determined: §6.2.6.2p2 mandates two's complement, so a
signed operand has exactly one representation. *(`J.3.6(4)` — "the
results of some bitwise operations on signed integers" — is the
implementation-defined catch-all, and the two's-complement mandate is
what empties it for these three. It still covers `>>` of a negative
value, which is why `shrOp` cites the profile.)*

Measured: 35 sites — `&` 13, `|` 15, `^` 7. No arm can overflow, because
an N-bit pattern combined with an N-bit pattern is an N-bit pattern. -/

/-- The value's object representation, as a natural number. -/
def IntTy.residue (t : IntTy) (v : Int) : Nat :=
  let m := t.modulus
  (((v % m) + m) % m).toNat

def bitAnd (t : IntTy) (a b : Int) : Int := t.wrap ((t.residue a &&& t.residue b : Nat))
def bitOr (t : IntTy) (a b : Int) : Int := t.wrap ((t.residue a ||| t.residue b : Nat))
def bitXor (t : IntTy) (a b : Int) : Int := t.wrap ((t.residue a ^^^ t.residue b : Nat))

/-- Integer conversion, C23 §6.3.1.3.

**§6.3.1.3p2 — to an unsigned type**: defined as reduction modulo `2^N`,
and has been since C89. Not in Annex J; nothing to pin.

**§6.3.1.3p3 — to a signed type, when the value is not representable**:
"either the result is implementation-defined or an implementation-defined
signal is raised." This is **`J.3.6(3)`**.

> **CORRECTED at M2 inch 2.** This docstring previously said C23
> *mandates* the two's-complement result and that the `-std=c23` pin was
> therefore load-bearing here. **It does not.** N3220 §6.3.1.3p3 is
> word-for-word identical to C11 and C17, and `J.3.6(3)` still lists the
> behavior as implementation-defined. What C23 *did* change is signed
> REPRESENTATION (§6.2.6.2p6 NOTE 2, and see `minVal`) — representation
> mandated, conversion rule untouched.

So the wrap below is **not the standard's answer; it is the profile's.**
The fact is `uint_to_int_wraps` in `docs/c-profile.json`, expression
`(int)0x80000000u == INT_MIN`, measured true on both development hosts
and marked `depended_on` — because `VM_VAL` (sunfish.c L652) needs it for
the move ordering. A third host that raised a signal instead would fail
`harness/c_profile_probe.py --check`, loudly, which is exactly the
service the profile exists to provide and which a false appeal to the
standard would have silently withdrawn.

Modeling the signal arm is not owed: no host in the profile raises one,
and inventing an unraised signal would be inventing behavior. -/
def convert (to : IntTy) (v : Int) : CVal := .int to (to.wrap v)

/-! ## Gates

The boundary cases `docs/c-semantics-design.md` §7 names for this inch.
They are the decision, executed.

Each block names the clause it gates, so a reader holding N3220 can check
the gate against the paragraph rather than against this file's prose. -/

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

-- conversion TO UNSIGNED is defined by the standard (§6.3.1.3p2, since C89)
#guard convert IntTy.uint (-1) == .int IntTy.uint 4294967295
#guard convert IntTy.uchar (-56) == .int IntTy.uchar 200

-- conversion TO SIGNED out of range is IMPLEMENTATION-DEFINED (§6.3.1.3p3,
-- J.3.6(3)) and these two gates are the PROFILE's answer, not the standard's.
-- `uint_to_int_wraps` in docs/c-profile.json: `(int)0x80000000u == INT_MIN`,
-- measured true on both hosts and depended on by VM_VAL (sunfish.c L652).
#guard convert IntTy.int_ 0x80000000 == .int IntTy.int_ (-2147483648)
#guard convert IntTy.char_ 200 == .int IntTy.char_ (-56)               -- char_signed, J.3.5(5)

-- bitwise: on the representation, and closed back into the type
#guard bitAnd IntTy.int_ 12 10 == 8            -- 1100 & 1010 = 1000
#guard bitOr IntTy.int_ 12 10 == 14
#guard bitXor IntTy.int_ 12 10 == 6
#guard bitAnd IntTy.int_ (-1) 255 == 255       -- -1 is all-ones under two's complement
#guard bitXor IntTy.int_ (-1) (-1) == 0
#guard bitOr IntTy.uint 0 4294967295 == 4294967295
#guard bitAnd IntTy.char_ (-1) 255 == -1       -- 8-bit: all-ones closes back to -1

-- the range invariant the whole model rests on
#guard IntTy.int_.minVal == -2147483648 && IntTy.int_.maxVal == 2147483647
#guard IntTy.uint.maxVal == 4294967295 && IntTy.uint.minVal == 0
#guard IntTy.char_.minVal == -128 && IntTy.char_.maxVal == 127
#guard IntTy.ulong.maxVal == 18446744073709551615

end LeanModels.C.C23
