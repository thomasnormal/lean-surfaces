import LeanModels.C.Ast
import LeanModels.C.C23.Value

/-!
# §6.2.4 / §6.2.6.1 / §6.3.2 / §6.5.3-§6.5.4 — objects, pointers, bytes — M2 inch 2

The memory model: what an object is, what a pointer IS, and the three
structural refusals every access goes through. **No interpreter, no
world, no fuel** — every operation here is a PURE function over `Mem`,
which is what lets inch 3 lift them into the monad stack
(`docs/c-semantics-design.md` §4.1a) without rewriting one of them.

Citations are C23 (N3220) by clause and paragraph; refusals name their
Annex J.2 index. The convention is `docs/c23-spec-mirror.md`.

## The decision this file exists for

**A pointer is `(object, offset)` with provenance. There is no integer
address to lose provenance to.** Two measurements force it and neither
can be retrofitted:

* **31 sites take `&` of an automatic object** and 20 take `&` of a
  subobject, so a C local cannot be an environment binding the way the
  Python tier's is. *(The charter published 86 for years; the guard that
  produced it could not see storage duration. §L72.)*
* **`realloc` MOVES the transposition table** (sunfish.c L453-454, on the
  search path), so the corpus exercises PROVENANCE TRANSFER in its
  hottest data structure — old object dies, a fresh object receives the
  bytes. `Addr := Nat` cannot express that; `(obj, off)` can.

## What the census changed about the shape

Inch 2's own census asked which operations actually make and use
pointers, and the answer reordered the file:

| produces | sites | | consumes | sites |
| --- | ---: | --- | --- | ---: |
| **array-to-pointer decay** (§6.3.2.1p3) | **405** | | lvalue conversion (§6.3.2.1p2) | 1837 |
| function-to-pointer decay | 307 | | `p->f` (§6.5.3.4) | **226** |
| `&` (§6.5.4.2p3) | 106 | | `a[i]` (§6.5.3.2) | 328 |
| null pointer constant (§6.3.2.3p3) | 110 | | `x.f` | 184 |
| `void*` ↔ `T*` | 52 | | `*p` (§6.5.4.2p4) | **24** |

**Decay outnumbers `&` four to one, and `->` outnumbers `*` nine to
one.** So `decay` and `member` are stated first and gated hardest; `*`
gets the same treatment because the standard defines it that way, not
because the corpus leans on it.
-/

namespace LeanModels.C.C23

open LeanModels.C (CType)

/-! ## §6.2.4 Storage durations of objects -/

/-- C23 §6.2.4: how long an object lives.

`static` (p3) — the whole program execution. `automatic` (p6) — "from
entry into the block with which it is associated until execution of that
block ends in any way". `allocated` (§7.24.3p1) — "from the allocation
until the deallocation".

The three are distinguished because their INDETERMINATE reads carry
different Annex J entries: `J.2(11)` for automatic, `J.2(185)` for
`malloc`ed. Pooling them would make the scoreboard unreadable. -/
inductive Duration where
  | static_
  | automatic
  | allocated
deriving Repr, Inhabited, BEq, DecidableEq

/-! ## §6.3.2.3 Pointers

`ObjId`, `Ptr`, `Ptr.null` and `Ptr.toObject` now live in `Value.lean`: a
pointer is a VALUE, and inch 3 is the first consumer that must produce
one. `docs/c-semantics-design.md` §1.1 always said so. -/

/-! ## §6.2.6.1 Representations of types — the byte lattice -/

/-- One byte of an object's representation.

C23 §6.2.6.1p2-p4 gives every object a representation as a sequence of
`CHAR_BIT`-bit bytes; the lattice adds the two states the standard talks
about but a concrete byte cannot express.

Per-BYTE and not per-object, because `setup_fen` declares `Pos p;` then
`memcpy(p.b, board, 120)` (sunfish.c L1130), leaving `p.score`, `p.ep`,
`p.kp` and `p.h` indeterminate while `p.b` is fully determined. A model
that refused any read from a partly-initialized object would refuse the
corpus; one that allowed it would invent values. -/
inductive CByte where
  /-- A determinate byte value. -/
  | conc (b : UInt8)
  /-- Byte `k` of some pointer's representation. Kept whole so that a
  torn read — part of a pointer, or a pointer read as an integer — is
  DETECTABLE rather than plausible (§6.2.6.1p5, `J.2(12)`). -/
  | ptrByte (p : Ptr) (k : Nat)
  /-- Indeterminate. C23 §6.2.6.1p5 and §6.7.11: an object with no
  initializer has an indeterminate representation. -/
  | indet
deriving Repr, Inhabited, BEq

/-! ## The refusal causes

`docs/c23-goal.md` §3.1 fixed three causes that must never be pooled,
because they retire on completely different schedules. This file's faults
are all of the middle kind — **UB, which never retires: it is the
product** — but the `Cause` projection is defined here so the scorer at
inch 6 reads it off the refusal rather than re-deriving it. -/

/-- The three REFUSAL causes of `docs/c23-goal.md` §3.1. -/
inductive Cause where
  /-- Undefined behavior, refused loudly. **Never retires.** -/
  | ub
  /-- A construct outside the tier's vocabulary. Retires by climbing a rung. -/
  | unsupported
  /-- A library function outside the modeled slice. Retires by widening it. -/
  | libc
deriving Repr, Inhabited, BEq, DecidableEq

/-- The memory model's undefined-behavior classes.

Each names its **Annex J.2 index** — C23 numbers J.2 `(1)`-`(221)`, which
C17 did not — and the normative clause where the rule actually lives.
Both, because Annex J is informative and in one place demonstrably wrong
(`docs/c23-spec-mirror.md` §3.3). -/
inductive MemFault where
  /-- **`J.2(39)`**, §6.5.4.2p4: the operand of unary `*` has an invalid
  value. (Annex J says "invalid value", never "null".) -/
  | nullDeref (off : Int)
  /-- **`J.2(9)`/`J.2(10)`**, §6.2.4p2: an object is referred to outside
  its lifetime, or the value of a pointer to it is used. The `Duration`
  says which story it is — a dead automatic, or freed storage. -/
  | deadObject (o : ObjId) (dur : Duration)
  /-- **`J.2(46)`**, §6.5.3.2 / **`J.2(43)`**, §6.5.7p9: an access or a
  formed pointer leaves the object. Structural here: the offset is
  checked against the size, so no sanitizer is needed to see it. -/
  | outOfBounds (o : ObjId) (off : Int) (want : Nat) (size : Nat)
  /-- **`J.2(11)`**, §6.2.4: the value of an object with AUTOMATIC
  storage duration is used while its representation is indeterminate. -/
  | indetAutomatic (o : ObjId) (off : Nat)
  /-- **`J.2(185)`**, §7.24.3.6p2: the value of a `malloc`ed object is
  used before it is written. A DISTINCT entry from `J.2(11)` — the
  annex separates them and so does this model. -/
  | indetAllocated (o : ObjId) (off : Nat)
  /-- **`J.2(12)`**, §6.2.6.1p5: a non-value representation is read by an
  lvalue expression that does not have character type — here, a torn
  pointer, or a pointer representation read as an integer. -/
  | nonValueRepresentation (o : ObjId) (off : Nat)
  /-- **`J.2(184)`**, §7.24.3.3 / §7.24.3.7: `free` or `realloc` given a
  pointer that no allocation returned, or one already deallocated. -/
  | freeUnmatched (p : Ptr)
  /-- **NO J.2 ENTRY EXISTS.** §7.24.3.7p3 — "or if the size is zero, the
  behavior is undefined" — is new in C23, and Annex J was not updated to
  match. Verified by exhaustive search of all 221 entries. The gap is
  carried in the type, not in a comment: `j2` returns `none` here. -/
  | reallocZero (p : Ptr)
  /-- **`J.2(36)`**, §6.5.1p6-p7: an object's stored value is accessed by
  an lvalue of a type that is not allowable for its effective type.
  Measured: the corpus has ZERO punning casts and ZERO unions, which is
  exactly the condition under which this wall is cheap to install
  correctly and expensive to install later — and no sanitizer on either
  development host detects a strict-aliasing violation, so without it the
  project has no instrument that would ever notice one. -/
  | effectiveType (o : ObjId) (off : Nat) (used : CType) (eff : CType)
  /-- **`J.2(45)`**, §6.5.9p6: pointers into DIFFERENT objects compared
  with a relational operator. Note the asymmetry with `==`, which
  §6.5.10p7 leaves fully DEFINED across unrelated objects — same clause
  family, opposite verdicts. -/
  | relationalAcrossObjects (a b : Ptr)
deriving Repr, Inhabited, BEq

namespace MemFault

/-- The Annex J.2 index for this fault, when one exists.

**`none` is a finding, not a hole.** `reallocZero` is undefined by
§7.24.3.7p3 and has no annex entry at all; returning an `Option` keeps
that gap where a reader will trip over it instead of where a comment
would be skimmed. -/
def j2 : MemFault → Option String
  | .nullDeref _ => some "J.2(39)"
  | .deadObject _ .allocated => some "J.2(10)"
  | .deadObject _ _ => some "J.2(9)"
  | .outOfBounds .. => some "J.2(46)"
  | .indetAutomatic .. => some "J.2(11)"
  | .indetAllocated .. => some "J.2(185)"
  | .nonValueRepresentation .. => some "J.2(12)"
  | .freeUnmatched _ => some "J.2(184)"
  | .reallocZero _ => none                      -- §7.24.3.7p3; the annex has none
  | .effectiveType .. => some "J.2(36)"
  | .relationalAcrossObjects .. => some "J.2(45)"

/-- The normative clause, which every fault HAS even where J.2 does not. -/
def clause : MemFault → String
  | .nullDeref _ => "6.5.4.2p4"
  | .deadObject _ .allocated => "7.24.3"
  | .deadObject _ _ => "6.2.4p2"
  | .outOfBounds .. => "6.5.7p9"
  | .indetAutomatic .. => "6.2.4"
  | .indetAllocated .. => "7.24.3.6p2"
  | .nonValueRepresentation .. => "6.2.6.1p5"
  | .freeUnmatched _ => "7.24.3.3"
  | .reallocZero _ => "7.24.3.7p3"
  | .effectiveType .. => "6.5.1p6"
  | .relationalAcrossObjects .. => "6.5.9p6"

end MemFault

/-- A refusal that rides in `ExceptT`, with its cause kept structural.

Two of `docs/c23-goal.md` §3.1's three causes live here, with the UB one
split by layer — the value rules (`Value.lean`) and the memory rules
(this file) both produce undefined behavior and both must stay separable
for diagnosis while pooling identically for scoring.

**The third cause, `unsupported`, is NOT here: it lives in `Halt`**, per
the family ruling at `docs/family-architecture.md` §3.4. Uncatchability
belongs to the definition rather than to a per-language proof
obligation. -/
inductive Refusal where
  | valueUB (u : UB)
  | memUB (f : MemFault)
  | libc (name : String)
deriving Repr, Inhabited, BEq

namespace Refusal

/-- Which of the three schedules this refusal retires on. **UB never
retires: it is the product.** -/
def cause : Refusal → Cause
  | .valueUB _ | .memUB _ => .ub
  | .libc _ => .libc

/-- The Annex J.2 index, where the refusal is UB and the annex has one. -/
def j2 : Refusal → Option String
  | .memUB f => f.j2
  | .valueUB u => some (match u with
      | .signedOverflow .. => "J.2(35)"
      | .divideByZero _ => "J.2(41)"
      | .divideOverflow => "J.2(35)"
      | .shiftCountTooLarge .. | .shiftCountNegative _ => "J.2(48)"
      | .shiftNegativeOperand _ | .shiftOverflow .. => "J.2(49)")
  | .libc _ => none

end Refusal

/-- The result of a memory operation. `Except` rather than a bespoke sum,
because inch 3's stack is `ExceptT Refusal (StateT CWorld Halt)` — the
STATE-RETAINING order, which the `mvcgen` pilot proved by `rfl` is the
one that does not discard the world on a raise — and an operation written
against `Except Refusal` today needs no adapter tomorrow
(`docs/c-semantics-design.md` §4.1a).

These operations take and return `Mem` explicitly rather than living in a
state monad, which is what makes the lift a lift rather than a rewrite. -/
abbrev MRes (α : Type) := Except Refusal α

/-- Core Lean gives `Except` no `BEq`, and every gate in
`Examples/c/sunfish/memory.lean` compares one. SCOPED, so it does not
leak into the other lanes: it is generic plumbing, and lifting it to
shared substrate is the architecture lane's call once a second consumer
exists — parking a global instance here to serve one lane is what the
lift-don't-copy law forbids. -/
scoped instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-! ## Objects and memory -/

/-- One object: its size in bytes, its lifetime, and its representation.

`effTy` is per-byte per C23 §6.5.1p6 — "the effective type of an object
for an access to its stored value is the declared type of the object, if
any". `none` is the *no declared type* case, which is exactly allocated
storage (footnote 84), and a store through a non-character lvalue is what
gives it one. -/
structure CObj where
  dur : Duration
  /-- Is the object inside its lifetime? A dead object is NOT removed —
  it becomes a tombstone, so a pointer to it stays a well-formed VALUE
  and `J.2(10)` is detectable instead of being a segfault. -/
  live : Bool
  bytes : List CByte
  effTy : Option CType
deriving Repr, Inhabited, BEq

/-- The object's size in bytes. **Computed, not carried.** An object that
stored its size beside its representation could disagree with itself, and
every lemma below would need a well-formedness side condition saying it
does not. `List.length` is that invariant, discharged by construction. -/
def CObj.size (c : CObj) : Nat := c.bytes.length

/-- The object store. Objects are only ever appended, never removed, so
an `ObjId` is stable for the whole execution and provenance never
dangles into a reused slot. -/
structure Mem where
  objs : List CObj
deriving Repr, Inhabited, BEq

namespace Mem

def empty : Mem := ⟨[]⟩

def get? (m : Mem) (o : ObjId) : Option CObj := m.objs[o]?

def count (m : Mem) : Nat := m.objs.length

/-- C23 §6.2.4 / §6.7.11: create an object whose representation is
INDETERMINATE. Returns the new memory and the object's id.

Every automatic object is created this way on block entry — which is the
locals-are-objects decision, executed. -/
def alloc (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) : Mem × ObjId :=
  (⟨m.objs ++ [⟨dur, true, List.replicate size .indet, ty⟩]⟩, m.objs.length)

/-- `calloc`'s object (§7.24.3.2p2): all bits zero, hence determinate. -/
def allocZeroed (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) : Mem × ObjId :=
  (⟨m.objs ++ [⟨dur, true, List.replicate size (.conc 0), ty⟩]⟩, m.objs.length)

/-- C23 §6.2.4p6 / §7.24.3: end an object's lifetime. The object stays in
the store as a tombstone — see `CObj.live`. -/
def kill (m : Mem) (o : ObjId) : Mem :=
  ⟨m.objs.modify o (fun c => { c with live := false })⟩

/-! ### The one place the structural refusals are raised -/

/-- Resolve a pointer to a live object and an in-bounds byte range.

**Every load and every store goes through this**, so C's three structural
undefined behaviors are decided in exactly one function:

* §6.5.4.2p4 — indirection through an invalid value (`J.2(39)`);
* §6.2.4p2 — the object is outside its lifetime (`J.2(9)`/`J.2(10)`);
* §6.5.7p9 — the access leaves the object (`J.2(46)`).

A negative offset fails the same test as an oversized one, so a pointer
walked backwards off its object is caught by the same arm. -/
def resolve (m : Mem) (p : Ptr) (n : Nat) : MRes (ObjId × CObj × Nat) :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o =>
    match m.get? o with
    | none => .error (.memUB (.nullDeref p.off))
    | some c =>
      if !c.live then .error (.memUB (.deadObject o c.dur))
      else if p.off < 0 || p.off + (n : Int) > (c.size : Int) then
        .error (.memUB (.outOfBounds o p.off n c.size))
      else .ok (o, c, p.off.toNat)

/-! ### §6.3.2.1p2 Lvalue conversion — reading bytes out -/

/-- Read `n` bytes of representation. Refuses per `resolve`; does NOT
inspect the bytes, because a `memcpy` of a partly-indeterminate object is
legal (§6.2.6.1p4 permits copying via character type) and only an
INTERPRETATION of those bytes as a value can fail. -/
def loadBytes (m : Mem) (p : Ptr) (n : Nat) : MRes (List CByte) := do
  let (_, c, off) ← m.resolve p n
  return (c.bytes.drop off).take n

/-- Write a byte string. The length is the caller's `n`. -/
def storeBytes (m : Mem) (p : Ptr) (bs : List CByte) : MRes Mem := do
  let (o, c, off) ← m.resolve p bs.length
  let bytes := (c.bytes.take off) ++ bs ++ (c.bytes.drop (off + bs.length))
  return ⟨m.objs.set o { c with bytes := bytes }⟩

/-! ### §6.2.6.2 Integer representation

Byte order is the profile's `little_endian`, measured on both hosts and
**deliberately not depended on**: a store/load round trip is
order-independent, and the corpus's only byte-level view of a multi-byte
object is `pos_seal` hashing the board, whose result is never observable
(`docs/c-profile.md` §4.3). -/

/-- Little-endian digits, `n` of them. -/
def natToBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofNat (v % 256) :: natToBytes n (v / 256)

/-- The inverse reading. -/
def natOfBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * natOfBytes bs

/-- The bytes of `v` at type `t`. The stored value is the mathematical
integer (`Value.lean`'s invariant), so it is reduced into the type's
unsigned residue first — that is what a representation IS. -/
def encodeInt (t : IntTy) (v : Int) : List CByte :=
  let width := t.bits / 8
  let u := (v % t.modulus + t.modulus) % t.modulus
  (natToBytes width u.toNat).map CByte.conc

/-- Interpret bytes as a value of type `t`. Every byte must be `conc`:
an indeterminate byte or a pointer byte is a non-value representation and
the caller refuses (`loadInt`). -/
def decodeInt (t : IntTy) (bs : List CByte) : Option Int :=
  let step := fun (b : CByte) (acc : Option (List UInt8)) =>
    match b, acc with
    | .conc x, some xs => some (x :: xs)
    | _, _ => none
  match bs.foldr step (some []) with
  | none => none
  | some xs => some (t.wrap (natOfBytes xs))

/-! ### The typed accessors -/

/-- Which indeterminate-read fault a duration raises. `J.2(11)` names
AUTOMATIC storage; `J.2(185)` is `malloc`'s own entry. Keeping them apart
is the annex's own distinction, not a refinement of it. -/
def indetFault (dur : Duration) (o : ObjId) (off : Nat) : MemFault :=
  match dur with
  | .allocated => .indetAllocated o off
  | _ => .indetAutomatic o off

/-- Read an integer. C23 §6.3.2.1p2 (lvalue conversion) with
§6.2.6.1p5: three outcomes, and two of them refuse.

* all bytes `conc` → the value they represent;
* any `indet` byte → **`J.2(11)`/`J.2(185)`**, by storage duration;
* any pointer byte → **`J.2(12)`**, a non-value representation read by a
  non-character lvalue.

The corpus has exactly one site where the third could fire and one where
the second could; neither is detectable by any sanitizer on either
development host, which is why the byte lattice is here at all. -/
def loadInt (m : Mem) (p : Ptr) (t : IntTy) : MRes CVal := do
  let width := t.bits / 8
  let (o, c, off) ← m.resolve p width
  let bs := (c.bytes.drop off).take width
  match decodeInt t bs with
  | some v => return .int t v
  | none =>
      if bs.any (· == CByte.indet) then
        .error (.memUB (indetFault c.dur o off))
      else
        .error (.memUB (.nonValueRepresentation o off))

/-- Write an integer. -/
def storeInt (m : Mem) (p : Ptr) (t : IntTy) (v : Int) : MRes Mem :=
  m.storeBytes p (encodeInt t v)

/-- Write a pointer, as `pointer_64`'s eight tagged bytes. Kept whole so
that a partial overwrite makes the remaining bytes UNREADABLE as a
pointer rather than silently valid. -/
def storePtr (m : Mem) (p : Ptr) (q : Ptr) : MRes Mem :=
  m.storeBytes p ((List.range 8).map (CByte.ptrByte q))

/-- Read a pointer: the eight bytes must be one pointer's representation,
in order. Anything else is `J.2(12)` — including a torn pointer, which
no sanitizer on either host detects. -/
def loadPtr (m : Mem) (p : Ptr) : MRes Ptr := do
  let (o, c, off) ← m.resolve p 8
  let bs := (c.bytes.drop off).take 8
  let expected (q : Ptr) := (List.range 8).map (CByte.ptrByte q)
  match bs.head? with
  | some (.ptrByte q 0) => if bs == expected q then return q
                           else .error (.memUB (.nonValueRepresentation o off))
  | _ =>
      if bs.any (· == CByte.indet) then
        .error (.memUB (indetFault c.dur o off))
      else .error (.memUB (.nonValueRepresentation o off))

/-! ## §6.3.2.1p3 / §6.5.3 / §6.5.4 — making and moving pointers

Stated in census order: decay first, because it is 405 of the corpus's
pointer productions to `&`'s 106. -/

/-- **C23 §6.3.2.1p3 — array-to-pointer decay.** An expression of array
type is converted to a pointer to its initial element.

**The corpus's main pointer producer: 405 sites.** It is also why every
one of the 328 subscripts indexes an OBJECT rather than an address. -/
def decay (o : ObjId) : Ptr := Ptr.toObject o

/-- **C23 §6.5.4.2p3 — the address-of operator.** Yields a pointer to its
operand. Measured: 31 automatic, 55 file-scope, 20 subobject.

Definitionally equal to `decay`: §6.5.4.2p3 makes `&*p` and `&a[0]` the
same value as `p` and `a`, and stating them as one definition is what
stops every lemma below from being proved twice. -/
def addrOf (o : ObjId) : Ptr := Ptr.toObject o

/-- **C23 §6.5.3.4 — structure members.** `p->f` is DEFINED as `(*p).f`
(§6.5.3.4p4), so the 226 arrow sites and the 184 dot sites are one
operation with two spellings.

The offset is a parameter: struct layout is implementation-defined
(`J.3.10`), so it belongs to the profile and to the layout inch, not to
this one. -/
def member (p : Ptr) (fieldOff : Nat) : Ptr :=
  { p with off := p.off + (fieldOff : Int) }

/-- **C23 §6.5.7p9 — pointer arithmetic**, and this is a constraint on
FORMING the pointer, not only on using it: the result must point into the
array or **one past its end**, else undefined (`J.2(43)`).

One-past-the-end is admitted here and refused by `resolve` on any access,
which is exactly §6.5.7p9's own split — the value is legal, the
dereference is not. -/
def offsetPtr (m : Mem) (p : Ptr) (elemSize : Nat) (i : Int) : MRes Ptr :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o =>
    match m.get? o with
    | none => .error (.memUB (.nullDeref p.off))
    | some c =>
      let off := p.off + i * (elemSize : Int)
      if off < 0 || off > (c.size : Int) then     -- `=` size is one-past-the-end: legal
        .error (.memUB (.outOfBounds o off elemSize c.size))
      else .ok { p with off := off }

/-- **C23 §6.5.3.2p2 — array subscripting.** `a[i]` is defined to be
`*(a + i)`, so it is `offsetPtr` and nothing else. Stated so the
mirror is visible, not because it computes anything new. -/
def subscript (m : Mem) (p : Ptr) (elemSize : Nat) (i : Int) : MRes Ptr :=
  m.offsetPtr p elemSize i

/-! ### §6.5.9 / §6.5.10 — comparing pointers, and the asymmetry

Two operators from the same clause family give OPPOSITE verdicts on the
same operands, which is the kind of thing a model gets wrong by being
tidy. -/

/-- **C23 §6.5.10p7 — equality.** Comparing pointers into unrelated
objects is fully DEFINED; they simply compare unequal. (The standard even
allows a one-past-the-end pointer to compare equal to a pointer to a
different object that happens to follow it — a case this model cannot
produce, since it has no address to coincide with.) -/
def ptrEq (a b : Ptr) : Bool := a == b

/-- **C23 §6.5.9p6 — relational.** Comparing pointers into DIFFERENT
objects with `<`, `>`, `<=` or `>=` is UNDEFINED — "in all other cases,
the behavior is undefined" (`J.2(45)`).

**The opposite verdict from `ptrEq` on the same operands.** -/
def ptrLt (a b : Ptr) : MRes Bool :=
  match a.obj, b.obj with
  | some x, some y => if x == y then .ok (a.off < b.off)
                      else .error (.memUB (.relationalAcrossObjects a b))
  | _, _ => .error (.memUB (.relationalAcrossObjects a b))

/-! ## §7.24.3 Memory management functions

C23 §7.24.3p1: "The lifetime of an allocated object extends from the
allocation until the deallocation." Note the clause NUMBER — C17's 7.24
is `<string.h>`; C23's is `<stdlib.h>`, so a stale citation retargets
silently instead of failing (`docs/c23-spec-mirror.md` §4.3). -/

/-- §7.24.3.6 `malloc`: indeterminate representation, no declared type. -/
def malloc (m : Mem) (size : Nat) : Mem × Ptr :=
  let (m', o) := m.alloc .allocated size none
  (m', Ptr.toObject o)

/-- §7.24.3.2 `calloc`: all bits zero. -/
def calloc (m : Mem) (n size : Nat) : Mem × Ptr :=
  let (m', o) := m.allocZeroed .allocated (n * size) none
  (m', Ptr.toObject o)

/-- §7.24.3.3 `free`. Refuses a pointer no allocation returned, or one
already freed (**`J.2(184)`**). A null pointer is accepted and does
nothing, per §7.24.3.3p2. -/
def free (m : Mem) (p : Ptr) : MRes Mem :=
  match p.obj with
  | none => .ok m                                  -- §7.24.3.3p2: free(NULL) is a no-op
  | some o =>
    match m.get? o with
    | some c => if c.dur == .allocated && c.live && p.off == 0
                then .ok (m.kill o)
                else .error (.memUB (.freeUnmatched p))
    | none => .error (.memUB (.freeUnmatched p))

/-- §7.24.3.7 `realloc` — **and this is why pointers carry provenance.**

The corpus reallocates the transposition table on the search path
(sunfish.c L453-454), so the old object DIES and a fresh object receives
the copied bytes. Every pointer derived from the old object must stop
working, and here it does: the old id becomes a tombstone and any access
through it raises `J.2(10)`. An `Addr := Nat` model cannot express that
because the new block might reuse the number.

§7.24.3.7p3: a zero size is UNDEFINED in C23 (it was not in C17), and
**Annex J has no entry for it** — so `reallocZero`'s `j2` is `none`. -/
def realloc (m : Mem) (p : Ptr) (size : Nat) : MRes (Mem × Ptr) :=
  if size == 0 then .error (.memUB (.reallocZero p)) else
  match p.obj with
  | none => .ok (m.malloc size)                    -- §7.24.3.7p3: behaves like malloc
  | some o =>
    match m.get? o with
    | some c =>
      if c.dur == .allocated && c.live && p.off == 0 then
        let keep := c.bytes.take size
        let fresh := keep ++ List.replicate (size - keep.length) CByte.indet
        let m' : Mem := ⟨m.objs ++ [⟨.allocated, true, fresh, none⟩]⟩
        .ok (m'.kill o, Ptr.toObject m.objs.length)
      else .error (.memUB (.freeUnmatched p))
    | none => .error (.memUB (.freeUnmatched p))

/-! ## Well-formedness

Four properties the interpreter will lean on, each stated about the
operations above and each RUN on the shipped corpus in
`Examples/c/sunfish/memory.lean` — a lemma nobody instantiated is a lemma
nobody checked. -/

/-- `alloc` places the new object where its returned id says it is. -/
@[simp] theorem get?_alloc (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) :
    (m.alloc dur size ty).1.get? (m.alloc dur size ty).2
      = some ⟨dur, true, List.replicate size .indet, ty⟩ := by
  simp [alloc, get?]

/-- C23 §6.2.4: a freshly created object is INSIDE its lifetime, so every
in-bounds access resolves. This is the base case every frame entry uses. -/
theorem resolve_alloc (m : Mem) (dur : Duration) (size n : Nat) (ty : Option CType)
    (h : n ≤ size) :
    (m.alloc dur size ty).1.resolve (Ptr.toObject (m.alloc dur size ty).2) n
      = .ok ((m.alloc dur size ty).2,
             ⟨dur, true, List.replicate size .indet, ty⟩, 0) := by
  simp [resolve, Ptr.toObject, CObj.size]
  omega

/-- INVERSION for `resolve`: everything a successful access establishes.

Stated once because `resolve` is the single place C's three structural
undefined behaviors are decided (§6.5.4.2p4, §6.2.4p2, §6.5.7p9), so
every later lemma wants exactly these facts and none should re-derive
them. -/
theorem resolve_ok {m : Mem} {p : Ptr} {n : Nat} {o : ObjId} {c : CObj} {off : Nat}
    (h : m.resolve p n = .ok (o, c, off)) :
    p.obj = some o ∧ m.get? o = some c ∧ c.live = true
      ∧ off = p.off.toNat ∧ 0 ≤ p.off ∧ off + n ≤ c.bytes.length := by
  unfold resolve at h
  cases hobj : p.obj with
  | none => rw [hobj] at h; simp only [] at h; exact absurd h (by simp)
  | some o' =>
    rw [hobj] at h
    simp only [] at h
    cases hget : m.get? o' with
    | none => rw [hget] at h; simp only [] at h; exact absurd h (by simp)
    | some c' =>
      rw [hget] at h
      simp only [] at h
      by_cases hlive : c'.live = true
      · rw [if_neg (by simp [hlive])] at h
        by_cases hb : p.off < 0 ∨ p.off + (n : Int) > (c'.size : Int)
        · rw [if_pos (by simpa using hb)] at h; exact absurd h (by simp)
        · rw [if_neg (by simpa using hb)] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          subst h1; subst h2; subst h3
          simp only [not_or, Int.not_lt, gt_iff_lt] at hb
          obtain ⟨hlo, hhi⟩ := hb
          refine ⟨rfl, hget, hlive, rfl, hlo, ?_⟩
          have he : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg hlo
          simp only [CObj.size] at hhi
          omega
      · rw [if_pos (by simp [hlive])] at h; exact absurd h (by simp)

/-- Writing an object leaves it where it was. -/
@[simp] theorem get?_set_self (m : Mem) (o : ObjId) (c : CObj) (h : o < m.objs.length) :
    (Mem.mk (m.objs.set o c)).get? o = some c := by
  simp [get?, h]

/-- C23 §6.2.4p2: once an object's lifetime ends, EVERY access through a
pointer to it refuses — `J.2(9)`/`J.2(10)`. The object is still in the
store, which is exactly what makes the refusal possible instead of a
reused slot silently answering. -/
theorem resolve_kill (m : Mem) (o : ObjId) (c : CObj) (p : Ptr) (n : Nat)
    (hp : p.obj = some o) (hc : m.get? o = some c) :
    (m.kill o).resolve p n = .error (.memUB (.deadObject o c.dur)) := by
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [resolve, hp, hk]

/-- **The round trip.** What `storeBytes` wrote, `loadBytes` reads back —
so the byte lattice is a memory and not a filter.

The store's success is a HYPOTHESIS, never a conclusion: a store that
refused has no out-memory to speak about, which is the same discipline
§4.3's drain amendment applies to worlds. -/
theorem loadBytes_storeBytes {m m' : Mem} {p : Ptr} {bs : List CByte}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p bs.length = .ok (o, c, off))
    (h : m.storeBytes p bs = .ok m') :
    m'.loadBytes p bs.length = .ok bs := by
  obtain ⟨hobj, hget, hlive, hoff, hlo, hhi⟩ := resolve_ok hr
  subst hoff
  simp only [storeBytes, hr, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  have hidx : o < m.objs.length := by
    simp only [get?] at hget
    match Nat.lt_or_ge o m.objs.length with
    | .inl hlt => exact hlt
    | .inr hge => rw [List.getElem?_eq_none hge] at hget; simp at hget
  have he : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg hlo
  have htk : (c.bytes.take p.off.toNat).length = p.off.toNat := by simp; omega
  simp only [loadBytes, resolve, hobj, get?_set_self _ _ _ hidx, bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [hlive]), if_neg ?bnd]
  case bnd =>
    intro hc
    simp only [CObj.size, Bool.or_eq_true, decide_eq_true_eq,
      List.length_append, List.length_take, List.length_drop] at hc
    omega
  simp only [Except.ok.injEq]
  rw [List.append_assoc, List.drop_left' htk, List.take_left' rfl]

/-! ### Axiom audit

The standing requirement: every theorem prints its axioms, and no
`sorry` or `native_decide` appears anywhere in the tier. -/

#print axioms get?_alloc
#print axioms resolve_alloc
#print axioms resolve_ok
#print axioms get?_set_self
#print axioms resolve_kill
#print axioms loadBytes_storeBytes

end Mem

/-! ## §3.4 — `Halt`, the base outside `ρ`

Per `docs/family-architecture.md` §3.4: the outcomes that **no construct
in any modelled language may catch** live in the monad's BASE, not in
`ExceptT`'s error. Inside `ρ`, "no catch reaches a refusal" is a
per-language, per-construct PROOF OBLIGATION — and C cannot discharge it
cheaply: this corpus alone has `setjmp` 2, `longjmp` 2 and 5 `jmp_buf`
objects, plus signal handlers in the language at large. Uncatchability
belongs to the definition.

So `timeout` and `unsupported` are here, and the two catchable-in-
principle refusal causes (`ub`, `libc`) stay in `Refusal`. -/

/-! ### HOLD: do NOT replace this with `Core.SemM`'s `Halt` yet

`LeanModels/Core/SemM.lean` is on master and has this type's exact SHAPE.
Adopting it today would still be wrong, because **its payload is poorer
than this one**: Core carries `unsupported (msg : String)`, while this
carries `(what, snapshot : Option Mem)` plus the two structural guards
that make the §3.4 ruling real — the hand-written `BEq` that ignores the
snapshot, and `Outcome`, which has nowhere to put a `Mem`.

**Importing Core now would delete the ruling**, not consolidate it. The
rebuild lane is landing a Core payload that SUBSUMES this one (cause +
message + optional snapshot, with the guards lifted into Core); when it
does, this lane's adoption is a substitution rather than a rewrite, and
the duplication is retired the way §9.2 wants — by touch, once the shared
thing is actually the better one. Until then, this is deliberate
duplication with a reason, not drift. -/

/-- The base monad: outcomes nothing can catch. -/
inductive Halt (α : Type) where
  | ok (a : α)
  /-- Fuel exhaustion, and nothing else. Carries NO state: a timeout is
  not an observation, and state here would invite treating it as one. -/
  | timeout
  /-- Outside the tier. Carries its CAUSE, and optionally a snapshot of
  the memory as it stood AT the refusal site.

  **The snapshot is diagnostic only and is NEVER an observable.** It
  exists so a REFUSE row can say what had happened by the time the model
  declined; it must not reach any verdict comparison. That guard is
  structural rather than advisory — see the `BEq` instance below, which
  ignores it, and `Outcome`, which drops it. -/
  | unsupported (what : String) (snapshot : Option Mem)
deriving Repr, Inhabited

namespace Halt

/-- **The snapshot is not an observable, and this instance is where that
is enforced.** Two runs that refused the same construct compare EQUAL
even if they reached it through different memories — because the memory
is diagnostic. A derived `BEq` would have compared it and quietly made a
diagnostic aid into part of the verdict. -/
instance [BEq α] : BEq (Halt α) where
  beq
    | .ok a, .ok b => a == b
    | .timeout, .timeout => true
    | .unsupported a _, .unsupported b _ => a == b
    | _, _ => false

@[inline] def bind : Halt α → (α → Halt β) → Halt β
  | .ok a, f => f a
  | .timeout, _ => .timeout
  | .unsupported w s, _ => .unsupported w s

instance : Monad Halt where
  pure := .ok
  bind := Halt.bind

@[simp] theorem bind_ok (a : α) (f : α → Halt β) : Halt.bind (.ok a) f = f a := rfl
@[simp] theorem bind_timeout (f : α → Halt β) :
    Halt.bind (.timeout : Halt α) f = .timeout := rfl
@[simp] theorem bind_unsupported (w : String) (sn : Option Mem) (f : α → Halt β) :
    Halt.bind (.unsupported w sn) f = .unsupported w sn := rfl

end Halt

/-! ## The verdict a scoreboard sees

`docs/c23-goal.md` §3's four verdicts, as one type. This is what inch 6
reads, and it is the second place the snapshot guard is enforced: there
is nowhere to put a `Mem` here, so a snapshot cannot reach a comparison
even by accident. -/

/-- What a run produced, with the three refusal causes kept apart. -/
inductive Outcome (α : Type) where
  | ok (value : α)
  /-- A refusal that rode in `ExceptT`: cause `ub` or `libc`. -/
  | refused (r : Refusal)
  /-- Cause `unsupported` — out of tier. The snapshot is deliberately
  NOT carried across this boundary. -/
  | unsupported (what : String)
  /-- Fuel exhaustion. Never conflated with a refusal. -/
  | timeout
deriving Repr, Inhabited, BEq

/-- The cause of an outcome, where it has one. -/
def Outcome.cause? : Outcome α → Option Cause
  | .ok _ => none
  | .refused r => some r.cause
  | .unsupported _ => some .unsupported
  | .timeout => none

end LeanModels.C.C23
