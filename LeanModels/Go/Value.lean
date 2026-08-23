/-!
# Go values — and integer overflow is DEFINED

M1 inch 1, first half. `docs/go-charter.md` §6.1 fixes the value model as
its own, not the Python tier's: Go's integers have WIDTHS, so an unbounded
`Int` constructor cannot express the language.

## The finding this file makes CHECKABLE

`docs/go-charter.md`'s headline is that **"undefined" appears zero times
in the Go specification**, against C23's 284 occurrences and Annex J.2's
221 enumerated circumstances. That is a quotable claim about a document.
Here it becomes a property of the model, at the one place where C and Go
differ most sharply and where the C tier had to arm a UB class.

The Go specification, "Integer overflow", verbatim:

> For unsigned integer values, the operations `+`, `-`, `*`, and `<<` are
> computed modulo 2ⁿ, where n is the bit width of the unsigned integer's
> type. Loosely speaking, these unsigned integer operations discard high
> bits upon overflow, and programs may rely on "wrap around".

and, for the signed case that C leaves undefined:

> For signed integers, the operations `+`, `-`, `*`, `/`, and `<<` may
> legally overflow and the resulting value exists and is deterministically
> defined by the signed integer representation, the operation, and its
> operands. **Overflow does not cause a run-time panic. A compiler may not
> optimize code under the assumption that overflow does not occur.**

So signed overflow is not merely permitted, it is *defined*, it is
*not* a panic, and the compiler is *forbidden* from assuming it away.
`docs/c-tier-charter.md` §2.2(a) had to give C "unsigned wraps, defined"
and "signed overflows, REFUSE" simultaneously. Go needs one rule for both,
and `Spec.lean` states it as a theorem rather than a comment.
-/

namespace LeanModels.Go

/-- An integer type's shape: its width in bits and its signedness.

The platform-dependent `int`/`uint`/`uintptr` widths are an input from the
envelope's profile, not a constant here — the same treatment
`docs/c-profile.md` gives C's, and for the same reason: same source,
different profile, different program. Inch 1 carries the profile width as
a parameter and pins nothing. -/
structure IntKind where
  bits : Nat
  signed : Bool
  deriving Repr, DecidableEq, Inhabited

namespace IntKind

def int8   : IntKind := ⟨8, true⟩
def int16  : IntKind := ⟨16, true⟩
def int32  : IntKind := ⟨32, true⟩
def int64  : IntKind := ⟨64, true⟩
def uint8  : IntKind := ⟨8, false⟩
def uint16 : IntKind := ⟨16, false⟩
def uint32 : IntKind := ⟨32, false⟩
def uint64 : IntKind := ⟨64, false⟩

/-- The modulus, 2 raised to the width. -/
def modulus (k : IntKind) : Nat := 2 ^ k.bits

/-- Reduce an arbitrary integer into `k`'s representable range.

This IS the specification's rule, both halves at once: unsigned is
"computed modulo 2ⁿ"; signed is the same reduction followed by the
two's-complement reading of the top half as negative. One function,
because the spec gives one behaviour — the C tier needs two and a refusal
between them. -/
def wrap (k : IntKind) (n : Int) : Int :=
  let m : Int := (k.modulus : Int)
  if m = 0 then 0
  else
    let r := n % m
    let r := if r < 0 then r + m else r
    if k.signed && 2 * r ≥ m then r - m else r

/-- The least value of `k`. -/
def lo (k : IntKind) : Int :=
  if k.signed then -((k.modulus : Int) / 2) else 0

/-- The greatest value of `k`. -/
def hi (k : IntKind) : Int :=
  if k.signed then (k.modulus : Int) / 2 - 1 else (k.modulus : Int) - 1

end IntKind

/-- A channel's identity. Channels are values in Go, and rung 0's fixture
is built on them, so the value model carries them from inch 1 even though
no rule steps one yet. -/
abbrev ChanId := Nat

/-- A location in the store. `docs/go-charter.md` §6.1: Go has pointers
and addressable locals, so a binding is not enough. -/
abbrev Addr := Nat

/-- A Go value, scoped to rung 1's vocabulary
(`docs/backlog/go.md` §G1: 45 AST node kinds, 56.9% of the standard
library by file).

`nilV` is a single constructor rather than a per-type nil because inch 1
carries no types; `docs/go-charter.md` §7.3 records that `go/types` is the
frontend's job and that seven constructs are type-dependent. -/
inductive GoVal where
  | boolV (b : Bool)
  | intV (k : IntKind) (n : Int)
  /-- **A Go string is a BYTE SEQUENCE, not a sequence of characters.**
  The specification is explicit — *"a string value is a (possibly empty)
  sequence of bytes"* — and `s[i]` yields a `byte`, never a rune.

  Modelling it as a Lean `String` would be wrong, and the corpus says so
  concretely: `math/bits`' `rev8tab` contains **128 bytes ≥ 0x80** (of
  256), and a Lean `Char` at code point 200 occupies **two** bytes in
  UTF-8 — measured, `(String.singleton c).utf8ByteSize = 2`. So a Lean
  `String` cannot hold that table with `len` 256 and `s[i]` byte-exact,
  and `Reverse8` would be unmodellable while looking fine. -/
  | stringV (bytes : List UInt8)
  | ptrV (a : Addr)
  | chanV (c : ChanId)
  | structV (fields : List (String × GoVal))
  | sliceV (elems : List GoVal)
  /-- A **run-time error** value — what a run-time panic carries.

  Go's `panic` from a run-time fault does NOT carry a string: it carries a
  value implementing `runtime.Error`, which is an `error`. Modelling it as
  `stringV` was wrong on that point, and it also cost: once a Go string
  became a byte sequence, every such panic forced `String.toUTF8` through
  the kernel and the `#guard` battery timed out. The faithful shape is
  also the cheap one. -/
  | runtimeErrorV (msg : String)
  | nilV
  deriving Repr, Inhabited

namespace GoVal

/-- Build an integer value already reduced into its type's range, which is
the only way one should ever be built: an `intV` outside its own range
would be a value the language cannot represent. -/
def mkInt (k : IntKind) (n : Int) : GoVal := .intV k (k.wrap n)

/-- Go's zero value, per "The zero value": booleans `false`, numbers `0`,
strings `""`, and pointers, channels and slices `nil`. -/
def zeroBool : GoVal := .boolV false
def zeroInt (k : IntKind) : GoVal := .intV k 0
def zeroString : GoVal := .stringV []

/-- Build a Go string from Lean text, via its UTF-8 bytes. Identity on
ASCII, and byte-exact on everything else — which is the property the
`String` representation could not offer. -/
def ofString (s : String) : GoVal := .stringV s.toUTF8.toList

end GoVal

end LeanModels.Go
