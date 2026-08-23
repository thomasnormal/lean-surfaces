import LeanModels.Go

/-!
# The rung-3 exemplar: `bigmod.bitLen`, and the model agrees with `gc`

**A real function, chosen by census — not a fixture written to be easy.**
`docs/backlog/go.md` §G6 searched the standard library for functions the
walker could execute, filtered to those that RETURN a value and do real
arithmetic, and this is what came out. Its source sits verbatim beside
this file in `bitlen.go`:

    // bitLen is a version of bits.Len that only leaks the bit length of
    // n, but not its value.
    func bitLen(n uint) int {
        len := 0
        for n != 0 {
            len++
            n >>= 1
        }
        return len
    }

from `src/crypto/internal/fips140/bigmod/nat.go` — FIPS-140 crypto code,
which is a better provenance than anything this lane could have written.

## What is claimed here, and what is not

The rows below are a **differential claim**: the model, executed in Lean's
kernel, produces the same integer as the compiled function did on the same
input. The expected column was not derived — it was **produced by running
the real `gc`-compiled function** and pasted in, which is the only way the
comparison means anything.

It is NOT a proof that `bitLen` is correct. That statement — `bitLen n` is
the number of significant bits of `n` — is an induction over the loop and
is this lane's next theorem, not this inch's. What these rows establish is
the thing that has to come first: **the model and the toolchain agree on
this function's behaviour.**

## What the exemplar needed, and why the census picked the operators

Nothing here was added because it seemed useful. `>>=` forced compound
assignment and the shift operators; the `for n != 0` form forced a
condition-only loop; and the function boundary forced calls, which
§G6 measured as blocking **73.3%** of the files rung 1 already reaches.
-/

namespace Examples.go.bitlen

open LeanModels LeanModels.Go

/-- Go's `uint` is 64-bit on the censused platform. The width is a profile
input, not a constant of the language — `docs/go-charter.md` §7.3. -/
def uintK : IntKind := IntKind.uint64
def intK : IntKind := IntKind.int64

private def u (n : Int) : Expr := .lit (GoVal.mkInt uintK n)
private def i (n : Int) : Expr := .lit (GoVal.mkInt intK n)

/-- `bitLen`'s body, transcribed statement for statement. The comment in
the middle of the real loop is a comment; everything else is here. -/
def bitLenBody : List Stmt :=
  [ .declare "len" (i 0),
    .forS none (some (.binary .ne (.ident "n") (u 0))) none
      [ .incDec "len" true,
        .assignOp .shr "n" (u 1) ],
    .ret (some (.ident "len")) ]

/-- The program: one function, one parameter. -/
def prog : FuncTable := [("bitLen", ["n"], bitLenBody)]

/-- Run `bitLen` on a concrete input and read the integer back out. -/
def bitLen (n : Int) : Option Int :=
  match (callFunction prog 4096 "bitLen" [GoVal.mkInt uintK n]) ({} : GoWorld) with
  | .ok (.ok (.intV _ r), _) => some r
  | _ => none

/-! ## THE DIFFERENTIAL ROWS — 35 of them, and the expected column was
GENERATED, not typed

Every row below was produced by `printf`-ing the compiled function's
answer and mechanically rewriting it into `#guard` syntax. Typing the
column by hand was the first attempt and it is exactly the wrong way:
this file's whole claim is that two independent implementations agree, and
a hand-copied expectation makes the Lean side's answer the source of both
columns the moment anyone "fixes" a row. The inputs sweep the powers of
two and their neighbours up to the full 64-bit width, where a width bug
would hide. -/

#guard bitLen 0 == some 0
#guard bitLen 1 == some 1
#guard bitLen 2 == some 2
#guard bitLen 3 == some 2
#guard bitLen 4 == some 3
#guard bitLen 5 == some 3
#guard bitLen 7 == some 3
#guard bitLen 8 == some 4
#guard bitLen 9 == some 4
#guard bitLen 15 == some 4
#guard bitLen 16 == some 5
#guard bitLen 17 == some 5
#guard bitLen 31 == some 5
#guard bitLen 32 == some 6
#guard bitLen 33 == some 6
#guard bitLen 63 == some 6
#guard bitLen 64 == some 7
#guard bitLen 65 == some 7
#guard bitLen 100 == some 7
#guard bitLen 127 == some 7
#guard bitLen 128 == some 8
#guard bitLen 255 == some 8
#guard bitLen 256 == some 9
#guard bitLen 511 == some 9
#guard bitLen 512 == some 10
#guard bitLen 1000 == some 10
#guard bitLen 1023 == some 10
#guard bitLen 1024 == some 11
#guard bitLen 65535 == some 16
#guard bitLen 65536 == some 17
#guard bitLen 2147483648 == some 32
#guard bitLen 4294967296 == some 33
#guard bitLen 4611686018427387904 == some 63
#guard bitLen 9223372036854775808 == some 64
#guard bitLen 18446744073709551615 == some 64

/-! `uint` is 64 bits on this profile, so the last row above — `2^64 - 1`
— is the widest value the type holds, and its bit length is 64. A value
BEYOND the width wraps on the way in, which is the language's own
reduction rule and not a clamp: -/

#guard bitLen (2 ^ 64) == some 0

/-! ## Non-vacuity

A differential row that cannot fail is decoration. Two things are checked
here, and the third — that a WRONG expectation actually breaks the build —
was verified by flipping a row and watching Lean report it, then restoring
(`docs/backlog/go.md` §G6). It is not left in the file, because a guard
that must fail is not a guard. -/

#guard (bitLen 1024).isSome
#guard bitLen 1024 == some 11

/-! ## Fuel is not decoration either

The loop runs once per significant bit, so `bitLen (2^63)` needs 64
iterations. At fuel too small for the walk, the answer is a TIMEOUT and
not a wrong number — the model declines rather than truncating. -/

def bitLenAt (fuel : Nat) (n : Int) : Bool :=
  match (callFunction prog fuel "bitLen" [GoVal.mkInt uintK n]) ({} : GoWorld) with
  | .error .timeout => true
  | _ => false

#guard bitLenAt 4 (2 ^ 63) == true
#guard bitLenAt 4096 (2 ^ 63) == false

/-! ## A call to an undeclared function is ENVIRONMENT, not a language gap

It retires by widening the modelled slice, never by climbing a rung —
and, per the tier's standing gate, never as `undefined`. -/

#guard (match (callFunction prog 64 "bits.Len" [GoVal.mkInt uintK 1]) ({} : GoWorld) with
        | .error (.unsupported c _ _) => c.className == "environment"
        | _ => false) == true

#guard (match (callFunction prog 64 "bits.Len" [GoVal.mkInt uintK 1]) ({} : GoWorld) with
        | .error (.unsupported c _ _) => c.isUndefined
        | _ => true) == false

end Examples.go.bitlen
