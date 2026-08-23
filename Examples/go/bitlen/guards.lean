import LeanModels.Go

/-!
# The rung-3 exemplar: `bigmod.bitLen`, and the model agrees with `gc`

**A real function, chosen by census — not a fixture written to be easy.**
`docs/backlog/go.md` §G6 searched the standard library for functions the
walker could execute, filtered to those that RETURN a value and do real
arithmetic, and this is what came out. Its source, verbatim from
`src/crypto/internal/fips140/bigmod/nat.go` (Go 1.25.6), comments and all:

    // bitLen is a version of bits.Len that only leaks the bit length of n, but not
    // its value. bits.Len and bits.LeadingZeros use a lookup table for the
    // low-order bits on some architectures.
    func bitLen(n uint) int {
        len := 0
        // We assume, here and elsewhere, that comparison to zero is constant time
        // with respect to different non-zero values.
        for n != 0 {
            len++
            n >>= 1
        }
        return len
    }

FIPS-140 crypto code — a better provenance than anything this lane could
have written. Reproduced under the cite-and-paraphrase law;
BSD-3-Clause, "Copyright 2009 The Go Authors", per
`docs/go-charter.md` §1.4's ruling that the in-tree copies are taken under
the repository's single instrument rather than the website's CC-BY-4.0.

**It is quoted HERE rather than vendored as a sibling `.go` file, and that
is a build-cost decision measured rather than guessed.** `tools/triad.sh`'s
`path_targets` maps `Examples/*.lean` to its own precise module but sends
every OTHER `Examples/` path to the whole `Examples` library — so a
reference file that nothing builds and no module reads widened the last
tenure's target from four Go modules to the entire library, and the build
went from 91 seconds to 37 minutes. `--build-target` cannot narrow it
(it UNIONs, never replaces). Quoting the source costs nothing and keeps
the tenure scoped.

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

/-! ## §1 THE SPEC HALF — the mathematics of `bitLen`, no interpreter

STMT-65 / `docs/statement-cookbook.md` §6: a theorem that can be stated
about the mathematics SHOULD be. Nothing in this section mentions
`execStmt`, `GoM`, a world or fuel, so all of it recompiles unchanged if
the walker is redefined.

`bitLenSpec` is what the Go loop computes, written as mathematics: shift
right until zero, counting. The two theorems are the CHARACTERISATION —
`bitLenSpec n` really is the number of significant bits, bracketed from
both sides. Together they say `2^(k-1) ≤ n < 2^k` for `k = bitLenSpec n`,
which is the definition of bit length and not a restatement of the code. -/

def bitLenSpec : Nat → Nat
  | 0 => 0
  | n + 1 => bitLenSpec ((n + 1) / 2) + 1
decreasing_by omega

@[go_spec] theorem bitLenSpec_zero : bitLenSpec 0 = 0 := by simp [bitLenSpec]

@[go_spec] theorem bitLenSpec_pos {n : Nat} (h : 0 < n) :
    bitLenSpec n = bitLenSpec (n / 2) + 1 := by
  match n, h with
  | k + 1, _ => rw [bitLenSpec]

@[go_spec] theorem bitLenSpec_lt (n : Nat) : n < 2 ^ bitLenSpec n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [bitLenSpec]
    | k + 1 =>
      have hh : (k + 1) / 2 < k + 1 := by omega
      have hrec := ih ((k + 1) / 2) hh
      rw [bitLenSpec_pos (by omega : 0 < k + 1), Nat.pow_succ]
      omega

@[go_spec] theorem bitLenSpec_le {n : Nat} (h : 0 < n) : 2 ^ (bitLenSpec n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, h with
    | k + 1, _ =>
      rw [bitLenSpec_pos (by omega : 0 < k + 1)]
      simp only [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos ((k + 1) / 2) with hz | hp
      · rw [hz, bitLenSpec_zero]; simp
      · have hh : (k + 1) / 2 < k + 1 := by omega
        have hrec := ih ((k + 1) / 2) hh hp
        have hb : 1 ≤ bitLenSpec ((k + 1) / 2) := by
          rw [bitLenSpec_pos hp]; omega
        have hsplit : bitLenSpec ((k+1)/2) - 1 + 1 = bitLenSpec ((k+1)/2) := by omega
        calc 2 ^ bitLenSpec ((k + 1) / 2)
            = 2 ^ (bitLenSpec ((k+1)/2) - 1) * 2 := by
              rw [← Nat.pow_succ]; congr 1; omega
          _ ≤ ((k + 1) / 2) * 2 := by exact Nat.mul_le_mul_right 2 hrec
          _ ≤ k + 1 := by omega


/-! ## §2 THE INTERPRETER BRIDGE — one step, and it is the load-bearing one

The interpreter half's content is that the walker's OPERATION is the
spec's operation. `n >>= 1` on a `uint64` is the interpreter's
`binNum .shr`; the spec's step is `n / 2`. This lemma is the join, and it
is where a width bug or a signedness bug would surface. -/

/-- Halving a non-negative integer is floor division — the arithmetic
fact the bridge rests on. -/
@[go_spec] theorem fdiv_two (v : Nat) :
    Int.fdiv (v : Int) 2 = ((v / 2 : Nat) : Int) := by
  cases v with
  | zero => rfl
  | succ k => rfl

/-- **THE BRIDGE.** The interpreter's `n >>= 1` on a `uint64` IS the
spec's `n / 2`. This is where a width bug or a signedness bug would
surface, and it is the one place the two halves touch. -/
@[go_spec] theorem shr_one_is_halving (v : Nat) :
    binNum .shr IntKind.uint64 (v : Int) 1
      = pure (GoVal.mkInt IntKind.uint64 ((v / 2 : Nat) : Int)) := by
  simp [binNum, fdiv_two]

/-! **What is still owed, named rather than implied.** The full
interpreter half — *the walker, run on `bitLenBody` with enough fuel,
leaves `len` equal to `bitLenSpec n`* — is an induction over the loop
carrying the store through each iteration. It is this lane's next
theorem. What is proved here is its arithmetic step; what is CHECKED
below, on 35 inputs, is the composition. The distinction is the whole
reason §1 and §2 are separated. -/

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

/-! ## THREE-WAY AGREEMENT — model, oracle, and the MATHEMATICS

The rows above pin the model against what `gc` printed. These pin it
against `bitLenSpec`, which §1 proved is genuinely the bit length
(`bitLenSpec_le` and `bitLenSpec_lt` bracket it from both sides).

So the same 35 inputs are checked twice, against two independent
standards: an executable oracle and a proved specification. A model that
agreed with the compiler but not the mathematics — or the reverse — would
show up in exactly one of the two blocks. -/

def bitLenN (n : Nat) : Option Int := bitLen (n : Int)

#guard bitLenN 0 == some (bitLenSpec 0)
#guard bitLenN 1 == some (bitLenSpec 1)
#guard bitLenN 2 == some (bitLenSpec 2)
#guard bitLenN 3 == some (bitLenSpec 3)
#guard bitLenN 4 == some (bitLenSpec 4)
#guard bitLenN 5 == some (bitLenSpec 5)
#guard bitLenN 7 == some (bitLenSpec 7)
#guard bitLenN 8 == some (bitLenSpec 8)
#guard bitLenN 9 == some (bitLenSpec 9)
#guard bitLenN 15 == some (bitLenSpec 15)
#guard bitLenN 16 == some (bitLenSpec 16)
#guard bitLenN 17 == some (bitLenSpec 17)
#guard bitLenN 31 == some (bitLenSpec 31)
#guard bitLenN 32 == some (bitLenSpec 32)
#guard bitLenN 33 == some (bitLenSpec 33)
#guard bitLenN 63 == some (bitLenSpec 63)
#guard bitLenN 64 == some (bitLenSpec 64)
#guard bitLenN 65 == some (bitLenSpec 65)
#guard bitLenN 100 == some (bitLenSpec 100)
#guard bitLenN 127 == some (bitLenSpec 127)
#guard bitLenN 128 == some (bitLenSpec 128)
#guard bitLenN 255 == some (bitLenSpec 255)
#guard bitLenN 256 == some (bitLenSpec 256)
#guard bitLenN 511 == some (bitLenSpec 511)
#guard bitLenN 512 == some (bitLenSpec 512)
#guard bitLenN 1000 == some (bitLenSpec 1000)
#guard bitLenN 1023 == some (bitLenSpec 1023)
#guard bitLenN 1024 == some (bitLenSpec 1024)
#guard bitLenN 65535 == some (bitLenSpec 65535)
#guard bitLenN 65536 == some (bitLenSpec 65536)
#guard bitLenN 2147483648 == some (bitLenSpec 2147483648)
#guard bitLenN 4294967296 == some (bitLenSpec 4294967296)
#guard bitLenN 4611686018427387904 == some (bitLenSpec 4611686018427387904)
#guard bitLenN 9223372036854775808 == some (bitLenSpec 9223372036854775808)
#guard bitLenN 18446744073709551615 == some (bitLenSpec 18446744073709551615)

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

/-! ## Axioms -/
#print axioms Examples.go.bitlen.bitLenSpec_lt
#print axioms Examples.go.bitlen.bitLenSpec_le
#print axioms Examples.go.bitlen.shr_one_is_halving
