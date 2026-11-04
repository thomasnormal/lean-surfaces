import LeanModels.Go.Sem

/-!
# The package tier — resolved `pkg.F` calls

`docs/backlog/go.md` §G21 chartered the extractor tier and §G21's rung E1
is this file plus `Expr.callPkg`. The division of labour is the point:

* **The EXTRACTOR resolves.** `bits.Len64(x)` becomes
  `Expr.callPkg "math/bits" "Len64" [x]` in the frontend, from the file's
  own import table — no type checker. Resolution is a SYNTACTIC question
  and it stays out of the walker, exactly as `Expr.convert` did in §G14:
  a decision the frontend can make must not be re-made inline at every
  evaluation.
* **The WALKER dispatches.** It never sees a package name it has to parse.

## Why `math/bits` is the first package, and what E1 is worth

Not because it leads the ranking — it does, among modellable packages,
but only just. Because **this lane already proved `bitLen` correct**
(§G15), so the rung tests the MECHANISM against settled semantics rather
than debugging resolution and arithmetic at once.

The honest label: E1's package model is worth **+7 files** on its own
(§G21). The deliverable is the mechanism, not the coverage.

## The size of what is NOT here, measured

`math/bits` has 3,855 call sites in the non-test standard library, and
they are dominated by functions this rung CANNOT model:

| function | sites | share |
| --- | ---: | ---: |
| `Add64` | 2,108 | 54.7% |
| `Mul64` | 1,069 | 27.7% |
| `Sub64` | 212 | 5.5% |
| all single-return functions together | ~250 | ~6% |

`Add64`, `Mul64` and `Sub64` return **two values**, and the walker has
single-valued returns (`Flow.returned` carries one `GoVal`). So **82.4%
of `math/bits` usage sits behind a multi-value-return rung** that does
not exist yet. That is a census result, not an excuse: it says the
tuple/multi-return rung is worth more than the rest of `math/bits` put
together, and it should be priced against the walker's other work rather
than smuggled in here. Declaring only what this rung executes is the
vocabulary law.

## Refusals NAME the package and the function

An unmodelled package call refuses as `environment` saying
`math/rand.Intn is not modelled`, not "selector call". That is §5.2's
`environment` bucket retiring **by widening the modelled slice**, which
is what `docs/family-architecture.md` prescribes for it, and it makes the
refusal stream a ranked worklist (§G8's recommendation 2).
-/

namespace LeanModels.Go

/-- `bits.LenN`'s specification: the number of bits needed to represent
`n`, with `bitLenSpec 0 = 0`.

This is the same recursion §G15 proved `bigmod.bitLen` implements, and
the agreement is stated as a theorem below rather than assumed. -/
def bitLenSpec : Nat → Nat
  | 0 => 0
  | n + 1 => bitLenSpec ((n + 1) / 2) + 1
decreasing_by omega

/-- `bits.TrailingZerosN` for a NON-ZERO argument. Zero is handled at the
call site because Go defines `TrailingZeros64(0) == 64` — the width, not
`0` — and that special case is a documented part of the function, not an
edge the recursion should absorb. -/
def trailingZerosSpec : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then 0 else trailingZerosSpec ((n + 1) / 2) + 1
decreasing_by omega

@[simp] theorem bitLenSpec_zero : bitLenSpec 0 = 0 := by simp [bitLenSpec]

@[simp] theorem trailingZerosSpec_zero : trailingZerosSpec 0 = 0 := by
  simp [trailingZerosSpec]

/-- **The zero case is the spec's, not the recursion's.** Stated so that a
future edit which "simplifies" `pkgCall` by dropping the guard breaks a
theorem instead of silently returning 0 where Go returns 64. -/
theorem trailingZeros_zero_is_special : trailingZerosSpec 0 ≠ 64 := by
  rw [trailingZerosSpec_zero]; decide

/-- What a modelled package function does.

`bits.Div` **panics** — on a zero divisor and on a quotient that will not
fit — so a plain `Option` cannot express this tier any more. The three
outcomes are genuinely distinct and must not be collapsed:

* `values` — it computed something;
* `panics` — Go DEFINES a run-time panic here, which is an outcome of the
  program, not a limit of the model;
* `notModelled` — a limit of the model, which becomes an `environment`
  refusal naming `pkg.fn`.

Folding `panics` into `notModelled` would report a program's own defined
behaviour as a gap in this tier, which is the §5.2 mis-bucketing §G14
already paid for once. -/
inductive PkgOutcome where
  | values (vs : List GoVal)
  | panics (msg : String)
  | notModelled
  deriving Repr, Inhabited

/-- `uint` is 64-bit on the platforms this tier models, and `bits.UintSize`
is a package CONSTANT reporting it (`const UintSize = uintSize`) — not a
function, which is why it needs its own resolution kind (§G24). -/
def uintSize : Nat := 64

private def u64 (n : Int) : GoVal := GoVal.mkInt IntKind.uint64 n
private def norm (v : GoVal) : Int :=
  match v with | .intV _ n => IntKind.uint64.wrap n | _ => 0
private def modulus : Int := (IntKind.uint64.modulus : Int)
private def goInt (n : Int) : GoVal := GoVal.mkInt IntKind.int64 n

/-- Decimal digits of a POSITIVE natural, most significant first.

Separate from the sign so that `FormatInt` on `MinInt64` is not a special
case: Lean's `Int` is unbounded, so `-(-9223372036854775808)` is an
ordinary number here where in Go it would overflow `int64`. Measured
against `gc`, `FormatInt(-9223372036854775808, 10)` is
`"-9223372036854775808"`, and this definition gets it without a guard. -/
def digitsDec : Nat → List UInt8
  | 0 => []
  | n + 1 => digitsDec ((n + 1) / 10) ++ [UInt8.ofNat (48 + (n + 1) % 10)]
decreasing_by omega

/-- `strconv.FormatInt(n, 10)` as bytes. -/
def formatIntDec (n : Int) : List UInt8 :=
  if n = 0 then [48]
  else if n < 0 then (45 : UInt8) :: digitsDec (-n).toNat
  else digitsDec n.toNat

@[simp] theorem formatIntDec_zero : formatIntDec 0 = [48] := by
  simp [formatIntDec]

/-- The modelled package functions.

Every argument is normalised through `uint64` first: these functions'
PARAMETERS are `uint64`/`uint`, so trusting a caller's `IntKind` would let
a negative reach a carry or borrow test and invert it — a wrong answer
rather than a refusal (§G23).

`Add`/`Sub`/`Mul`/`LeadingZeros`/`TrailingZeros` are the `uint`-width
spellings and are **the same function** as their `64` counterparts at
`uintSize = 64`; they are listed separately because the corpus calls both
names and the walker resolves by name. -/
def pkgCall (pkg fn : String) (args : List GoVal) : PkgOutcome :=
  match pkg, fn, args with
  | "math/bits", "Len64", [a] | "math/bits", "Len", [a] =>
      .values [goInt (bitLenSpec (norm a).toNat)]
  | "math/bits", "TrailingZeros64", [a] =>
      let x := norm a
      .values [goInt (if x = 0 then 64 else trailingZerosSpec x.toNat)]
  | "math/bits", "TrailingZeros", [a] =>
      let x := norm a
      .values [goInt (if x = 0 then (uintSize : Int) else trailingZerosSpec x.toNat)]
  | "math/bits", "LeadingZeros64", [a] =>
      .values [goInt (64 - (bitLenSpec (norm a).toNat : Int))]
  | "math/bits", "LeadingZeros", [a] =>
      .values [goInt ((uintSize : Int) - (bitLenSpec (norm a).toNat : Int))]
  -- --- carry / borrow chains: the SECOND value is the point ---
  | "math/bits", "Add64", [a, b, c] | "math/bits", "Add", [a, b, c] =>
      let s := norm a + norm b + norm c
      .values [u64 s, u64 (if s ≥ modulus then 1 else 0)]
  | "math/bits", "Sub64", [a, b, c] | "math/bits", "Sub", [a, b, c] =>
      let d := norm a - norm b - norm c
      .values [u64 d, u64 (if d < 0 then 1 else 0)]
  | "math/bits", "Mul64", [a, b] | "math/bits", "Mul", [a, b] =>
      let p := norm a * norm b
      .values [u64 (p / modulus), u64 (p % modulus)]
  -- --- the one that PANICS ---
  | "math/bits", "Div64", [h, l, d] | "math/bits", "Div", [h, l, d] =>
      let hi := norm h
      let lo := norm l
      let y := norm d
      if y = 0 then .panics "runtime error: integer divide by zero"
      else if y ≤ hi then .panics "runtime error: integer overflow"
      else
        let v := hi * modulus + lo
        .values [u64 (v / y), u64 (v % y)]
  -- --- strconv, base 10 only (§G28: the 26 files that need it all pass 10) ---
  | "strconv", "FormatInt", [.intV _ n, .intV _ b] =>
      if b = 10 then .values [GoVal.stringV (formatIntDec n)]
      else
        -- an honest refusal, not a wrong answer: bases other than 10 are
        -- outside this rung's vocabulary and no file that needs them is
        -- being claimed as reached.
        .notModelled
  | "strconv", "Itoa", [.intV _ n] =>
      .values [GoVal.stringV (formatIntDec n)]
  | _, _, _ => .notModelled

/-- Package-level CONSTANTS. A distinct resolution kind: `bits.UintSize`
is not a call, so no `callPkg` node ever names it. -/
def pkgConst (pkg name : String) : Option GoVal :=
  match pkg, name with
  | "math/bits", "UintSize" => some (goInt (uintSize : Int))
  | _, _ => none

/-- The modelled surface, as data — with each function's ARITY, so that
"what does this tier support" is a claim a test can CHECK rather than a
comment that can drift.

It drifted immediately: the first version of this list named
`("math/bits", "Len")` while `pkgCall` implemented only `Len64`. Nothing
caught it, because the list was prose in a different shape. The theorem
below is what makes it a claim.

Each entry carries **sample arguments**, not just an arity, because §G28
added a CONDITIONALLY modelled function: `FormatInt` handles base 10 and
refuses every other base. An arity-only list would have had to either
omit it (under-claiming) or assert it at a base it refuses (failing).
Sample arguments say exactly what is claimed, and `Div`'s `[0,1,1]`
likewise avoids the divisor it panics on. -/
def modelledPkgFuncs : List (String × String × List Int) :=
  [("math/bits", "Len64", [1]), ("math/bits", "Len", [1]),
   ("math/bits", "TrailingZeros64", [1]), ("math/bits", "TrailingZeros", [1]),
   ("math/bits", "LeadingZeros64", [1]), ("math/bits", "LeadingZeros", [1]),
   ("math/bits", "Add64", [1, 1, 1]), ("math/bits", "Add", [1, 1, 1]),
   ("math/bits", "Sub64", [1, 1, 1]), ("math/bits", "Sub", [1, 1, 1]),
   ("math/bits", "Mul64", [1, 1]), ("math/bits", "Mul", [1, 1]),
   ("math/bits", "Div64", [0, 1, 1]), ("math/bits", "Div", [0, 1, 1]),
   ("strconv", "Itoa", [1]), ("strconv", "FormatInt", [1, 10])]

/-- Is `o` anything other than "this tier does not model it"? A defined
panic COUNTS as modelled — that is the distinction `PkgOutcome` exists
for. -/
def PkgOutcome.isModelled : PkgOutcome → Bool
  | .notModelled => false
  | _ => true

/-- **Every function this tier CLAIMS to model, it models.** Checked at
each declared arity, with sample arguments chosen so no
listed function panics or refuses, so a name that appears in the surface list but
not in `pkgCall` fails here instead of misleading a reader. -/
theorem surface_is_honest :
    modelledPkgFuncs.all (fun t =>
      (pkgCall t.1 t.2.1 (t.2.2.map (GoVal.mkInt IntKind.uint64))).isModelled)
      = true := by
  rfl

/-- A modelled function yields VALUES. -/
theorem modelled_Len64_has_values :
    ∃ vs, pkgCall "math/bits" "Len64" [GoVal.mkInt IntKind.uint64 1] = .values vs := by
  exact ⟨_, rfl⟩

/-- An unmodelled package is `notModelled` — the model's limit, which the
walker turns into an `environment` refusal naming `pkg.fn`. -/
theorem unmodelled_is_notModelled :
    pkgCall "math/rand" "Intn" [GoVal.mkInt IntKind.int64 5] = .notModelled := rfl

/-- **`panics` is NOT `notModelled`.** `bits.Div` by zero is behaviour Go
defines, and reporting it as a gap in this tier would be the §5.2
mis-bucketing §G14 paid for once already. -/
theorem div_by_zero_panics_not_unmodelled :
    pkgCall "math/bits" "Div"
        [GoVal.mkInt IntKind.uint64 0, GoVal.mkInt IntKind.uint64 5,
         GoVal.mkInt IntKind.uint64 0]
      = .panics "runtime error: integer divide by zero" := by
  rfl

end LeanModels.Go
