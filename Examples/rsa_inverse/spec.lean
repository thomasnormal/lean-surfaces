/-
Examples/rsa_inverse — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): rsa_inverse.py (vendored BYTE-VERBATIM from the
python-rsa package — provenance in its module docstring), rsa_inverse.json
(generated envelope), THIS FILE (statements, `:= by proofs`), proof.lean
(the real proofs, namespace `Examples.rsa_inverse.proof`).

REAL-WORLD TARGET: `rsa.common.extended_gcd` / `rsa.common.inverse` from
python-rsa 4.9.1 (rsa/common.py, sha256
c3452e5791cdbe4142e2c04c8cc0cef094d4242a17bec2f372826b02eab32e90) — the
modular-inverse routine of a security-critical, heavily-downloaded PyPI
package, proved correct against its ACTUAL shipped source.

Tier facts (envelope, extractor run 2026-07-21):
* `extended_gcd(a, b)` — fully in-tier, zero Unsupported nodes;
  `args_unsupported`/`locals_unsupported` both null. Node kinds: Assign
  (incl. tuple-unpack `(a, b) = (b, a % b)`), AugAssign:Add,
  BinOp FloorDiv/Mod/Mult/Sub, Compare Lt/NotEq, Constant, Expr
  (docstring), If, Name, Return, Tuple, While.
* `inverse(x, n)` — in-tier except EXACTLY ONE Unsupported node: the
  `raise NotRelativePrimeError(x, n, divider)` statement (rsa_inverse.py
  line 71). `inverse_spec` covers precisely that node with an
  unreachability argument: coprime inputs ⇒ divider = 1 ⇒ the `if` guard
  is concretely false ⇒ symbolic execution never reaches the raise.
  Out-of-tier code is fine when proven unreachable — the interpreter
  refuses it loudly everywhere else (the `#guard … matches .unsupported`
  line below documents the edge: NON-coprime input does reach it).

Authenticity: every expected value below was computed with Python 3.9.25
against the vendored file AND against the installed rsa==4.9.1 package
(pip, 2026-07-21) — both agree; the same rows run through the CPython
differential harness (harness/cases.json, incl. the non-coprime
`unsupported` row).
-/
import Examples.rsa_inverse.proof

open LeanModels LeanModels.Python

load_program rsa_inverse from "Examples/rsa_inverse/rsa_inverse.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired).
Tuple results use the typed int-triple marshalling (`ToVal
(PyInt × PyInt × PyInt)`, Surface.lean — added for this example). -/
#py_check rsa_inverse.inverse(3, 7) = 5
#py_check rsa_inverse.inverse(7, 40) = 23
#py_check rsa_inverse.inverse(17, 3120) = 2753
#py_check rsa_inverse.inverse(1, 2) = 1
#py_check rsa_inverse.inverse(41, 7) = 6
#py_check rsa_inverse.extended_gcd(12, 18) = (((6, 17, 1) : PyInt × PyInt × PyInt))
#py_check rsa_inverse.extended_gcd(270, 192) = (((6, 5, 263) : PyInt × PyInt × PyInt))
#py_check rsa_inverse.extended_gcd(5, 0) = (((5, 1, 0) : PyInt × PyInt × PyInt))

/-! Tier-edge documentation: a NON-coprime `inverse` call reaches the
vendored `raise NotRelativePrimeError(…)` — the single Unsupported node —
and the interpreter refuses loudly (`.unsupported`, not a Python result),
so the check stays a raw `#guard … matches`. The theorems below prove the
node is unreachable on the coprime domain — never that it is absent. -/
#guard (callFunction rsa_inverse "inverse" #[.int 4, .int 6] 4096 matches .unsupported _)

/-! Spec-shape notes. `extended_gcd` returns coefficients that are not a
function of the inputs any spec would name, so its theorems are
RELATIONAL (`∃ i j, …`) — no Lean model function. Exact Bezout
`i·a + j·b = gcd` is deliberately NOT claimed: the two trailing `if`s
wrap a negative `lx` by the ORIGINAL b and a negative `ly` by the
ORIGINAL a, shifting each coefficient by a multiple of the other
argument, so it is false as shipped (`extended_gcd(3, 7) = (1, 5, 1)`,
`5·3 + 1·7 = 22 = 1 + 3·7`). The honest strengthening is modular Bezout
plus the wrap ranges — exactly what the Python docstring promises
("i = multiplicitive inverse of a mod b"). Positivity is load-bearing:
at `a = 0` the j-range fails (`extended_gcd(0, 5) = (5, 0, 1)`, j = 1 > a)
and at `b = 0` the i-range fails (`extended_gcd(5, 0) = (5, 1, 0)`,
i = 1 > b — see `extended_gcd_zero` for that boundary). No `@[spec]`
forms here: the relational/existential conclusions are not conditional
simp shapes (cf. Examples/add/spec.lean). -/

/-- **Total correctness of the shipped `extended_gcd`** (python-rsa 4.9.1,
positive inputs): it terminates and returns `(gcd a b, i, j)` with
`i·a ≡ gcd (mod b)`, `j·b ≡ gcd (mod a)`, `0 ≤ i < b`, `0 ≤ j ≤ a`.
Proof (six-variable loop, hand-instantiated generic while rule at arity 7
with a one-iteration pre-roll for the growing env): proof.lean. -/
theorem extended_gcd_total (a b : PyInt) (ha : 0 < a) (hb : 0 < b) :
    ∃ i j : PyInt,
      rsa_inverse.extended_gcd(a, b) ==> ((Int.gcd a b : PyInt), i, j) ∧
      0 ≤ i ∧ i < b ∧ (i * a) % b = (Int.gcd a b : PyInt) % b ∧
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : PyInt) % a := by proofs

/-- Relational `⇓` form: ANY result `extended_gcd(a, b)` evaluates to (at
any fuel) is `(gcd a b, i, j)` with the range and modular-Bezout facts —
a determinism corollary of `extended_gcd_total`
(`CallsTo.typed_int3_eq`, Surface.lean). -/
theorem extended_gcd_spec (a b : PyInt) (r : PyInt × PyInt × PyInt)
    (ha : 0 < a) (hb : 0 < b) (h : rsa_inverse.extended_gcd(a, b) ⇓ r) :
    ∃ i j : PyInt, r = ((Int.gcd a b : PyInt), i, j) ∧
      0 ≤ i ∧ i < b ∧ (i * a) % b = (Int.gcd a b : PyInt) % b ∧
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : PyInt) % a := by proofs

set_option linter.unusedVariables false in
/-- Boundary `b = 0`: the loop never runs and the result is `(a, 1, 0)` —
for `a ≥ 0` that reads `a = gcd(a, 0)` with exact Bezout `1·a + 0·0`
(the wrap ranges of `extended_gcd_total` are exactly what fails here;
see the spec-shape notes above). `ha` is not consumed by the
constant-fuel run; it is the domain on which this reading is true
(statement discipline — silenced unused-variable linter, cf.
`midpoint_nonneg`). -/
theorem extended_gcd_zero (a : PyInt) (ha : 0 ≤ a) :
    rsa_inverse.extended_gcd(a, 0) ==> ((a, 1, 0) : PyInt × PyInt × PyInt) := by proofs

/-- **Total correctness of the shipped `inverse` — the headline theorem.**
On coprime inputs (`0 < x`, `1 < n`, `gcd x n = 1`) `inverse(x, n)`
terminates and returns THE modular inverse: the unique `r` with
`0 ≤ r < n` and `(r * x) % n = 1`. The `raise NotRelativePrimeError`
branch — the function's single out-of-tier node — is proven UNREACHABLE
on this domain (coprimality forces `divider = 1`, the guard is
concretely false, symbolic execution never touches the raise), so the
theorem is total correctness of the byte-verbatim shipped source with
its exception path intact. -/
theorem inverse_spec (x n : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) :
    ∃ r : PyInt, 0 ≤ r ∧ r < n ∧ (r * x) % n = 1 ∧
      rsa_inverse.inverse(x, n) ==> r := by proofs

/-- Typed relational corollary (determinism modulo fuel): ANY `⇓`-bound
result of `inverse(x, n)` on coprime inputs is a canonical modular
inverse — the form a caller composes with. -/
theorem inverse_correct (x n r : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) (h : rsa_inverse.inverse(x, n) ⇓ r) :
    0 ≤ r ∧ r < n ∧ (r * x) % n = 1 := by proofs

/-- On coprime inputs `inverse` can raise NOTHING — the falsifiable
exception-freedom claim (totality + determinism exclude every `==>!`
outcome at every fuel; the naive "if it returns then v" partial reading
could not state this). In particular the vendored raise is dead code on
this domain. -/
theorem inverse_no_raise (x n : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) (e : PyErr) :
    ¬ rsa_inverse.inverse(x, n) ==>! e := by proofs
