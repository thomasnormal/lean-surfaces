/-
Proof module for `Examples/python/rsa_inverse/spec.lean` (three-file example
layout; see Examples/python/tri/proof.lean for the pattern rationale). Every
theorem stated in spec.lean is proved here under the same name; the spec
side is `:= by proofs` (Surface.lean). Statements are duplicated between
the two files BY DESIGN; the spec-side reference typechecks the
duplication. This file loads its own copy of the program literal.

Target: python-rsa 4.9.1 `extended_gcd` / `inverse` (provenance in
rsa_inverse.py) — the repo's six-variable real-world loop, proved by the
VC walker `py_vcgen` (VCTactic.lean) from ONE clause pair per function.
The two shapes that once forced a hand-instantiated while rule at arity 7
are now walker features:

* THE GROWING ENVIRONMENT. `q` is first assigned inside the loop body;
  it lives behind the invariant's symbolic environment tail, so there is
  no hand-unrolled first iteration. Instead the invariant carries the
  ENTRY STATE as an extra disjunct of its sign block (`EgcdPhase` below):
  preservation from that disjunct is the old "first iteration
  establishes the invariant" argument, verbatim.

* THE RELATIONAL CONCLUSION. The Bezout coefficients are not a function
  of the inputs any spec would name, so the core goal is the walker's
  relational entry form `∃ v, CallsTo … v ∧ Φ v`; the `∃ i j` witnesses
  inside `Φ` are solved by unification against the four wrap forks of
  the trailing `if`s (each fork closes from the exit facts — no
  interpreter replay, no threshold splicing).

The invariant (`EgcdPhase` + the linear conjuncts in the clause): 0 < a,
0 ≤ b, gcd preservation, the two Bezout identities (oriented sum-to-var,
so the walker's hypothesis rewrites leave the environment alone), and a
sign-alternation block — entry state, or `b < a` with coefficient pairs
`(x, lx)`/`(y, ly)` of opposite signs (flipping each iteration), the
magnitude identities sign-expanded per phase, and the bounds
`2|lx| ≤ B`, `|ly| ≤ A` that land the wrapped coefficients in `[0, b)`
resp. `[0, a]`. The `exit1` clause distills exactly what the wrap forks
consume. `EgcdPhase` is one abbrev so the residual splitter keeps the
disjunction whole (the phase case analysis happens HERE, not in the
walker).
-/
import LeanModels

namespace Examples.python.rsa_inverse.proof

open LeanModels LeanModels.Python

load_program rsa_inverse from "Examples/python/rsa_inverse/rsa_inverse.json"

/-- Sign block of the `extended_gcd` invariant: the entry state, or the
established alternation (module docstring). One abbrev, one residual. -/
private abbrev EgcdPhase (A B a b x y lx ly : Int) : Prop :=
  (a = A ∧ b = B ∧ x = 0 ∧ y = 1 ∧ lx = 1 ∧ ly = 0) ∨
  (b < a ∧
   ((0 ≤ x ∧ lx ≤ 0 ∧ y ≤ 0 ∧ 0 ≤ ly ∧
     x * a - lx * b = B ∧ ly * b - y * a = A ∧ -(2 * lx) ≤ B ∧ ly ≤ A) ∨
    (x ≤ 0 ∧ 0 ≤ lx ∧ 0 ≤ y ∧ ly ≤ 0 ∧
     lx * b - x * a = B ∧ y * a - ly * b = A ∧ 2 * lx ≤ B ∧ -ly ≤ A)))

set_option maxHeartbeats 4000000 in
/-- `Int`-typed relational core: `extended_gcd` terminates with
`(gcd A B, i, j)` where the coefficients satisfy the wrap ranges and the
modular Bezout identities. One `py_vcgen` call; residuals in walk order:
init (`0 ≤ B`, the phase block at entry), the exit distillation, the six
preservation leaves (the phase flip is the big one — its entry case is
the old first-iteration argument, its two nonlinear bound steps are
explicit `Int.mul_*` monotonicity facts), decrease, and the four wrap
forks (ranges by `omega`, each modular identity from one `grind` key). -/
private theorem egcd_core (A B : Int) (hA : 0 < A) (hB : 0 < B) :
    ∃ v, CallsTo rsa_inverse "extended_gcd" #[.int A, .int B] v ∧
      ∃ i j : Int, v = .tuple #[.int (Int.gcd A B : Nat), .int i, .int j] ∧
        0 ≤ i ∧ i < B ∧ (i * A) % B = (Int.gcd A B : Int) % B ∧
        0 ≤ j ∧ j ≤ A ∧ (j * B) % A = (Int.gcd A B : Int) % A := by
  py_vcgen [rsa_inverse]
    (inv := fun (a b x y lx ly : Int) =>
      0 < a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B ∧
      lx * A + ly * B = a ∧ x * A + y * B = b ∧ EgcdPhase A B a b x y lx ly)
    (dec := fun (a b x y lx ly : Int) => b.toNat)
    (exit1 := fun (a b x y lx ly : Int) =>
      lx * A + ly * B = (Int.gcd A B : Int) ∧ -B ≤ 2 * lx ∧ 2 * lx ≤ B ∧
      -A ≤ ly ∧ ly ≤ A ∧ a = (Int.gcd A B : Int))
  -- init: 0 ≤ B, then the phase block at the entry state
  · omega
  · exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- exit: collapse the invariant at b = 0 into the distilled exit facts
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcore
    subst hx
    have hag : a = (Int.gcd A B : Int) := by have := Int.gcd_zero_right a; omega
    have hR : (-B ≤ 2 * lx ∧ 2 * lx ≤ B) ∧ -A ≤ ly ∧ ly ≤ A := by
      rcases h6 with ⟨-, hb0, -⟩ | ⟨-, ⟨-, hlx, -, hly, -, -, hb1, hb2⟩ |
        ⟨-, hlx, -, hly, -, -, hb1, hb2⟩⟩ <;> omega
    exact ⟨a, 0, x, y, lx, ly, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h1, h2, h3, h4, h5, h6⟩, by omega, hR.1.1, hR.1.2, hR.2.1, hR.2.2, hag⟩
  -- preservation: the five linear conjuncts, then the phase flip
  · omega
  · exact Int.fmod_nonneg (by omega) (by omega)
  · rw [gcd_fmod_step (by omega) (by omega)]; exact hinv3
  · have hf := Int.fmod_def a b; grind
  · have hq0 : 0 ≤ a.fdiv b := Int.fdiv_nonneg (by omega) (by omega)
    have hf : a.fmod b = a - b * a.fdiv b := Int.fmod_def a b
    have hmb : a.fmod b < b := Int.fmod_lt_of_pos a (by omega)
    refine Or.inr ⟨hmb, ?_⟩
    rcases hinv6 with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨hba, hph⟩
    · exact Or.inl (by grind)  -- the first iteration lands in phase 1
    · have ha2 : (2 : Int) ≤ a := by omega
      rcases hph with ⟨hx, hlx, hy, hly, hid1, hid2, hbd1, hbd2⟩ |
                      ⟨hx, hlx, hy, hly, hid1, hid2, hbd1, hbd2⟩
      · refine Or.inr ?_
        have hqx : 0 ≤ a.fdiv b * x := Int.mul_nonneg hq0 hx
        have hqy : a.fdiv b * y ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hq0 hy
        refine ⟨by omega, hx, by omega, hy, by grind, by grind, ?_, ?_⟩
        · -- 2·x ≤ B: x·a ≤ B (identity, lx·b ≤ 0) and 2·x ≤ x·a (a ≥ 2)
          have h1 : x * a ≤ B := by
            have : lx * b ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hlx (by omega)
            omega
          have h2 : x * 2 ≤ x * a := Int.mul_le_mul_of_nonneg_left ha2 hx
          have h3 : x * 2 = 2 * x := Int.mul_comm x 2
          omega
        · -- -y ≤ A: -y·a ≤ A (identity, ly·b ≥ 0) and -y ≤ -y·a (a ≥ 1)
          have h1 : -(y * a) ≤ A := by
            have : 0 ≤ ly * b := Int.mul_nonneg hly (by omega)
            omega
          have h2 : -y * 1 ≤ -y * a := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
          have h3 : -y * a = -(y * a) := by grind
          omega
      · refine Or.inl ?_
        have hqx : a.fdiv b * x ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hq0 hx
        have hqy : 0 ≤ a.fdiv b * y := Int.mul_nonneg hq0 hy
        refine ⟨by omega, hx, by omega, hy, by grind, by grind, ?_, ?_⟩
        · have h1 : -(x * a) ≤ B := by
            have : 0 ≤ lx * b := Int.mul_nonneg hlx (by omega)
            omega
          have h2 : -x * 2 ≤ -x * a := Int.mul_le_mul_of_nonneg_left ha2 (by omega)
          have h3 : -x * a = -(x * a) := by grind
          have h4 : -x * 2 = -(2 * x) := by grind
          omega
        · have h1 : y * a ≤ A := by
            have : ly * b ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hly (by omega)
            omega
          have h2 : y * 1 ≤ y * a := Int.mul_le_mul_of_nonneg_left (by omega) hy
          omega
  -- decrease
  · have := Int.fmod_lt_of_pos a (show (0:Int) < b by omega)
    have := Int.fmod_nonneg (a := a) (by omega) (by omega)
    omega
  -- the four wrap forks: ranges by omega, each modular identity by one key
  all_goals first
    | omega
    | (obtain ⟨hbez, -, -, -, -, -⟩ := hcont
       first
         | rw [show (lx' + B) * A = (Int.gcd A B : Int) + (A - ly') * B by grind,
               Int.add_mul_emod_self_right]
         | rw [show lx' * A = (Int.gcd A B : Int) + (-ly') * B by grind,
               Int.add_mul_emod_self_right]
         | rw [show (ly' + A) * B = (Int.gcd A B : Int) + (B - lx') * A by grind,
               Int.add_mul_emod_self_right]
         | rw [show ly' * B = (Int.gcd A B : Int) + (-lx') * A by grind,
               Int.add_mul_emod_self_right])

/-- **Total correctness of the shipped `extended_gcd`** (python-rsa 4.9.1,
positive inputs): it terminates and returns `(gcd a b, i, j)` where the
returned coefficients satisfy the *modular* Bezout identities
`i·a ≡ gcd (mod b)` and `j·b ≡ gcd (mod a)` with the ranges `0 ≤ i < b`,
`0 ≤ j ≤ a` produced by the two trailing wrap-`if`s. Exact Bezout
`i·a + j·b = gcd` is deliberately NOT claimed — the wraps shift each
coefficient by a multiple of the other original argument, so it is false
as shipped (e.g. `extended_gcd(3, 7) = (1, 5, 1)` with `5·3 + 1·7 = 22`);
the modular form is the honest strengthening the docstring of the Python
source actually promises ("i = multiplicative inverse of a mod b"). -/
theorem extended_gcd_total (a b : PyInt) (ha : 0 < a) (hb : 0 < b) :
    ∃ i j : PyInt,
      rsa_inverse.extended_gcd(a, b) ==> ((Int.gcd a b : PyInt), i, j) ∧
      0 ≤ i ∧ i < b ∧ (i * a) % b = (Int.gcd a b : PyInt) % b ∧
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : PyInt) % a := by
  obtain ⟨v, hrun, i, j, rfl, h⟩ := egcd_core a b ha hb
  exact ⟨i, j, hrun, h⟩

/-- Relational `⇓` form of `extended_gcd_total` (determinism corollary via
`CallsTo.typed_int3_eq`, Surface.lean): any `⇓`-bound triple result IS
`(gcd a b, i, j)` with the range and modular-Bezout facts. -/
theorem extended_gcd_spec (a b : PyInt) (r : PyInt × PyInt × PyInt)
    (ha : 0 < a) (hb : 0 < b) (h : rsa_inverse.extended_gcd(a, b) ⇓ r) :
    ∃ i j : PyInt, r = ((Int.gcd a b : PyInt), i, j) ∧
      0 ≤ i ∧ i < b ∧ (i * a) % b = (Int.gcd a b : PyInt) % b ∧
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : PyInt) % a := by
  obtain ⟨i, j, hrun, hrest⟩ := extended_gcd_total a b ha hb
  exact ⟨i, j, CallsTo.typed_int3_eq h hrun, hrest⟩

set_option linter.unusedVariables false in
set_option maxRecDepth 4096 in
/-- Boundary `b = 0`: the loop never runs and `extended_gcd(a, 0)`
returns `(a, 1, 0)` — constant-fuel symbolic execution, no loop rule
(cf. `tri_neg_total`). `ha` is not consumed by the proof (the run is the
same for `a < 0`); it is kept because it is what makes the *reading*
`a = gcd(a, 0)` with Bezout `1·a + 0·0 = a` true (statement discipline:
hypotheses document the spec's domain, AGENTS.md). -/
theorem extended_gcd_zero (a : PyInt) (ha : 0 ≤ a) :
    rsa_inverse.extended_gcd(a, 0) ==> ((a, 1, 0) : PyInt × PyInt × PyInt) :=
  CallsTo.intro 32 (by py_simp [callFunction, callIn, execWhile, rsa_inverse])

/-- `Int`-typed core of `inverse_spec` — TOTAL correctness on coprime
inputs. Coprimality rewrites the callee fact's gcd to 1, and the closing
`py_vcgen` consumes it as a local `CallsTo` hypothesis at the call site;
the guard `divider != 1` is then concretely false, so the walk proves the
`raise NotRelativePrimeError(…)` — the function's single out-of-tier
(`Unsupported`) node — unreachable rather than modeling it. Zero
residuals. -/
private theorem inverse_core (x n : Int) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) :
    ∃ r : Int, 0 ≤ r ∧ r < n ∧ (r * x) % n = 1 ∧
      rsa_inverse.inverse(x, n) ==> r := by
  obtain ⟨v, hrun, i, j, rfl, hi0, hib, himod, -⟩ := egcd_core x n hx (by omega)
  rw [hco] at hrun himod
  simp only [Int.natCast_one] at hrun himod
  rw [show (1:Int) % n = 1 from Int.emod_eq_of_lt (by omega) (by omega)] at himod
  refine ⟨i, hi0, hib, himod, ?_⟩
  py_vcgen [rsa_inverse]

/-- **Total correctness of the shipped `inverse`** (python-rsa 4.9.1): on
coprime inputs `0 < x`, `1 < n`, it terminates and returns the modular
inverse — the unique `r` with `0 ≤ r < n` and `r·x ≡ 1 (mod n)`. The
`raise NotRelativePrimeError` branch (the function's single out-of-tier
node) is unreachable under `gcd x n = 1`; see `inverse_core`. -/
theorem inverse_spec (x n : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) :
    ∃ r : PyInt, 0 ≤ r ∧ r < n ∧ (r * x) % n = 1 ∧
      rsa_inverse.inverse(x, n) ==> r :=
  inverse_core x n hx hn hco

/-- Typed relational corollary of `inverse_spec` (determinism modulo
fuel): ANY `⇓`-bound result of `inverse(x, n)` on coprime inputs is a
canonical modular inverse. -/
theorem inverse_correct (x n r : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) (h : rsa_inverse.inverse(x, n) ⇓ r) :
    0 ≤ r ∧ r < n ∧ (r * x) % n = 1 := by
  obtain ⟨r₀, h0, h1, h2, hrun⟩ := inverse_core x n hx hn hco
  obtain rfl : r = r₀ := Val.int.inj (CallsTo.functional h hrun)
  exact ⟨h0, h1, h2⟩

/-- On coprime inputs `inverse` can raise NOTHING — totality plus
determinism (`CallsTo.partialTo` + `PartialTo.not_raises`) excludes every
exception outcome, at every fuel. Together with `inverse_spec` this also
rules out the `unsupported` outcome: the vendored `raise` (the one
out-of-tier node) really is dead code on this domain. -/
theorem inverse_no_raise (x n : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) (e : PyErr) :
    ¬ rsa_inverse.inverse(x, n) ==>! e := by
  intro hraise
  obtain ⟨r₀, -, -, -, hrun⟩ := inverse_core x n hx hn hco
  exact hrun.partialTo.not_raises hraise

end Examples.python.rsa_inverse.proof
