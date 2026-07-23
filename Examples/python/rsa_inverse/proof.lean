/-
Proof module for `Examples/python/rsa_inverse/spec.lean` (three-file example
layout; see Examples/python/tri/proof.lean for the pattern rationale). Every
theorem stated in spec.lean is proved here under the same name; the spec
side is `:= by proofs` (Surface.lean). Statements are duplicated between
the two files BY DESIGN; the spec-side reference typechecks the
duplication. This file loads its own copy of the program literal.

Target: python-rsa 4.9.1 `extended_gcd` / `inverse` (provenance in
rsa_inverse.py). This is the repo's six-variable real-world loop, and it
stresses the loop layer past `py_loop`'s v1 recipe in two ways — both
resolved WITHOUT framework changes (the generic while rule
`execWhile_total_of_invariant` is arity-generic as designed):

* THE GROWING ENVIRONMENT. `q` is first assigned inside the loop body, so
  the interpreter env has 8 bindings at loop entry (a, b, x, y, lx, ly,
  oa, ob) and 9 from the end of iteration 1 on (`Env.set` appends). A
  single `toEnv : σ → Env` cannot render both shapes, so the while rule
  cannot apply at loop entry. Resolution: unroll ONE iteration by hand
  (`rw [execWhile.eq_2]` + `py_simp` of the body at the concrete entry
  state), then apply the rule from the post-first-iteration state, where
  the env shape is stable. `q` joins the logical state as a 7th component
  with no invariant constraints; the loop-constant `oa`/`ob` stay fixed
  env entries of `egcdEnv`, not state components.

* THE RELATIONAL CONCLUSION. The returned Bezout coefficients are not a
  named function of the inputs, so the theorems are `∃ i j, …` — not the
  `CallsTo`-shaped goals `py_begin`/`py_loop` open (they commit to a known
  value). The proof therefore instantiates the while rule directly — the
  hand instantiation pattern that `py_loop` mechanized, here at arity 7.

The invariant (`egcdInv`): 0 < a, 0 ≤ b < a, gcd preservation, the two
Bezout identities a = lx·A + ly·B and b = x·A + y·B, and a
sign-alternation block: the coefficient pairs (x, lx) and (y, ly) carry
opposite signs (flipping each iteration, disjunction over the two
phases), with the exact magnitude identities |x|·a + |lx|·b = B and
|y|·a + |ly|·b = A carried *sign-expanded* per phase (no `natAbs` in the
invariant), plus the coefficient bounds 2|lx| ≤ B and |ly| ≤ A that make
the post-loop wrap of `lx`/`ly` land in [0, b) resp. [0, a].
-/
import LeanModels

namespace Examples.python.rsa_inverse.proof

open LeanModels LeanModels.Python

load_program rsa_inverse from "Examples/python/rsa_inverse/rsa_inverse.json"

/-! ## The loop, as mathematics -/

/-- Logical loop state `(a, b, x, y, lx, ly, q)` — the six Python loop
variables plus `q`, in the state because it is env-bound from iteration 1
on (module docstring). -/
private abbrev EgcdS : Type := Int × Int × Int × Int × Int × Int × Int

/-- The loop test `b != 0`, exactly as extracted (spans included): the
literal that the frozen `execWhile` occurrence carries, needed to
instantiate the while rule outside `py_loop`. -/
private def egcdTest : Expr :=
  .compare (.name "b" ⟨47, 10, 47, 11⟩) #[.notEq]
    #[.constant (.int 0) ⟨47, 15, 47, 16⟩] ⟨47, 10, 47, 16⟩

/-- The loop body `q = a // b; (a, b) = (b, a % b); (x, lx) = ((lx - (q * x)), x);
(y, ly) = ((ly - (q * y)), y)`, exactly as extracted. -/
private def egcdBody : List Stmt := [
  .assign #[.name "q" ⟨48, 8, 48, 9⟩]
    (.binOp (.name "a" ⟨48, 12, 48, 13⟩) .floorDiv (.name "b" ⟨48, 17, 48, 18⟩)
      ⟨48, 12, 48, 18⟩) ⟨48, 8, 48, 18⟩,
  .assign #[.tuple #[.name "a" ⟨49, 9, 49, 10⟩, .name "b" ⟨49, 12, 49, 13⟩] ⟨49, 8, 49, 14⟩]
    (.tuple #[.name "b" ⟨49, 18, 49, 19⟩,
      .binOp (.name "a" ⟨49, 21, 49, 22⟩) .mod (.name "b" ⟨49, 25, 49, 26⟩) ⟨49, 21, 49, 26⟩]
      ⟨49, 17, 49, 27⟩) ⟨49, 8, 49, 27⟩,
  .assign #[.tuple #[.name "x" ⟨50, 9, 50, 10⟩, .name "lx" ⟨50, 12, 50, 14⟩] ⟨50, 8, 50, 15⟩]
    (.tuple #[.binOp (.name "lx" ⟨50, 20, 50, 22⟩) .sub
        (.binOp (.name "q" ⟨50, 26, 50, 27⟩) .mult (.name "x" ⟨50, 30, 50, 31⟩) ⟨50, 26, 50, 31⟩)
        ⟨50, 20, 50, 32⟩,
      .name "x" ⟨50, 35, 50, 36⟩] ⟨50, 18, 50, 37⟩) ⟨50, 8, 50, 37⟩,
  .assign #[.tuple #[.name "y" ⟨51, 9, 51, 10⟩, .name "ly" ⟨51, 12, 51, 14⟩] ⟨51, 8, 51, 15⟩]
    (.tuple #[.binOp (.name "ly" ⟨51, 20, 51, 22⟩) .sub
        (.binOp (.name "q" ⟨51, 26, 51, 27⟩) .mult (.name "y" ⟨51, 30, 51, 31⟩) ⟨51, 26, 51, 31⟩)
        ⟨51, 20, 51, 32⟩,
      .name "y" ⟨51, 35, 51, 36⟩] ⟨51, 18, 51, 37⟩) ⟨51, 8, 51, 37⟩]

/-- Render a logical state into the stable 9-binding interpreter
environment; `oa`/`ob` are loop constants, fixed to the original `A`/`B`. -/
private def egcdEnv (A B : Int) (s : EgcdS) : Env :=
  [("a", .int s.1), ("b", .int s.2.1), ("x", .int s.2.2.1), ("y", .int s.2.2.2.1),
   ("lx", .int s.2.2.2.2.1), ("ly", .int s.2.2.2.2.2.1),
   ("oa", .int A), ("ob", .int B), ("q", .int s.2.2.2.2.2.2)]

/-- The body's logical effect (with `q' := a // b`, computed from the
incoming state): `(a, b, x, y, lx, ly, q) ↦ (b, a % b, lx - q'·x, ly - q'·y, x, y, q')`.
Written in projections, not a tuple match, so `egcdStep s` for abstract `s`
matches the environment the symbolic execution of the body produces. -/
private def egcdStep (s : EgcdS) : EgcdS :=
  (s.2.1, Int.fmod s.1 s.2.1,
   s.2.2.2.2.1 - Int.fdiv s.1 s.2.1 * s.2.2.1,
   s.2.2.2.2.2.1 - Int.fdiv s.1 s.2.1 * s.2.2.2.1,
   s.2.2.1, s.2.2.2.1, Int.fdiv s.1 s.2.1)

/-- Loop invariant over `(a, b, x, y, lx, ly, _)` relative to the original
arguments `A B` (holds from the end of iteration 1 on; see the module
docstring for the mathematical reading of the sign-alternation block). -/
private def egcdInv (A B : Int) : EgcdS → Prop
  | (a, b, x, y, lx, ly, _) =>
    0 < a ∧ 0 ≤ b ∧ b < a ∧ Int.gcd a b = Int.gcd A B ∧
    a = lx * A + ly * B ∧ b = x * A + y * B ∧
    ((0 ≤ x ∧ lx ≤ 0 ∧ y ≤ 0 ∧ 0 ≤ ly ∧
      x * a - lx * b = B ∧ ly * b - y * a = A ∧ -(2 * lx) ≤ B ∧ ly ≤ A) ∨
     (x ≤ 0 ∧ 0 ≤ lx ∧ 0 ≤ y ∧ ly ≤ 0 ∧
      lx * b - x * a = B ∧ y * a - ly * b = A ∧ 2 * lx ≤ B ∧ -ly ≤ A))

/-- The generic while rule `execWhile_total_of_invariant` (Surface.lean),
instantiated at arity 7 for the `extended_gcd` loop: from any invariant
state, some fuel runs the loop to completion, landing in an invariant
state where `b = 0`. The three interpreter obligations are discharged by
the `py_threshold` recipe; preservation of the sign-alternation block
flips the disjunct each iteration, its two nonlinear bound steps
(`2·x ≤ x·a ≤ B` for `a ≥ 2`) supplied as explicit `Int.mul_*`
monotonicity facts. -/
private theorem egcd_loop (A B : Int) :
    ∀ s, egcdInv A B s →
      ∃ s', egcdInv A B s' ∧ (!(s'.2.1 == 0)) = false ∧
        ∃ F, execWhile rsa_inverse F (egcdEnv A B s) egcdTest egcdBody [] =
          .ok (egcdEnv A B s', .next) := by
  refine execWhile_total_of_invariant rsa_inverse egcdTest egcdBody (egcdEnv A B)
    (egcdInv A B) (fun s => !(s.2.1 == 0)) egcdStep (fun s => s.2.1.toNat)
    (fun s => .bool (!(s.2.1 == 0))) ?htest ?htv ?hbody ?hinv ?hdec
  case htest =>
    intro s _hs
    py_threshold 32 [egcdEnv, egcdTest, ite_ok_bool]
  case htv =>
    intro s _hs; rfl
  case hbody =>
    intro s _hs hc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hc
    py_threshold 32 [egcdEnv, egcdBody, egcdStep, hc]
  case hinv =>
    rintro ⟨a, b, x, y, lx, ly, _q⟩ hs hc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hc
    simp only [egcdStep, egcdInv]
    obtain ⟨ha, hb, hba, hgcd, hbez1, hbez2, hsigns⟩ := hs
    have ha2 : (2 : Int) ≤ a := by omega
    have hq0 : 0 ≤ Int.fdiv a b := Int.fdiv_nonneg (by omega) (by omega)
    have hfmod : Int.fmod a b = a - b * Int.fdiv a b := Int.fmod_def a b
    have hm0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg (by omega) (by omega)
    have hmb : Int.fmod a b < b := Int.fmod_lt_of_pos a (by omega)
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · -- gcd preservation: Euclid's step over Python's `%`
      show Int.gcd b (Int.fmod a b) = Int.gcd A B
      rw [gcd_fmod_step (by omega) (by omega)]; exact hgcd
    · -- Bezout for the new a (= b): new lx = x, new ly = y
      exact hbez2
    · -- Bezout for the new b (= a % b = a - b·q): ring algebra from hfmod
      grind
    · -- the sign/identity/bound block flips phase
      rcases hsigns with ⟨hx, hlx, hy, hly, hid1, hid2, hbd1, hbd2⟩ |
                         ⟨hx, hlx, hy, hly, hid1, hid2, hbd1, hbd2⟩
      · refine Or.inr ?_
        have hqx : 0 ≤ Int.fdiv a b * x := Int.mul_nonneg hq0 hx
        have hqy : Int.fdiv a b * y ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos hq0 hy
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
        have hqx : Int.fdiv a b * x ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos hq0 hx
        have hqy : 0 ≤ Int.fdiv a b * y := Int.mul_nonneg hq0 hy
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
  case hdec =>
    rintro ⟨a, b, x, y, lx, ly, _q⟩ hs hc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hc
    obtain ⟨ha, hb, -⟩ := hs
    have hm0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg (by omega) (by omega)
    have hmb : Int.fmod a b < b := Int.fmod_lt_of_pos a (by omega)
    simp only [egcdStep]
    omega

/-! ## extended_gcd -/

set_option maxHeartbeats 1000000 in
/-- `Int`-typed core of `extended_gcd_total` (the public wrappers restate
it over the `PyInt` brand; `omega` consumes only unbranded comparisons —
AGENTS.md failure table). Structure: prove the invariant at the
post-first-iteration state `(b, a % b, 1, -(a // b), 0, 1, a // b)`, run
the while rule, extract `b' = 0` / `a' = gcd` / the coefficient ranges
from the exit invariant, then replay the interpreter: symbolic entry
execution, one hand-unrolled iteration, threshold splice of the loop run
(`execWhile_at_least`), and the epilogue under a four-way case split on
the two wrap conditions — the `lx' < 0 ∧ ly' < 0` case contradicts sign
alternation and dies without execution. -/
private theorem egcd_total_core (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    ∃ i j : Int,
      rsa_inverse.extended_gcd(a, b) ==> (((Int.gcd a b : Int), i, j) : Int × Int × Int) ∧
      0 ≤ i ∧ i < b ∧ (i * a) % b = (Int.gcd a b : Int) % b ∧
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : Int) % a := by
  have hb0 : b ≠ 0 := by omega
  -- the invariant holds after the (hand-unrolled) first iteration
  have hs₁ : egcdInv a b (b, Int.fmod a b, 1, -(Int.fdiv a b), 0, 1, Int.fdiv a b) := by
    have hq0 : 0 ≤ Int.fdiv a b := Int.fdiv_nonneg (by omega) (by omega)
    have hfmod : Int.fmod a b = a - b * Int.fdiv a b := Int.fmod_def a b
    have hm0 : 0 ≤ Int.fmod a b := Int.fmod_nonneg (by omega) (by omega)
    have hmb : Int.fmod a b < b := Int.fmod_lt_of_pos a (by omega)
    refine ⟨hb, hm0, hmb, gcd_fmod_step (by omega) (by omega), by omega, by grind, ?_⟩
    exact Or.inl ⟨by omega, by omega, by omega, by omega, by grind, by grind, by omega, by omega⟩
  obtain ⟨s', hinv', hcont', hex⟩ := egcd_loop a b _ hs₁
  obtain ⟨a', b', x', y', lx', ly', q'⟩ := s'
  simp only [egcdInv] at hinv'
  obtain ⟨hap, hbp, hbap, hgcd', hbez1, hbez2, hsigns⟩ := hinv'
  have hb'0 : b' = 0 := by simpa using hcont'
  subst hb'0
  -- at exit the gcd is a' itself (`gcd a' 0 = |a'|`, and a' > 0)
  have hag : a' = (Int.gcd a b : Int) := by
    rw [Int.gcd_zero_right] at hgcd'
    omega
  -- coefficient ranges, extracted from whichever sign phase the exit is in
  have hlxR : -b ≤ 2 * lx' ∧ 2 * lx' ≤ b := by
    rcases hsigns with ⟨-, h1, -, -, -, -, h2, -⟩ | ⟨-, h1, -, -, -, -, h2, -⟩ <;> omega
  have hlyR : -a ≤ ly' ∧ ly' ≤ a := by
    rcases hsigns with ⟨-, -, -, h1, -, -, -, h2⟩ | ⟨-, -, -, h1, -, -, -, h2⟩ <;> omega
  obtain ⟨fl, hl⟩ := execWhile_at_least hex
  -- normalize the loop fact to the literal shapes the goal will contain
  -- (module literal unfolded, projections reduced)
  py_simp [rsa_inverse, egcdEnv, egcdTest, egcdBody] at hl
  refine ⟨(if lx' < 0 then lx' + b else lx'), (if ly' < 0 then ly' + a else ly'),
    ?run, ?i0, ?ib, ?imod, ?j0, ?ja, ?jmod⟩
  case i0 => split <;> omega
  case ib => split <;> omega
  case j0 => split <;> omega
  case ja => split <;> omega
  case imod =>
    -- i·a ≡ gcd (mod b): from gcd = lx'·a + ly'·b, the wrap shifts by a·b
    split
    · have key : (lx' + b) * a = (Int.gcd a b : Int) + (a - ly') * b := by grind
      rw [key, Int.add_mul_emod_self_right]
    · have key : lx' * a = (Int.gcd a b : Int) + (-ly') * b := by grind
      rw [key, Int.add_mul_emod_self_right]
  case jmod =>
    split
    · have key : (ly' + a) * b = (Int.gcd a b : Int) + (b - lx') * a := by grind
      rw [key, Int.add_mul_emod_self_right]
    · have key : ly' * b = (Int.gcd a b : Int) + (-lx') * a := by grind
      rw [key, Int.add_mul_emod_self_right]
  case run =>
    by_cases hlx : lx' < 0 <;> by_cases hly : ly' < 0
    -- `lx' < 0 ∧ ly' < 0` contradicts sign alternation: no run needed
    · exfalso
      rcases hsigns with ⟨-, -, -, h, -, -, -, -⟩ | ⟨-, h, -, -, -, -, -, -⟩ <;> omega
    all_goals
      (refine ⟨fl + 64, ?_⟩
       rw [callFunction.eq_2]
       py_simp [rsa_inverse, hb0]
       rw [execWhile.eq_2]
       py_simp [hb0]
       simp (disch := omega) only [hl]
       py_simp [hlx, hly, hag])

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
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : PyInt) % a :=
  egcd_total_core a b ha hb

/-- Relational `⇓` form of `extended_gcd_total` (determinism corollary via
`CallsTo.typed_int3_eq`, Surface.lean): any `⇓`-bound triple result IS
`(gcd a b, i, j)` with the range and modular-Bezout facts. -/
theorem extended_gcd_spec (a b : PyInt) (r : PyInt × PyInt × PyInt)
    (ha : 0 < a) (hb : 0 < b) (h : rsa_inverse.extended_gcd(a, b) ⇓ r) :
    ∃ i j : PyInt, r = ((Int.gcd a b : PyInt), i, j) ∧
      0 ≤ i ∧ i < b ∧ (i * a) % b = (Int.gcd a b : PyInt) % b ∧
      0 ≤ j ∧ j ≤ a ∧ (j * b) % a = (Int.gcd a b : PyInt) % a := by
  obtain ⟨i, j, hrun, hrest⟩ := egcd_total_core a b ha hb
  exact ⟨i, j, CallsTo.typed_int3_eq h hrun, hrest⟩

set_option linter.unusedVariables false in
/-- Boundary `b = 0`: the loop never runs and `extended_gcd(a, 0)`
returns `(a, 1, 0)` — constant-fuel symbolic execution, no loop rule
(cf. `tri_neg_total`). `ha` is not consumed by the proof (the run is the
same for `a < 0`); it is kept because it is what makes the *reading*
`a = gcd(a, 0)` with Bezout `1·a + 0·0 = a` true (statement discipline:
hypotheses document the spec's domain, AGENTS.md). -/
theorem extended_gcd_zero (a : PyInt) (ha : 0 ≤ a) :
    rsa_inverse.extended_gcd(a, 0) ==> ((a, 1, 0) : PyInt × PyInt × PyInt) :=
  CallsTo.intro 32 (by py_simp [callFunction, execWhile, rsa_inverse])

/-! ## inverse -/

set_option maxHeartbeats 1000000 in
/-- `Int`-typed core of `inverse_spec` — TOTAL correctness on coprime
inputs, by callee-spec composition: splice `egcd_total_core`'s run at the
call site in threshold form (`py_lift`), then finish symbolically. The
coprimality hypothesis rewrites the returned gcd to 1, so the guard
`divider != 1` is concretely false and symbolic execution never touches
the `raise NotRelativePrimeError(…)` statement — the function's single
out-of-tier (`Unsupported`) node is proven unreachable rather than
modeled. -/
private theorem inverse_spec_core (x n : Int) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) :
    ∃ r : Int, 0 ≤ r ∧ r < n ∧ (r * x) % n = 1 ∧
      rsa_inverse.inverse(x, n) ==> r := by
  obtain ⟨i, j, hrun, hi0, hib, himod, hj0, hja, hjmod⟩ :=
    egcd_total_core x n hx (by omega)
  rw [hco] at hrun himod
  simp only [Int.natCast_one] at hrun himod
  rw [show (1:Int) % n = 1 from Int.emod_eq_of_lt (by omega) (by omega)] at himod
  refine ⟨i, hi0, hib, himod, ?_⟩
  py_lift ⟨f₀, hcall⟩ := hrun with [rsa_inverse]
  refine ⟨f₀ + 32, ?_⟩
  rw [callFunction.eq_2]
  py_simp [rsa_inverse]
  simp (disch := omega) only [hcall]
  py_simp

/-- **Total correctness of the shipped `inverse`** (python-rsa 4.9.1): on
coprime inputs `0 < x`, `1 < n`, it terminates and returns the modular
inverse — the unique `r` with `0 ≤ r < n` and `r·x ≡ 1 (mod n)`. The
`raise NotRelativePrimeError` branch (the function's single out-of-tier
node) is unreachable under `gcd x n = 1`; see `inverse_spec_core`. -/
theorem inverse_spec (x n : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) :
    ∃ r : PyInt, 0 ≤ r ∧ r < n ∧ (r * x) % n = 1 ∧
      rsa_inverse.inverse(x, n) ==> r :=
  inverse_spec_core x n hx hn hco

/-- Typed relational corollary of `inverse_spec` (determinism modulo
fuel): ANY `⇓`-bound result of `inverse(x, n)` on coprime inputs is a
canonical modular inverse. -/
theorem inverse_correct (x n r : PyInt) (hx : 0 < x) (hn : 1 < n)
    (hco : Int.gcd x n = 1) (h : rsa_inverse.inverse(x, n) ⇓ r) :
    0 ≤ r ∧ r < n ∧ (r * x) % n = 1 := by
  obtain ⟨r₀, h0, h1, h2, hrun⟩ := inverse_spec_core x n hx hn hco
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
  obtain ⟨r₀, -, -, -, hrun⟩ := inverse_spec_core x n hx hn hco
  exact hrun.partialTo.not_raises hraise

end Examples.python.rsa_inverse.proof
