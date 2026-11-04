import LeanModels.Sv.Gen2
import LeanModels.Sv.PinAxioms
import LeanModels.Sv.CombGuard2Sound
import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.Hier2Gen

/-!
# Procedural loops as trip schemas (`LeanModels.Sv` — WS3, LOOP-NOTE G1, gate G-L0)

**Status: provisional over `run2`** (EXECUTION-PLAN §1 labels). Nothing imports this module.

A procedural `for` (`PStmt.forLoop it init cond step body`, `Param.lean`) keeps its structure:
its meaning is a fold of the body over the loop's **trip schema**, the iterator values it runs
with, computed from the header with no fuel. This file is the loop *domain*, the statement-level
run (`Denotes`, the seam primitives), the guard, the frame and Bridge S; the recurrence over the trips
is computed by the recognizer (`Loop2Frag.lean`).

## The trip schema

`TripSchema` is an indexed domain: `count` trips, trip `k : Fin count` running with the iterator
at `value k`. A list of values (`toList`) and `intRange` (`toList_arith_one`) are *derived* views,
never the definition. A nest of two loops is a `TripSchema2`: the outer schema and, per outer trip,
an inner schema that may depend on the outer iterator (`for (j = 0; j < i; j++)`).

## Agreement with the source header, read in 32-bit `int` arithmetic

The iterator of `for (int i = init; cond; step)` is a 32-bit signed `int`: it stores `init`'s value
wrapped to 32 bits (`int32`, the constant tier's `canonInt 32 true`, the reading `IEnv.int32` and
`PDesign.int32Agrees` use), and every step stores `i + δ` wrapped again (`iter32`). A schema
**agrees** with a header (`TripSchema.Agrees`, `HeaderAgrees`) when its values are exactly the
iterator values before each trip, the condition is nonzero at each of them, and zero at the value
after the last trip. Agreement determines the schema (`Agrees.unique`), so "the trip schema of a
header" is well defined without fuel; a header no schema agrees with (a runaway or wrapping loop)
has no meaning in the profile.

The step is decoded by `procStepDelta2` (`Param2.lean`, the trusted decoder: `++`, `--`, `+= c`,
`-= c` with `c > 0`); the condition is evaluated by `evalInt` under `env.bindVal it v`, exactly
the environment `instStmt2` instantiates the body in (the iterator shadows any outer binding of
its name: an outer iterator, or a parameter).

**Canonical headers** (`<`, `<=`, `>`, `>=` against a bound that does not move): `canonCount`
gives the trip count in closed form, refusing a header that runs away from its bound or whose exit
value leaves the 32-bit range (the iterator would wrap, and a simulator would not stop where the
unbounded reading does). `headerAgrees_canon` is the workhorse: the header's three pieces
characterized (initializer value, decoded step, the condition as a comparison) give agreement of
the arithmetic schema `arith (int32 i0) δ n`.

## The legacy instantiation

`instStmt2`'s `forLoop` arm still computes the trip list with fuel: `forValues2` runs the iteration
`forValuesFuel2` at the fuel master's `forFuel2` derives from the header (`c64ebdac`; before it, a
fixed 128). `forValuesFuel2_of_agrees` is the bridge: a
schema that agrees with the header, read without wrap, is what the legacy instantiation unrolls,
whenever its fuel exceeds the trip count. The new meaning does not depend on the legacy fuel.

## Recorded restriction

`int32Agrees`' restriction carries over: the model's bounds are unbounded `Int`s, a simulator's
`int` parameters are 32-bit. A header whose exit value is outside the 32-bit range has no agreeing
schema here (`canonCount` refuses it) although the legacy unbounded reading unrolls it.
-/

namespace LeanModels.Sv

namespace Loop2

/-! ## 32-bit `int` reading -/

/-- The value a 32-bit signed `int` holds after storing `v` (two's complement wrap). -/
abbrev int32 (v : Int) : Int := canonInt 32 true v

/-- `v` is a 32-bit signed `int` value. -/
abbrev InInt32 (v : Int) : Prop := -2147483648 ≤ v ∧ v < 2147483648

/-- The 32-bit reading, spelled with a literal modulus (`omega`'s form). -/
theorem int32_eq (v : Int) :
    int32 v = if 2147483648 ≤ v % 4294967296 then v % 4294967296 - 4294967296 else v % 4294967296 := by
  unfold int32 canonInt
  have h31 : ((2 : Int) ^ (32 - 1)) = 2147483648 := rfl
  have h32 : ((2 : Int) ^ 32) = 4294967296 := rfl
  have he : v % 4294967296 = v.emod 4294967296 := rfl
  rw [he]
  simp only [h31, h32]
  by_cases h : 2147483648 ≤ v.emod 4294967296 <;> simp [h]

/-- A value in range is stored unchanged. -/
theorem int32_of_inInt32 {v : Int} (h : InInt32 v) : int32 v = v := by
  obtain ⟨h1, h2⟩ := h
  rw [int32_eq]
  split <;> omega

@[simp] theorem int32_zero : int32 0 = 0 := int32_of_inInt32 ⟨by decide, by decide⟩

/-- A natural number below `2^31` is stored unchanged. -/
theorem int32_natCast {n : Nat} (h : n < 2147483648) : int32 n = n :=
  int32_of_inInt32 ⟨by omega, by omega⟩

/-- Every stored value is in range. -/
theorem int32_inInt32 (v : Int) : InInt32 (int32 v) := by
  rw [int32_eq]
  split <;> constructor <;> omega

/-- The iterator before trip `k` of a header that stores `i0` and steps by `δ`, on a 32-bit
`int`: `int i = init` stores `int32 i0`, and `i += δ` stores `int32 (i + δ)`. -/
def iter32 (i0 δ : Int) : Nat → Int
  | 0 => int32 i0
  | k + 1 => int32 (iter32 i0 δ k + δ)

/-- Without wrap the 32-bit iterator is the arithmetic one: if every value up to trip `n` is
in range, `iter32 i0 δ k = int32 i0 + k δ` for `k ≤ n`. -/
theorem iter32_eq {i0 δ : Int} {n : Nat}
    (hr : ∀ k, k ≤ n → InInt32 (int32 i0 + k * δ)) :
    ∀ k, k ≤ n → iter32 i0 δ k = int32 i0 + k * δ
  | 0, _ => by simp [iter32]
  | k + 1, hk => by
      rw [iter32, iter32_eq hr k (by omega)]
      have he : int32 i0 + k * δ + δ = int32 i0 + ((k + 1 : Nat) : Int) * δ := by
        rw [Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul, Int.add_assoc]
      rw [he, int32_of_inInt32 (hr (k + 1) hk)]

/-! ## Trip schemas -/

/-- **A trip schema**: `count` trips; trip `k` runs with the iterator at `value k`. -/
structure TripSchema where
  count : Nat
  value : Fin count → Int

namespace TripSchema

/-- The trip values in trip order: the derived list view. -/
def toList (S : TripSchema) : List Int := List.ofFn S.value

@[simp] theorem length_toList (S : TripSchema) : S.toList.length = S.count := by
  simp [toList]

theorem getElem_toList (S : TripSchema) {k : Nat} (h : k < S.toList.length) :
    S.toList[k] = S.value ⟨k, by simpa using h⟩ := by
  simp [toList]

/-- The arithmetic schema: `n` trips at `s, s + δ, …, s + (n-1)δ`. -/
def arith (s δ : Int) (n : Nat) : TripSchema := ⟨n, fun k => s + (k : Nat) * δ⟩

@[simp] theorem arith_count (s δ : Int) (n : Nat) : (arith s δ n).count = n := rfl

@[simp] theorem arith_value (s δ : Int) (n : Nat) (k : Fin n) :
    (arith s δ n).value k = s + (k : Nat) * δ := rfl

theorem toList_arith (s δ : Int) (n : Nat) :
    (arith s δ n).toList = (List.range n).map fun k : Nat => s + k * δ := by
  apply List.ext_getElem <;> simp [toList, arith]

/-- **The bridge to `intRange`**: a unit-step arithmetic schema's list is `intRange`. -/
theorem toList_arith_one (s : Int) (n : Nat) : (arith s 1 n).toList = intRange s n := by
  rw [toList_arith, intRange_eq_map]
  simp

/-! ### Agreement with a header -/

/-- **`S` agrees with a header**, read in 32-bit `int` arithmetic: the iterator starts at
`int32 i0` and steps by `δ` with 32-bit wrap (`iter32`); trip `k` runs at the `k`-th value, the
guard `g` (the condition at an iterator value) is nonzero there, and it is zero at the value after
the last trip. -/
structure Agrees (g : Int → Except String Int) (i0 δ : Int) (S : TripSchema) : Prop where
  value : ∀ k : Fin S.count, S.value k = iter32 i0 δ k
  run : ∀ k : Fin S.count, ∃ c, g (S.value k) = .ok c ∧ c ≠ 0
  exit : g (iter32 i0 δ S.count) = .ok 0

/-- **Agreement determines the schema.** -/
theorem Agrees.unique {g : Int → Except String Int} {i0 δ : Int} {S S' : TripSchema}
    (h : S.Agrees g i0 δ) (h' : S'.Agrees g i0 δ) : S = S' := by
  have stop : ∀ {A B : TripSchema}, A.Agrees g i0 δ → B.Agrees g i0 δ → ¬ A.count < B.count :=
    fun {A B} hA hB hl => by
      obtain ⟨c, hc, hne⟩ := hB.run ⟨A.count, hl⟩
      rw [hB.value] at hc
      dsimp only at hc
      rw [hA.exit] at hc
      exact hne (Except.ok.inj hc).symm
  have hc : S.count = S'.count := by
    have := @stop S S' h h'
    have := @stop S' S h' h
    omega
  obtain ⟨n, f⟩ := S
  obtain ⟨n', f'⟩ := S'
  simp only at hc
  subst hc
  congr
  funext k
  exact (h.value k).trans (h'.value k).symm

/-- The condition of a header at iterator value `v`: `cond` evaluated with the iterator bound to
`v` (`instStmt2`'s discipline: the binding shadows any outer binding of the name). -/
def guard (env : IEnv) (it : String) (cond : PExpr) (v : Int) : Except String Int :=
  evalInt (env.bindVal it v) cond

/-- **`S` is the trip schema of the header** `for (it = init; cond; step)` in `env`: the
initializer and the step decode, and `S` agrees with the header's 32-bit iteration. -/
def HeaderAgrees (env : IEnv) (it : String) (init cond step : PExpr) (S : TripSchema) : Prop :=
  ∃ i0 δ, evalInt env init = .ok i0 ∧ procStepDelta2 env it step = .ok δ ∧
    S.Agrees (guard env it cond) i0 δ

/-- At most one schema agrees with a header. -/
theorem HeaderAgrees.unique {env : IEnv} {it : String} {init cond step : PExpr}
    {S S' : TripSchema} (h : S.HeaderAgrees env it init cond step)
    (h' : S'.HeaderAgrees env it init cond step) : S = S' := by
  obtain ⟨i0, δ, hi, hs, ha⟩ := h
  obtain ⟨i0', δ', hi', hs', ha'⟩ := h'
  rw [hi] at hi'
  rw [hs] at hs'
  cases hi'
  cases hs'
  exact ha.unique ha'

end TripSchema

/-! ## Canonical headers: the closed-form trip count -/

/-- The comparisons of a canonical header `it <op> bound`. -/
inductive Cmp where
  | lt | le | gt | ge
deriving DecidableEq, Repr

/-- `v` passes the comparison against `B`. -/
def Cmp.holds : Cmp → Int → Int → Prop
  | .lt, v, B => v < B
  | .le, v, B => v ≤ B
  | .gt, v, B => B < v
  | .ge, v, B => B ≤ v

/-- The direction of a comparison: `+1` counts up to its bound, `-1` down. -/
def Cmp.sign : Cmp → Int
  | .lt | .le => 1
  | .gt | .ge => -1

/-- The strict upper bound `B'` with `c.holds v B ↔ c.sign * v < B'`. -/
def Cmp.bound : Cmp → Int → Int
  | .lt, B => B
  | .le, B => B + 1
  | .gt, B => -B
  | .ge, B => -B + 1

theorem Cmp.holds_iff (c : Cmp) (v B : Int) : c.holds v B ↔ c.sign * v < c.bound B := by
  cases c <;> simp only [Cmp.holds, Cmp.sign, Cmp.bound] <;> omega

/-- Trips of the strict ascending header `v < B` from `s` by `δ > 0`: `⌈(B - s) / δ⌉`, which is
`0` when `B ≤ s`. -/
def ascCount (s δ B : Int) : Nat := ((B - s + δ - 1) / δ).toNat

theorem ascCount_run {s δ B : Int} (hδ : 0 < δ) {k : Nat} (hk : k < ascCount s δ B) :
    s + k * δ < B := by
  unfold ascCount at hk
  have h1 := Int.ediv_mul_le (B - s + δ - 1) (b := δ) (by omega)
  generalize (B - s + δ - 1) / δ = q at hk h1
  have hq : (k : Int) + 1 ≤ q := by have := Int.lt_toNat.mp hk; omega
  have h2 := Int.mul_le_mul_of_nonneg_right hq (Int.le_of_lt hδ)
  rw [Int.add_mul, Int.one_mul] at h2
  omega

theorem ascCount_exit {s δ B : Int} (hδ : 0 < δ) : B ≤ s + (ascCount s δ B : Nat) * δ := by
  unfold ascCount
  have h1 := Int.lt_ediv_add_one_mul_self (B - s + δ - 1) hδ
  generalize (B - s + δ - 1) / δ = q at h1 ⊢
  rw [Int.add_mul, Int.one_mul] at h1
  by_cases hq : 0 ≤ q
  · rw [Int.toNat_of_nonneg hq]; omega
  · have hneg : q * δ ≤ -1 * δ := Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hδ)
    rw [Int.toNat_eq_zero.mpr (by omega)]
    simp only [Int.natCast_zero, Int.zero_mul, Int.add_zero]
    omega

/-- **The canonical trip count** of `it <c> B` from the start value `s` by the step `δ`: `0` when
the condition fails at the start; otherwise the header must move towards its bound (`c.sign * δ >
0`) and its exit value `s + n δ` must be a 32-bit `int` (else the iterator wraps); both failures
are loud. Fuel-free. -/
def canonCount (c : Cmp) (s δ B : Int) : Except String Nat :=
  if c.sign * s < c.bound B then
    if 0 < c.sign * δ then
      if InInt32 (s + (ascCount (c.sign * s) (c.sign * δ) (c.bound B) : Nat) * δ) then
        .ok (ascCount (c.sign * s) (c.sign * δ) (c.bound B))
      else .error "for loop: the exit value leaves the 32-bit int range (the iterator wraps)"
    else .error "for loop: the step moves away from the bound"
  else .ok 0

/-- What `canonCount` guarantees: the comparison holds at every trip value, fails at the exit
value, and every value up to the exit is a 32-bit `int`. -/
theorem canonCount_sound {c : Cmp} {s δ B : Int} {n : Nat} (hs : InInt32 s)
    (h : canonCount c s δ B = .ok n) :
    (∀ k, k < n → c.holds (s + k * δ) B) ∧ ¬ c.holds (s + n * δ) B ∧
      ∀ k, k ≤ n → InInt32 (s + k * δ) := by
  unfold canonCount at h
  split at h
  · rename_i hstart
    split at h
    · rename_i hdir
      split at h
      · rename_i hrange
        cases h
        -- `σ (s + k δ) = σ s + k (σ δ)`, with `σ = ±1`
        have hlin : ∀ k : Nat, c.sign * (s + k * δ) = c.sign * s + k * (c.sign * δ) := by
          intro k
          rw [Int.mul_add, Int.mul_left_comm]
        refine ⟨fun k hk => ?_, ?_, fun k hk => ?_⟩
        · rw [Cmp.holds_iff, hlin]; exact ascCount_run hdir hk
        · rw [Cmp.holds_iff, hlin]; have := ascCount_exit (s := c.sign * s) (B := c.bound B) hdir
          omega
        · -- monotone between the start and the exit value
          have hk' : (k : Int) ≤ (ascCount (c.sign * s) (c.sign * δ) (c.bound B) : Nat) := by
            exact_mod_cast hk
          obtain ⟨hs1, hs2⟩ := hs
          obtain ⟨hr1, hr2⟩ := hrange
          refine ⟨?_, ?_⟩ <;>
          cases c <;> simp only [Cmp.sign] at hdir <;>
            first
            | (have h1 := Int.mul_le_mul_of_nonneg_right hk' (by omega : (0 : Int) ≤ δ)
               have h2 := Int.mul_nonneg (Int.natCast_nonneg k) (by omega : (0 : Int) ≤ δ)
               omega)
            | (have h1 := Int.mul_le_mul_of_nonpos_right hk' (by omega : δ ≤ 0)
               have h2 := Int.mul_le_mul_of_nonpos_right (Int.natCast_nonneg k) (by omega : δ ≤ 0)
               simp only [Int.zero_mul] at h2
               omega)
      · cases h
    · cases h
  · rename_i hstart
    cases h
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), ?_, fun k hk => ?_⟩
    · rw [Cmp.holds_iff]; simpa using hstart
    · obtain rfl : k = 0 := by omega
      simpa using hs

/-- **Agreement of a canonical header.** The initializer evaluates to `i0`, the step decodes to
`δ`, and the condition at every 32-bit iterator value `v` is nonzero exactly when `v <c> B`; then
the arithmetic schema of `canonCount` is the header's trip schema. -/
theorem headerAgrees_canon {env : IEnv} {it : String} {init cond step : PExpr} {i0 δ B : Int}
    {c : Cmp} {n : Nat} (hinit : evalInt env init = .ok i0)
    (hstep : procStepDelta2 env it step = .ok δ)
    (hcond : ∀ v, InInt32 v → ∃ r, TripSchema.guard env it cond v = .ok r ∧ (r ≠ 0 ↔ c.holds v B))
    (hn : canonCount c (int32 i0) δ B = .ok n) :
    (TripSchema.arith (int32 i0) δ n).HeaderAgrees env it init cond step := by
  have hs : InInt32 (int32 i0) := int32_inInt32 i0
  obtain ⟨hrun, hexit, hrange⟩ := canonCount_sound hs hn
  have hit := iter32_eq (i0 := i0) (δ := δ) hrange
  refine ⟨i0, δ, hinit, hstep, ⟨fun k => ?_, fun k => ?_, ?_⟩⟩
  · rw [hit k.1 (Nat.le_of_lt k.2)]; rfl
  · obtain ⟨r, hr, hiff⟩ := hcond (int32 i0 + (k.1 : Int) * δ) (hrange k.1 (Nat.le_of_lt k.2))
    exact ⟨r, hr, hiff.mpr (hrun k.1 k.2)⟩
  · simp only [TripSchema.arith_count]
    rw [hit n (Nat.le_refl n)]
    obtain ⟨r, hr, hiff⟩ := hcond (int32 i0 + (n : Int) * δ) (hrange n (Nat.le_refl n))
    rw [hr]
    by_cases h0 : r = 0
    · rw [h0]
    · exact absurd (hiff.mp h0) hexit

/-! ## Discharging the header pieces (the tedium of every agreement) -/

/-- The signed comparison operator the extractor emits for each `Cmp` on `int` operands. -/
def Cmp.op : Cmp → SymBinOp
  | .lt => .slt
  | .le => .sle
  | .gt => .sgt
  | .ge => .sge

/-- **The guard of a canonical condition** `it <c> rhs`, the bound an INT-class expression that
evaluates to `B` whatever the iterator's value. -/
theorem guard_canon (c : Cmp) {env : IEnv} {it : String} {rhs : PExpr} {B : Int}
    (hri : ∀ v, rhs.isInt (env.bindVal it v) = true)
    (hrv : ∀ v, evalInt (env.bindVal it v) rhs = .ok B) (v : Int) :
    ∃ r, TripSchema.guard env it (.binary c.op (.genvarRef it) rhs) v = .ok r ∧
      (r ≠ 0 ↔ c.holds v B) := by
  have hg : (PExpr.genvarRef it).isInt (env.bindVal it v) = true := rfl
  have hgv := evalInt_genvarRef_bind (env := env) (g := it) (v := v)
  cases c
  · exact ⟨_, evalInt_slt_of hg (hri v) hgv (hrv v), by by_cases h : v < B <;> simp [h, Cmp.holds]⟩
  · exact ⟨_, evalInt_sle_of hg (hri v) hgv (hrv v), by by_cases h : v ≤ B <;> simp [h, Cmp.holds]⟩
  · exact ⟨_, evalInt_sgt_of hg (hri v) hgv (hrv v), by by_cases h : v > B <;> simp [h, Cmp.holds]⟩
  · exact ⟨_, evalInt_sge_of hg (hri v) hgv (hrv v),
      by by_cases h : v ≥ B <;> simp [h, Cmp.holds] <;> omega⟩

/-- `it++` steps by `1`. -/
@[simp] theorem procStepDelta2_inc (env : IEnv) (it : String) :
    procStepDelta2 env it (.unary .inc (.genvarRef it)) = .ok 1 := by
  simp [procStepDelta2]

/-- `it--` steps by `-1`. -/
@[simp] theorem procStepDelta2_dec (env : IEnv) (it : String) :
    procStepDelta2 env it (.unary .dec (.genvarRef it)) = .ok (-1) := by
  simp [procStepDelta2]

/-- `it += c` steps by `c` when `c` is a positive constant. -/
theorem procStepDelta2_add {env : IEnv} {it : String} {amount : PExpr} {c : Int}
    (h : evalInt env amount = .ok c) (hc : 0 < c) :
    procStepDelta2 env it (.binary (.m0 .add) (.genvarRef it) amount) = .ok c := by
  simp [procStepDelta2, h, hc]

/-- The ascending canonical count from a start below a strict bound, step `δ > 0`. -/
theorem canonCount_up {c : Cmp} {s δ B : Int} (hc : c.sign = 1) (hδ : 0 < δ)
    (hstart : c.sign * s < c.bound B)
    (hexit : InInt32 (s + (ascCount s δ (c.bound B) : Nat) * δ)) :
    canonCount c s δ B = .ok (ascCount s δ (c.bound B)) := by
  unfold canonCount
  have h1 : 0 < c.sign * δ := by rw [hc]; omega
  have h2 : c.sign * s = s := by rw [hc, Int.one_mul]
  have h3 : c.sign * δ = δ := by rw [hc, Int.one_mul]
  rw [if_pos hstart, if_pos h1, h2, h3, if_pos hexit]

/-- The descending canonical count from a start above a strict bound, step `δ < 0`. -/
theorem canonCount_down {c : Cmp} {s δ B : Int} (hc : c.sign = -1) (hδ : δ < 0)
    (hstart : c.sign * s < c.bound B)
    (hexit : InInt32 (s + (ascCount (-s) (-δ) (c.bound B) : Nat) * δ)) :
    canonCount c s δ B = .ok (ascCount (-s) (-δ) (c.bound B)) := by
  unfold canonCount
  have h1 : 0 < c.sign * δ := by rw [hc]; omega
  have h2 : c.sign * s = -s := by rw [hc, Int.neg_one_mul]
  have h3 : c.sign * δ = -δ := by rw [hc, Int.neg_one_mul]
  rw [if_pos hstart, if_pos h1, h2, h3, if_pos hexit]

/-- A header whose condition fails at the start runs `0` trips. -/
theorem canonCount_none {c : Cmp} {s δ B : Int} (hstart : ¬ c.sign * s < c.bound B) :
    canonCount c s δ B = .ok 0 := by
  unfold canonCount
  rw [if_neg hstart]

/-- `ascCount` at unit step: the distance. -/
theorem ascCount_one (s B : Int) : ascCount s 1 B = (B - s).toNat := by
  unfold ascCount
  rw [show B - s + 1 - 1 = B - s by omega, Int.ediv_one]

/-- `ascCount` at unit step from `s` to `s + n`: `n`. -/
theorem ascCount_one_add (s : Int) (n : Nat) : ascCount s 1 (s + n) = n := by
  rw [ascCount_one, show s + n - s = (n : Int) by omega]
  simp

/-- **`for (it = s; it < B; it++)` with `B = s + n`**: `n` trips. -/
theorem canonCount_lt_one {s B : Int} {n : Nat} (hn : B = s + n) (hB : InInt32 B) :
    canonCount .lt s 1 B = .ok n := by
  subst hn
  rcases n with _ | n
  · exact canonCount_none (by simp [Cmp.sign, Cmp.bound])
  · have hc : ascCount s 1 (Cmp.bound .lt (s + ((n + 1 : Nat) : Int))) = n + 1 :=
      ascCount_one_add s (n + 1)
    rw [canonCount_up (c := .lt) rfl (by decide) (by simp [Cmp.sign, Cmp.bound]; omega)
      (by rw [hc]; simpa using hB), hc]

/-- **`for (it = s; it <= B; it++)` with `B + 1 = s + n`**: `n` trips. -/
theorem canonCount_le_one {s B : Int} {n : Nat} (hn : B + 1 = s + n) (hB : InInt32 (B + 1)) :
    canonCount .le s 1 B = .ok n := by
  rcases n with _ | n
  · exact canonCount_none (by simp [Cmp.sign, Cmp.bound]; omega)
  · have hc : ascCount s 1 (Cmp.bound .le B) = n + 1 := by
      simp only [Cmp.bound]; rw [hn]; exact ascCount_one_add s (n + 1)
    rw [canonCount_up (c := .le) rfl (by decide) (by simp [Cmp.sign, Cmp.bound]; omega)
      (by rw [hc]; simp only [Int.mul_one]; rw [← hn]; exact hB), hc]

/-- **`for (it = s; it >= B; it--)` with `s = B + n - 1`**: `n` trips. -/
theorem canonCount_ge_dec {s B : Int} {n : Nat} (hn : s + 1 = B + n) (hB : InInt32 (B - 1)) :
    canonCount .ge s (-1) B = .ok n := by
  rcases n with _ | n
  · exact canonCount_none (by simp [Cmp.sign, Cmp.bound]; omega)
  · have hc : ascCount (-s) (-(-1)) (Cmp.bound .ge B) = n + 1 := by
      simp only [Cmp.bound, Int.neg_neg]
      rw [show -B + 1 = -s + ((n + 1 : Nat) : Int) by omega]
      exact ascCount_one_add (-s) (n + 1)
    rw [canonCount_down (c := .ge) rfl (by decide) (by simp [Cmp.sign, Cmp.bound]; omega)
      (by rw [hc]; rw [show s + ((n + 1 : Nat) : Int) * -1 = B - 1 by omega]; exact hB), hc]

/-! ## The trip schema computed from a canonical header (fuel-free) -/

/-- The comparison of a signed `int` condition operator. -/
def Cmp.ofOp? : SymBinOp → Option Cmp
  | .slt => some .lt
  | .sle => some .le
  | .sgt => some .gt
  | .sge => some .ge
  | _ => none

theorem Cmp.ofOp?_eq {op : SymBinOp} {c : Cmp} (h : Cmp.ofOp? op = some c) : op = c.op := by
  cases op <;> simp [Cmp.ofOp?] at h <;> subst h <;> rfl

/-- The value of a canonical bound: a literal, a parameter, or an outer iterator — never the
loop's own iterator, so it reads the same at every trip (`boundAt?_sound`). Anything else is not
decoded (the header stays outside the canonical tier, loudly). -/
def boundAt? (env : IEnv) (it : String) : PExpr → Option Int
  | .int k => some k
  | .paramRef n none => if n = it then none else env.vals.lookup n
  | .genvarRef g => if g = it then none else env.vals.lookup g
  | _ => none

theorem boundAt?_sound {env : IEnv} {it : String} {rhs : PExpr} {B : Int}
    (h : boundAt? env it rhs = some B) (v : Int) :
    rhs.isInt (env.bindVal it v) = true ∧ evalInt (env.bindVal it v) rhs = .ok B := by
  cases rhs with
  | int k => simp only [boundAt?, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | paramRef n p =>
      cases p with
      | some _ => simp [boundAt?] at h
      | none =>
          simp only [boundAt?] at h
          split at h
          · cases h
          · rename_i hne
            have hl : (env.bindVal it v).vals.lookup n = some B := by
              rw [vals_lookup_bindVal_ne v hne, h]
            exact ⟨isInt_paramRef_of hl, evalInt_paramRef_of hl⟩
  | genvarRef g =>
      simp only [boundAt?] at h
      split at h
      · cases h
      · rename_i hne
        exact ⟨rfl, evalInt_genvarRef_of (by rw [vals_lookup_bindVal_ne v hne, h])⟩
  | _ => simp [boundAt?] at h

/-- **The trip schema of a canonical header, computed with no fuel**: the initializer's value
read as an `int`, the decoded step, and the condition `it <op> bound` with a signed comparison
against a literal, a parameter or an outer iterator, counted in closed form (`canonCount`). Every
other header is refused, naming why. -/
def headerSchema (env : IEnv) (it : String) (init cond step : PExpr) : Except String TripSchema :=
  match evalInt env init, procStepDelta2 env it step, cond with
  | .ok i0, .ok δ, .binary op (.genvarRef g) rhs =>
      match Cmp.ofOp? op, boundAt? env it rhs with
      | some c, some B =>
          if g = it then (canonCount c (int32 i0) δ B).map (TripSchema.arith (int32 i0) δ)
          else .error "for condition does not test the loop's own iterator"
      | _, _ => .error "for condition outside the canonical tier (a signed comparison of the iterator with a literal, a parameter or an outer iterator)"
  | .error e, _, _ => .error s!"for initializer: {e}"
  | _, .error e, _ => .error s!"for step: {e}"
  | _, _, _ => .error "for condition outside the canonical tier"

/-- **The computed schema agrees with its header** (so it is THE trip schema,
`TripSchema.HeaderAgrees.unique`). -/
theorem headerSchema_agrees {env : IEnv} {it : String} {init cond step : PExpr} {S : TripSchema}
    (h : headerSchema env it init cond step = .ok S) : S.HeaderAgrees env it init cond step := by
  unfold headerSchema at h
  split at h
  · rename_i i0 δ op g rhs hinit hstep
    split at h
    · rename_i c B hop hB
      split at h
      · rename_i hg
        subst hg
        cases hn : canonCount c (int32 i0) δ B with
        | error e => rw [hn] at h; cases h
        | ok n =>
            rw [hn] at h
            cases h
            rw [Cmp.ofOp?_eq hop]
            exact headerAgrees_canon hinit hstep
              (fun v _ => guard_canon c (fun v => (boundAt?_sound hB v).1)
                (fun v => (boundAt?_sound hB v).2) v) hn
      · cases h
    · cases h
  all_goals cases h

/-! ## Nests: the inner schema depends on the outer trip -/

/-- **A two-level nest**: the outer schema and, for each outer trip `k`, the inner schema (which
may depend on the outer iterator value, as in `for (j = 0; j < i; j++)`). -/
structure TripSchema2 where
  outer : TripSchema
  inner : Fin outer.count → TripSchema

namespace TripSchema2

/-- The nest's trips in execution order, as (outer value, inner value) pairs: a derived view. -/
def toList (S : TripSchema2) : List (Int × Int) :=
  (List.finRange S.outer.count).flatMap fun k => (S.inner k).toList.map fun v => (S.outer.value k, v)

/-- **`S` is the schema of the nest** `for (it₁ = …) for (it₂ = …)`: the outer header agrees with
`S.outer` in `env`, and the inner header of outer trip `k` agrees with `S.inner k` in `env` with
the outer iterator bound to its trip value (`instStmt2` instantiates the outer body there). -/
def HeaderAgrees (env : IEnv) (it₁ : String) (init₁ cond₁ step₁ : PExpr) (it₂ : String)
    (init₂ cond₂ step₂ : PExpr) (S : TripSchema2) : Prop :=
  S.outer.HeaderAgrees env it₁ init₁ cond₁ step₁ ∧
    ∀ k : Fin S.outer.count,
      (S.inner k).HeaderAgrees (env.bindVal it₁ (S.outer.value k)) it₂ init₂ cond₂ step₂

/-- At most one nest schema agrees with a pair of headers. -/
theorem HeaderAgrees.unique {env : IEnv} {it₁ it₂ : String} {init₁ cond₁ step₁ init₂ cond₂ step₂ : PExpr}
    {S S' : TripSchema2}
    (h : S.HeaderAgrees env it₁ init₁ cond₁ step₁ it₂ init₂ cond₂ step₂)
    (h' : S'.HeaderAgrees env it₁ init₁ cond₁ step₁ it₂ init₂ cond₂ step₂) : S = S' := by
  obtain ⟨o, f⟩ := S
  obtain ⟨o', f'⟩ := S'
  have ho : o = o' := h.1.unique h'.1
  subst ho
  congr
  funext k
  exact (h.2 k).unique (h'.2 k)

end TripSchema2

/-! ## Rows: a statement as a function on states (gate G-L1)

`Denotes I s g`: on every state satisfying `I`, the statement `s` runs to `g st` with no
nonblocking write, at every fuel from ONE bound on (the same for all `I`-states, which is what
`Terminates2` needs). The fuel stays inside the existential, as in `Runs2`; no definition below
mentions it. The seam primitives (`Denotes.block`, `DenotesL.cons`, `Denotes.assignSlice` here, the
rest in `Loop2Rows`/`Loop2Frag`) are the only lemmas that open the interpreter; a loop's
instantiated block of trips needs no rule of its own (the recognizer's `listStep_range` reads it as
a recurrence over the trips, proved once, by induction on the trip count). -/

/-- **`s` denotes `g` on the states `I`** (uniform fuel, no NBA). -/
def Denotes (I : SvState → Prop) (s : Stmt2) (g : SvState → SvState) : Prop :=
  ∃ F, ∀ st, I st → ∀ fuel, F ≤ fuel → execStmt2 fuel st [] s = .ok (g st, [])

/-- `Denotes` for a statement sequence (`execStmts2`). -/
def DenotesL (I : SvState → Prop) (ss : List Stmt2) (g : SvState → SvState) : Prop :=
  ∃ F, ∀ st, I st → ∀ fuel, F ≤ fuel → execStmts2 fuel st [] ss = .ok (g st, [])

theorem DenotesL.nil (I : SvState → Prop) : DenotesL I [] id :=
  ⟨1, fun st _ fuel h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [execStmts2]⟩

theorem DenotesL.cons {I : SvState → Prop} {s : Stmt2} {ss : List Stmt2} {g h : SvState → SvState}
    (hs : Denotes I s g) (hI : ∀ st, I st → I (g st)) (hss : DenotesL I ss h) :
    DenotesL I (s :: ss) (fun st => h (g st)) := by
  obtain ⟨F1, h1⟩ := hs
  obtain ⟨F2, h2⟩ := hss
  refine ⟨max F1 F2 + 1, fun st hst fuel hf => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [execStmts2, h1 st hst f (by omega), Res.ok_bind, h2 (g st) (hI st hst) f (by omega)]

theorem Denotes.block {I : SvState → Prop} {arr : Array Stmt2} {g : SvState → SvState}
    (h : DenotesL I arr.toList g) : Denotes I (.block arr) g := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F + 1, fun st hst fuel hf => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [execStmt2, hF st hst f (by omega)]

/-- `Denotes` on a smaller set of states. -/
theorem Denotes.weaken {I J : SvState → Prop} {s : Stmt2} {g : SvState → SvState}
    (h : Denotes I s g) (hJ : ∀ st, J st → I st) : Denotes J s g :=
  let ⟨F, hF⟩ := h
  ⟨F, fun st hst => hF st (hJ st hst)⟩

/-- **One generic trip that writes a constant slice**: `n[lo +: w] = e`, where `e` evaluates to
`val st` on every `I`-state from a fuel bound on and `n` is bound. -/
theorem Denotes.assignSlice {I : SvState → Prop} {n : String} {lo w : Nat} {e : Expr2}
    {val : SvState → LVec}
    (he : ∃ F, ∀ st, I st → ∀ fuel, F ≤ fuel → evalExpr2 fuel st e = .ok (val st))
    (hn : ∀ st, I st → ∃ old, SvState.lookup st n = some old) :
    Denotes I (.blockingAssign (.slice n lo w) e) fun st =>
      SvState.set st n (((SvState.lookup st n).getD default).insertAt lo ((val st).resizeU w)) := by
  obtain ⟨F, hF⟩ := he
  refine ⟨F + 1, fun st hst fuel hf => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨old, hold⟩ := hn st hst
  simp [execStmt2, hF st hst f (by omega), resolveLhs2, hold]

/-! ## The self-read guard over a trip family (gate G-L2)

`combGuardProc` (`CombGuard2.lean`) walks a body with the bits `M` written on every path so far and
the bits `A` some later statement may write. Its docstring's premise is a loop-free body; a loop's
instantiated block of trips is loop-free, so the walk applies as it is, and at a symbolic trip
count it is decided by ONE lemma rather than a walk: if every bit the body may write is already in
`M0` when the walk reaches it (the accumulator is cleared first, so every later read is of a
written bit), no read can violate (`GuardIn.admits`). The hypothesis is compositional over blocks
(`GuardIn.block`) and about one generic trip (`GuardIn.assign`): affine windows, closed by `omega`. -/

open CombGuard in
/-- Every bit of window `x` lies in `M`. -/
def Covered (M : List BWin) (x : BWin) : Prop := ∀ n i, x.Mem n i → InSet M n i

open CombGuard in
theorem subAll_pos : ∀ (bs : List BWin) (a p : BWin), p ∈ a.subAll bs → 0 < p.2.2
  | [], a, p, h => by
      simp only [BWin.subAll] at h
      split at h
      · simp at h
      · simp only [List.mem_singleton] at h; subst h; omega
  | b :: bs, a, p, h => by
      simp only [BWin.subAll, List.mem_flatMap] at h
      obtain ⟨q, _, hq⟩ := h
      exact subAll_pos bs q p hq

open CombGuard in
/-- A read can only violate where some later write is not yet covered. -/
theorem readsViol_covered {M A R : List BWin} (h : ∀ x ∈ A, Covered M x) :
    readsViol M A R = none := by
  unfold readsViol
  rw [List.findSome?_eq_none_iff]
  intro r _
  rw [List.findSome?_eq_none_iff]
  intro x hx
  rw [List.head?_eq_none_iff]
  cases hs : (r.inter x).subAll M with
  | nil => rfl
  | cons p ps =>
      have hpos := subAll_pos M (r.inter x) p (by rw [hs]; exact List.mem_cons_self ..)
      have hm := (BWin.mem_subAll M (r.inter x) (n := p.1) (i := p.2.1)).mp
        ⟨p, by rw [hs]; exact List.mem_cons_self .., rfl, Nat.le_refl _, by omega⟩
      exact absurd (h x hx _ _ (BWin.mem_inter.mp hm.1).2) hm.2

open CombGuard in
theorem mem_listMayW {wd : String → Option Nat} {x : BWin} :
    ∀ {ss : List Stmt2}, x ∈ Stmt2.listMayW wd ss → ∃ s ∈ ss, x ∈ s.mayW wd
  | [], h => by simp [Stmt2.listMayW] at h
  | s :: ss, h => by
      simp only [Stmt2.listMayW, List.mem_append] at h
      rcases h with h | h
      · exact ⟨s, List.mem_cons_self .., h⟩
      · obtain ⟨t, ht, hx⟩ := mem_listMayW h
        exact ⟨t, List.mem_cons_of_mem _ ht, hx⟩

open CombGuard in
/-- **`s` is guard-safe under `M0`**: everything it may write is covered by `M0`, and from any
must-set extending `M0`, with any later writes covered by `M0`, its walk finds no self-read. -/
def GuardIn (wd : String → Option Nat) (M0 : List BWin) (s : Stmt2) : Prop :=
  (∀ x ∈ s.mayW wd, Covered M0 x) ∧
    ∀ M A, (∀ x, Covered M0 x → Covered M x) → (∀ x ∈ A, Covered M0 x) →
      s.combViol wd M A = none

open CombGuard in
/-- One generic trip: an assignment whose target windows are covered. -/
theorem GuardIn.assign {wd : String → Option Nat} {M0 : List BWin} {t : Lhs2} {e : Expr2}
    (ht : ∀ x ∈ t.mayW wd, Covered M0 x) : GuardIn wd M0 (.blockingAssign t e) := by
  refine ⟨by simpa [Stmt2.mayW] using ht, fun M A hM hA => ?_⟩
  simp only [Stmt2.combViol]
  apply readsViol_covered
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hM x (ht x hx)
  · exact hM x (hA x hx)

open CombGuard in
/-- A sequence of guard-safe statements walks clean. -/
theorem GuardIn.list {wd : String → Option Nat} {M0 : List BWin} :
    ∀ (ss : List Stmt2) (M A : List BWin), (∀ s ∈ ss, GuardIn wd M0 s) →
      (∀ x, Covered M0 x → Covered M x) → (∀ x ∈ A, Covered M0 x) →
      Stmt2.listCombViol wd M A ss = none
  | [], _, _, _, _, _ => rfl
  | s :: ss, M, A, h, hM, hA => by
      simp only [Stmt2.listCombViol]
      rw [orElse_eq_none]
      refine ⟨(h s (List.mem_cons_self ..)).2 M _ hM fun x hx => ?_,
        GuardIn.list ss (M ++ s.mustW wd) A (fun t ht => h t (List.mem_cons_of_mem _ ht))
          (fun x hx n i hm => inSet_append.mpr (Or.inl (hM x hx n i hm))) hA⟩
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨t, ht, hxt⟩ := mem_listMayW hx
        exact (h t (List.mem_cons_of_mem _ ht)).1 x hxt
      · exact hA x hx

open CombGuard in
/-- A block of guard-safe statements is guard-safe. -/
theorem GuardIn.block {wd : String → Option Nat} {M0 : List BWin} {arr : Array Stmt2}
    (h : ∀ s ∈ arr.toList, GuardIn wd M0 s) : GuardIn wd M0 (.block arr) := by
  refine ⟨fun x hx => ?_, fun M A hM hA => ?_⟩
  · simp only [Stmt2.mayW] at hx
    obtain ⟨s, hs, hxs⟩ := mem_listMayW hx
    exact (h s hs).1 x hxs
  · simp only [Stmt2.combViol]
    exact GuardIn.list _ M A h hM hA

open CombGuard in
/-- **The guard admits a body `init; loop`** whose first statement must-writes `M0` without
reading anything and whose loop is guard-safe under `M0`. -/
theorem GuardIn.admits {wd : String → Option Nat} {M0 : List BWin} {init loop : Stmt2}
    (hinit : ∀ A, init.combViol wd [] A = none) (hM : init.mustW wd = M0)
    (hloop : GuardIn wd M0 loop) : (Stmt2.block #[init, loop]).combAdmits wd = true := by
  have h2 := hloop.2 ([] ++ init.mustW wd) (Stmt2.listMayW wd [] ++ [])
    (fun x hx => by simpa [hM] using hx) (by simp [Stmt2.listMayW])
  show ((init.combViol wd [] (Stmt2.listMayW wd [loop] ++ []) <|>
    (loop.combViol wd ([] ++ init.mustW wd) (Stmt2.listMayW wd [] ++ []) <|>
      Stmt2.listCombViol wd (([] ++ init.mustW wd) ++ loop.mustW wd) [] []))).isNone = true
  rw [hinit, h2]
  rfl

/-! ## Frame: trips that write one signal (gate G-L3, generic)

A loop whose every trip rewrites ONE signal `n` from its own value and a reading of the others
(that the write leaves alone) has value rows, `vrows`: the recurrence on `n`'s value. -/

/-- The value of signal `n` (the default when unbound). -/
def sig (st : SvState) (n : String) : LVec := (SvState.lookup st n).getD default

theorem set_set (st : SvState) (n : String) (v w : LVec) :
    SvState.set (SvState.set st n v) n w = SvState.set st n w := by
  induction st with
  | nil => simp [SvState.set]
  | cons kv rest ih =>
      obtain ⟨k, u⟩ := kv
      by_cases h : k = n <;> simp [SvState.set, h, ih]

theorem set_self {st : SvState} {n : String} {v : LVec} (h : SvState.lookup st n = some v) :
    SvState.set st n v = st := by
  induction st with
  | nil => simp [SvState.lookup] at h
  | cons kv rest ih =>
      obtain ⟨k, u⟩ := kv
      by_cases hk : k = n
      · subst hk; simp [SvState.lookup] at h; subst h; simp [SvState.set]
      · simp [SvState.lookup, hk] at h; simp [SvState.set, hk, ih h]

/-- The value rows: trip `k` rewrites the value by `h k r`. -/
def vrows {α : Type} (h : Nat → α → LVec → LVec) (r : α) : Nat → LVec → LVec
  | 0, v => v
  | k + 1, v => h k r (vrows h r k v)

theorem width_vrows {α : Type} {h : Nat → α → LVec → LVec} {r : α}
    (hw : ∀ k v, (h k r v).width = v.width) : ∀ l v, (vrows h r l v).width = v.width
  | 0, _ => rfl
  | l + 1, v => by rw [vrows, hw, width_vrows hw l v]

@[simp] theorem width_insertAt (v : LVec) (lo : Nat) (q : LVec) : (v.insertAt lo q).width = v.width := by
  simp [LVec.insertAt, LVec.width]

@[simp] theorem width_resizeU (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

/-! ## Bridge S: one `always_comb` process (gate G-L3, generic)

A design whose only process is one `always_comb` with a body that denotes an idempotent `f` on an
invariant `I`: every settle reaches `f` of its start in at most two passes, so every cycle's
snapshot is `f` of the applied inputs (`SingleComb.runs`) and every run completes
(`SingleComb.terminates`). The snapshot equals the body's final row, read off the process as
written, with no lowering. -/

/-- **A single-`always_comb` design** whose body denotes the idempotent `f` on the invariant `I`.
`noq` exists because master's `run2` (`Spec2.lean:132`) applies a post-hoc trace check to designs with a
qualified `case`, which `execStmt2` does not see. -/
structure SingleComb (d : Design2) (body : Stmt2) (I : SvState → Prop) (f : SvState → SvState) :
    Prop where
  procs : d.processes = #[.alwaysComb body]
  noq : body.hasQualifiedCase = false
  run : Denotes I body f
  inv : ∀ st, I st → I (f st)
  idem : ∀ st, I st → f (f st) = f st
  inputs : ∀ inputs st, I st → I (applyInputs2 d inputs st)
  init : I (initState2 d)

namespace SingleComb

variable {d : Design2} {body : Stmt2} {I : SvState → Prop} {f : SvState → SvState}

theorem combIndices (h : SingleComb d body I f) : d.combIndices = [0] := by
  simp [Design2.combIndices, h.procs, Process2.isCombPhase]

theorem edgeIndices (h : SingleComb d body I f) : d.edgeIndices = [] := by
  simp [Design2.edgeIndices, h.procs, Process2.isEdgePhase]

theorem resetIndices (h : SingleComb d body I f) (a b : SvState) : d.resetIndices a b = [] := by
  simp [Design2.resetIndices, h.procs]

/-- One settle pass runs the body once. -/
theorem pass (h : SingleComb d body I f) (σ : ScheduleOracle) : ∃ F, ∀ st k fuel, I st →
    F ≤ fuel → combPass2 d fuel st (σ.choose k d.combIndices) = .ok (f st) := by
  obtain ⟨F, hF⟩ := h.run
  refine ⟨F, fun st k fuel hst hf => ?_⟩
  rw [h.combIndices, List.perm_singleton.mp (σ.choose_perm k [0])]
  simp [combPass2, h.procs, runCombProcess2, hF st hst fuel hf]

/-- The settle reaches `f st` in at most two passes. -/
theorem settle (h : SingleComb d body I f) (σ : ScheduleOracle) : ∃ F, ∀ st k fuel, I st →
    F ≤ fuel → ∃ k', combSettle2 d σ fuel st k = .ok (f st, k') := by
  obtain ⟨F, hF⟩ := h.pass σ
  refine ⟨F + 2, fun st k fuel hst hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by omega⟩
  by_cases hb : (f st == st) = true
  · exact ⟨k + 1, by simp only [combSettle2, hF st k (g + 1) hst (by omega), Res.ok_bind, hb, if_true]⟩
  · refine ⟨k + 1 + 1, ?_⟩
    simp only [combSettle2, hF st k (g + 1) hst (by omega), Res.ok_bind, hb, if_false,
      Bool.false_eq_true]
    simp [hF (f st) (k + 1) g (h.inv st hst) (by omega), h.idem st hst]

/-- A cycle's snapshot is `f` of the applied inputs. -/
theorem cycle (h : SingleComb d body I f) (σ : ScheduleOracle) : ∃ F, ∀ inputs st k fuel, I st →
    F ≤ fuel → ∃ k', cycleStep2 d σ fuel inputs st k = .ok (f (applyInputs2 d inputs st), k') := by
  obtain ⟨F, hF⟩ := h.settle σ
  refine ⟨F, fun inputs st k fuel hst hf => ?_⟩
  obtain ⟨k1, h1⟩ := hF _ k fuel (h.inputs inputs st hst) hf
  obtain ⟨k2, h2⟩ := hF _ (k1 + 1) fuel (h.inv _ (h.inputs inputs st hst)) hf
  refine ⟨k2, ?_⟩
  rw [cycleStep2_of_noEdge h.edgeIndices h.resetIndices, h1, Res.ok_bind]
  simp only [h2, h.idem _ (h.inputs inputs st hst)]

/-- Every successful cycle from an `I`-state lands on `f` of the applied inputs. -/
theorem snapshot (h : SingleComb d body I f) {σ : ScheduleOracle} {fuel : Nat}
    {inputs st S : SvState} {k k' : Nat} (hst : I st)
    (hc : cycleStep2 d σ fuel inputs st k = .ok (S, k')) : S = f (applyInputs2 d inputs st) := by
  obtain ⟨F, hF⟩ := h.cycle σ
  obtain ⟨k2, h2⟩ := hF inputs st k F hst (Nat.le_refl F)
  exact congrArg Prod.fst (cycleStep2_det hc h2)

/-- **Bridge S, termination**: every schedule and stimulus completes. -/
theorem terminates (h : SingleComb d body I f) : Terminates2 d :=
  Terminates2.of_invariant I h.init (fun σ => by
    obtain ⟨F, hF⟩ := h.cycle σ
    exact ⟨F, fun inputs st k hst =>
      let ⟨k', hk⟩ := hF inputs st k F hst (Nat.le_refl F)
      ⟨_, k', hk, h.inv _ (h.inputs inputs st hst)⟩⟩)
    (by simp [h.procs, Process2.hasQualifiedCase, h.noq])

/-- **Bridge S, the snapshots**: snapshot `c` of a completed run is `f` of cycle `c`'s inputs
applied to a state of the run. -/
theorem runs (h : SingleComb d body I f) {σ : ScheduleOracle} {stim tr : List SvState}
    (hr : Runs2 d σ stim tr) {c : Nat} {inputs S : SvState} (hi : stim[c]? = some inputs)
    (hS : tr[c]? = some S) : ∃ prev, I prev ∧ S = f (applyInputs2 d inputs prev) := by
  have hall := hr.forall_of_step (I := I) h.init fun fuel inputs prev k st k' hp hc => by
    rw [h.snapshot hp hc]; exact h.inv _ (h.inputs _ _ hp)
  obtain ⟨fuel, inputs', prev, k, k', hi', hp, hc⟩ := hr.snapshot_step hS
  rw [hi] at hi'
  cases hi'
  have hIp : I prev := by
    cases c with
    | zero => simp at hp; subst hp; exact h.init
    | succ c => exact hall c prev (by simpa using hp)
  exact ⟨prev, hIp, h.snapshot hIp hc⟩

end SingleComb

/-! ## The legacy instantiation (`forValuesFuel2`, fuel) unrolls the schema -/

/-- The legacy iteration `forValuesFuel2.go` (unbounded `Int`, one fuel unit per trip and one for the
exit test) over a guard that holds at `s + k δ` for `k < n` and fails at `s + n δ` lists the
arithmetic schema, given fuel beyond `n`. -/
theorem forValuesFuel2_go_arith {env : IEnv} {it : String} {cond : PExpr} {δ : Int} :
    ∀ (n : Nat) (s : Int) (F : Nat), n < F →
      (∀ k, k < n → ∃ c, TripSchema.guard env it cond (s + k * δ) = .ok c ∧ c ≠ 0) →
      TripSchema.guard env it cond (s + n * δ) = .ok 0 →
      forValuesFuel2.go env it cond δ F s = .ok (TripSchema.arith s δ n).toList
  | n, s, 0, hF, _, _ => absurd hF (Nat.not_lt_zero n)
  | 0, s, F + 1, _, _, hexit => by
      simp only [Int.natCast_zero, Int.zero_mul, Int.add_zero] at hexit
      simp only [TripSchema.guard] at hexit
      simp [forValuesFuel2.go, hexit, TripSchema.toList, TripSchema.arith]
  | n + 1, s, F + 1, hF, hrun, hexit => by
      obtain ⟨c, hc, hne⟩ := hrun 0 (by omega)
      simp only [Int.natCast_zero, Int.zero_mul, Int.add_zero, TripSchema.guard] at hc
      have hshift : ∀ k : Nat, s + δ + k * δ = s + ((k + 1 : Nat) : Int) * δ := by
        intro k; rw [Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul]; omega
      have ih := forValuesFuel2_go_arith n (s + δ) F (by omega)
        (fun k hk => by rw [hshift]; exact hrun (k + 1) (by omega))
        (by rw [hshift]; exact hexit)
      have hne' : (c == 0) = false := by simpa using hne
      simp only [forValuesFuel2.go, hc, hne', ih, Bool.false_eq_true, if_false, Res.ok_bind]
      simp only [TripSchema.toList, TripSchema.arith, List.ofFn_succ, Fin.val_zero,
        Int.natCast_zero, Int.zero_mul, Int.add_zero, Fin.val_succ, hshift]

/-- **The legacy instantiation unrolls the trip schema.** If `S` agrees with the header and the
32-bit reading does not wrap (the iterator values up to the exit are the unbounded ones), then
`forValuesFuel2` at any fuel beyond `S.count + 1` returns `S.toList`. -/
theorem forValuesFuel2_of_agrees {env : IEnv} {it : String} {init cond step : PExpr} {i0 δ : Int}
    {S : TripSchema} (hinit : evalInt env init = .ok i0)
    (hstep : procStepDelta2 env it step = .ok δ) (hS : S.Agrees (TripSchema.guard env it cond) i0 δ)
    (hnowrap : ∀ k, k ≤ S.count → iter32 i0 δ k = i0 + k * δ) {F : Nat} (hF : S.count + 1 < F) :
    forValuesFuel2 env it init cond step F = .ok S.toList := by
  have hS' : S = TripSchema.arith i0 δ S.count := by
    obtain ⟨n, f⟩ := S
    simp only [TripSchema.arith, TripSchema.mk.injEq, heq_eq_eq, true_and]
    funext k
    exact (hS.value k).trans (hnowrap k.1 (Nat.le_of_lt k.2))
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [forValuesFuel2, hinit, hstep]
  rw [hS']
  apply forValuesFuel2_go_arith S.count i0 F' (by omega)
  · intro k hk
    have := hS.run ⟨k, hk⟩
    rwa [hS.value, hnowrap k (Nat.le_of_lt hk)] at this
  · have := hS.exit
    rwa [hnowrap S.count (Nat.le_refl _)] at this

/-! ## The one-driver rule for a single process (gate G-L3, generic) -/

theorem mem_drvWinsList {w : DrvWin} :
    ∀ {ss : List Stmt2}, w ∈ Stmt2.drvWinsList ss → ∃ s ∈ ss, w ∈ s.drvWins
  | [], h => by simp [Stmt2.drvWinsList] at h
  | s :: ss, h => by
      simp only [Stmt2.drvWinsList, List.mem_append] at h
      rcases h with h | h
      · exact ⟨s, List.mem_cons_self .., h⟩
      · obtain ⟨t, ht, hw⟩ := mem_drvWinsList h
        exact ⟨t, List.mem_cons_of_mem _ ht, hw⟩

/-- Every window `s` assigns is on the signal `n`. -/
def WritesOnly (n : String) (s : Stmt2) : Prop := ∀ w ∈ s.drvWins, w.1 = n

theorem WritesOnly.block {n : String} {arr : Array Stmt2} (h : ∀ s ∈ arr.toList, WritesOnly n s) :
    WritesOnly n (.block arr) := fun w hw => by
  simp only [Stmt2.drvWins] at hw
  obtain ⟨s, hs, hws⟩ := mem_drvWinsList hw
  exact h s hs w hws

/-- **A lone `always_comb` that writes one non-input signal passes the one-driver rule.** -/
theorem driversOk_single {names inputs : List String} {n : String} {body : Stmt2}
    (h : WritesOnly n body) (hn : n ∉ inputs) :
    driversOk names inputs [.alwaysComb body] = true := by
  simp only [driversOk, driverWins, Process2.drvWins, Process2.procWrites, Process2.procWins,
    procExclusiveOk, List.flatMap_cons, List.flatMap_nil, List.filter_nil, List.append_nil,
    drvWinsDisjoint, List.all_nil, Bool.true_and, List.all_eq_true, List.mem_map,
    Bool.and_true]
  rintro x ⟨w, hw, rfl⟩
  rw [h w hw]
  simpa using hn

/-- The legacy iteration of the canonical unit-step header `for (it = 0; it < bound; it++)` at
any fuel beyond `N + 1` lists `0..N-1` (unbounded `Int`). -/
theorem forValuesFuel2_upto {env : IEnv} {it : String} {rhs : PExpr} {N F : Nat}
    (hri : ∀ v, rhs.isInt (env.bindVal it v) = true)
    (hrv : ∀ v, evalInt (env.bindVal it v) rhs = .ok N) (hF : N + 1 < F) :
    forValuesFuel2 env it (.int 0) (.binary Cmp.lt.op (.genvarRef it) rhs)
      (.unary .inc (.genvarRef it)) F = .ok (intRange 0 N) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hg := guard_canon .lt hri hrv
  simp only [forValuesFuel2, evalInt_int, procStepDelta2_inc]
  rw [← TripSchema.toList_arith_one]
  apply forValuesFuel2_go_arith N 0 F' (by omega)
  · intro k hk
    obtain ⟨r, hr, hiff⟩ := hg (0 + k * 1)
    exact ⟨r, hr, hiff.mpr (by simp [Cmp.holds]; omega)⟩
  · obtain ⟨r, hr, hiff⟩ := hg (0 + N * 1)
    rw [hr]
    by_cases h0 : r = 0
    · rw [h0]
    · exact absurd (hiff.mp h0) (by simp [Cmp.holds])

/-- Master's header fuel at the canonical unit-step header: `N + 2`. -/
theorem forFuel2_upto {env : IEnv} {it : String} {rhs : PExpr} {N : Nat}
    (hb : evalInt env rhs = .ok N) :
    forFuel2 env it (.int 0) (.binary Cmp.lt.op (.genvarRef it) rhs) (.unary .inc (.genvarRef it))
      = .ok (N + 2) := by
  by_cases h0 : N = 0
  · subst h0
    simp [forFuel2, Cmp.op, hb, Gen2.except_ok_bind]
    rfl
  · have hpos : 0 < N := Nat.pos_of_ne_zero h0
    have hneg : ¬ ((N : Int) < 0) := by omega
    simp [forFuel2, Cmp.op, hb, Gen2.except_ok_bind, hpos, hneg]
    rfl

/-- **The canonical unit-step header unrolls to `intRange 0 N`** in the instantiation `sem` uses
(`forValues2`: `forValuesFuel2` at `forFuel2`'s fuel), for every `N`. -/
theorem forValues2_upto {env : IEnv} {it : String} {rhs : PExpr} {N : Nat}
    (hri : ∀ v, rhs.isInt (env.bindVal it v) = true)
    (hrv : ∀ v, evalInt (env.bindVal it v) rhs = .ok N) (hb : evalInt env rhs = .ok N) :
    forValues2 env it (.int 0) (.binary Cmp.lt.op (.genvarRef it) rhs) (.unary .inc (.genvarRef it))
      = .ok (intRange 0 N) := by
  rw [forValues2, forFuel2_upto hb]
  exact forValuesFuel2_upto hri hrv (by omega)

end Loop2

#pin_axioms Loop2.int32_eq Loop2.int32_of_inInt32 Loop2.int32_zero Loop2.int32_natCast
  Loop2.int32_inInt32 Loop2.iter32_eq Loop2.TripSchema.length_toList Loop2.TripSchema.getElem_toList
  Loop2.TripSchema.toList_arith Loop2.TripSchema.toList_arith_one Loop2.TripSchema.Agrees.unique
  Loop2.TripSchema.HeaderAgrees.unique Loop2.Cmp.holds_iff Loop2.ascCount_run Loop2.ascCount_exit
  Loop2.canonCount_sound Loop2.headerAgrees_canon Loop2.guard_canon Loop2.procStepDelta2_inc
  Loop2.procStepDelta2_dec Loop2.procStepDelta2_add Loop2.canonCount_up Loop2.canonCount_down
  Loop2.canonCount_none Loop2.ascCount_one Loop2.ascCount_one_add Loop2.canonCount_lt_one
  Loop2.canonCount_le_one Loop2.canonCount_ge_dec vals_lookup_bindVal_self
  vals_lookup_bindVal_ne Loop2.Cmp.ofOp?_eq Loop2.boundAt?_sound Loop2.headerSchema_agrees
  Loop2.TripSchema2.HeaderAgrees.unique Loop2.forValuesFuel2_go_arith Loop2.forValuesFuel2_of_agrees
  Loop2.Denotes.weaken Loop2.DenotesL.nil Loop2.DenotesL.cons Loop2.Denotes.block Loop2.Denotes.assignSlice
  Loop2.subAll_pos Loop2.readsViol_covered Loop2.mem_listMayW Loop2.GuardIn.assign Loop2.GuardIn.list Loop2.GuardIn.block
  Loop2.GuardIn.admits Loop2.set_set Loop2.set_self Loop2.width_vrows
  Loop2.width_insertAt Loop2.width_resizeU LVec.insertAt_zero_of_width_eq Loop2.SingleComb.combIndices
  Loop2.SingleComb.edgeIndices Loop2.SingleComb.resetIndices Loop2.SingleComb.pass
  Loop2.SingleComb.settle Loop2.SingleComb.cycle Loop2.SingleComb.snapshot
  Loop2.SingleComb.terminates Loop2.SingleComb.runs Loop2.mem_drvWinsList Loop2.WritesOnly.block
  Loop2.driversOk_single Loop2.forValuesFuel2_upto Loop2.forFuel2_upto Loop2.forValues2_upto

end LeanModels.Sv
