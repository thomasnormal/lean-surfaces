/-
Proof module for `Examples/python/bench_bisect/spec.lean` (three-file example
layout). Every theorem stated in spec.lean is proved here under the same
name; the spec side is `:= by proofs`, which resolves
`Examples.python.bench_bisect.proof.<decl>` (Surface.lean).

PROVENANCE OF THE PROOFS (benchmark cold-prover runs, 2026-07-30): the
`bisect_left` development (namespace `BL`) and the `bisect_right`
development (namespace `BR`) were produced by two INDEPENDENT cold prover
agents working from the repo docs alone (docs/benchmark.md "Cold-prover
runs"), then adapted to the house layout. Adaptation deltas are recorded
in docs/benchmark.md; statements were only strengthened, never weakened.

Both loops defeat the `py_vcgen`/`py_loop` v1 recipe for the same reason:
the body CREATES `mid` on its first iteration (`Env.set` appends a new
slot), so the loop environment before iteration 1 has a different shape
than after — the two developments model this with an `Option Int` slot
(BL) and a `grown : Bool` flag (BR) in a hand-instantiated
`execWhile_total_of_invariant`, spliced back into `callFunction` with
`execWhile_at_least` + threshold rewriting. See the goal-shape table in
AGENTS.md (growing-environment row).
-/
import LeanModels

namespace Examples.python.bench_bisect.proof

open LeanModels LeanModels.Python

load_program bench_bisect from "Examples/python/bench_bisect/bench_bisect.json"

/-- The pinned world of the stage-1 geometry (`initWorld` unfolded — what
`py_simp` presents at every state; docs/memory-model.md). -/
def pw : World := ⟨#[], [], []⟩

/-! # Part 1 — `bisect_left` (cold prover 0, adapted) -/

namespace BL

/-! ## Logical loop state

`(lo, hi, om)`: the two live loop variables plus the `mid` slot, which is
absent from the environment before the first iteration (`Env.set` appends
it at the tail on first assignment). -/

abbrev SB := Int × Int × Option Int

def midEnv : Option Int → Env
  | Option.none => []
  | some mv => [("mid", RVal.int mv)]

def toEnvB (xs : List Int) (x : Int) : SB → Env
  | (lo, hi, om) =>
    ("a", RVal.listV ((List.map (RVal.thaw ∘ ToVal.toVal) xs).toArray)) ::
      ("x", RVal.int x) :: ("lo", RVal.int lo) ::
      ("hi", RVal.int hi) :: midEnv om

def ContB : SB → Bool
  | (lo, hi, _) => decide (lo < hi)

def tvB (s : SB) : RVal := .bool (ContB s)

def stepB (xs : List Int) (x : Int) : SB → SB
  | (lo, hi, _) =>
    let mid := Int.fdiv (lo + hi) 2
    if xs.getD mid.toNat 0 < x then (mid + 1, hi, some mid)
    else (lo, mid, some mid)

def μB : SB → Nat
  | (lo, hi, _) => (hi - lo).toNat

/-- The loop invariant, over the mathematical values of `lo`/`hi`:
window in range, everything left of `lo` is `< x`, everything from `hi`
on is `≥ x`. -/
def MIB (xs : List Int) (x : Int) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ xs.length ∧
  (∀ j : Nat, (j : Int) < lo → xs.getD j 0 < x) ∧
  (∀ j : Nat, hi ≤ (j : Int) → j < xs.length → x ≤ xs.getD j 0)

def InvB (xs : List Int) (x : Int) : SB → Prop
  | (lo, hi, _) => MIB xs x lo hi

/-! ## Pure list lemmas -/

/-- Sorted (`Pairwise (· ≤ ·)`) lists are monotone under `getD`-indexing. -/
theorem sorted_getD {xs : List Int} (hs : List.Pairwise (· ≤ ·) xs)
    {i j : Nat} (hij : i ≤ j) (hj : j < xs.length) :
    xs.getD i 0 ≤ xs.getD j 0 := by
  have hi : i < xs.length := Nat.lt_of_le_of_lt (Nat.le_refl i) (Nat.lt_of_le_of_lt hij hj)
  rcases Nat.lt_or_eq_of_le hij with h | h
  · have := (List.pairwise_iff_getElem.mp hs) i j hi hj h
    rw [← List.getElem_eq_getD (fallback := 0), ← List.getElem_eq_getD (fallback := 0)]
    exact this
  · subst h; exact Int.le_refl _

/-- Characterization of the strict-lower-prefix length: if everything below
`k` is `< x` and position `k` (when it exists) is not, then the `takeWhile`
prefix has length exactly `k`. -/
theorem takeWhile_length_eq {x : Int} :
    ∀ (xs : List Int) (k : Nat), k ≤ xs.length →
      (∀ j : Nat, j < k → xs.getD j 0 < x) →
      (k < xs.length → ¬ xs.getD k 0 < x) →
      (xs.takeWhile (fun v => decide (v < x))).length = k := by
  intro xs
  induction xs with
  | nil =>
    intro k hk _ _
    simp only [List.length_nil] at hk
    simp only [List.takeWhile_nil, List.length_nil]
    omega
  | cons a as ih =>
    intro k hk hlt hge
    cases k with
    | zero =>
      have ha : ¬ a < x := by simpa using hge (by simp)
      simp [ha]
    | succ k' =>
      have ha : a < x := by simpa using hlt 0 (Nat.succ_pos _)
      have hk' : k' ≤ as.length := by simp only [List.length_cons] at hk; omega
      have hrec : (as.takeWhile (fun v => decide (v < x))).length = k' := by
        refine ih k' hk' (fun j hj => by simpa using hlt (j + 1) (by omega)) ?_
        intro hklen hcontra
        have h1 := hge (by simp only [List.length_cons]; omega)
        exact h1 (by simpa using hcontra)
      simp [ha, hrec]

/-- The weak-prefix variant (`≤` instead of `<`) — the `bisect_right`
characterization. Same induction, relation swapped. -/
theorem takeWhile_le_length_eq {x : Int} :
    ∀ (xs : List Int) (k : Nat), k ≤ xs.length →
      (∀ j : Nat, j < k → xs.getD j 0 ≤ x) →
      (k < xs.length → ¬ xs.getD k 0 ≤ x) →
      (xs.takeWhile (fun v => decide (v ≤ x))).length = k := by
  intro xs
  induction xs with
  | nil =>
    intro k hk _ _
    simp only [List.length_nil] at hk
    simp only [List.takeWhile_nil, List.length_nil]
    omega
  | cons a as ih =>
    intro k hk hle hgt
    cases k with
    | zero =>
      have ha : ¬ a ≤ x := by simpa using hgt (by simp)
      simp [ha]
    | succ k' =>
      have ha : a ≤ x := by simpa using hle 0 (Nat.succ_pos _)
      have hk' : k' ≤ as.length := by simp only [List.length_cons] at hk; omega
      have hrec : (as.takeWhile (fun v => decide (v ≤ x))).length = k' := by
        refine ih k' hk' (fun j hj => by simpa using hle (j + 1) (by omega)) ?_
        intro hklen hcontra
        have h1 := hgt (by simp only [List.length_cons]; omega)
        exact h1 (by simpa using hcontra)
      simp [ha, hrec]

/-- `Array.getD` on the thawed marshalled list, at an in-range index. -/
theorem arr_getD (xs : List Int) (n : Nat) (h : n < xs.length) :
    (List.map (RVal.thaw ∘ ToVal.toVal (α := Int)) xs).toArray.getD n RVal.none
      = RVal.int (xs.getD n 0) := by
  have hbound : n < (List.map (RVal.thaw ∘ ToVal.toVal (α := Int)) xs).toArray.size := by
    simpa using h
  rw [Array.getD, dif_pos hbound]
  show ((List.map (RVal.thaw ∘ ToVal.toVal (α := Int)) xs).toArray)[n]'hbound
      = RVal.int (xs.getD n 0)
  rw [List.getElem_toArray, List.getElem_map]
  show RVal.thaw (ToVal.toVal xs[n]) = _
  rw [thaw_toVal_int, List.getElem_eq_getD (fallback := (0 : Int))]

/-! ## The loop's AST (transcribed from the loaded envelope; the `#guard`
below checks the transcription against the loaded module by kernel
reduction). -/

def blTest : Expr :=
  (Expr.name "lo" ⟨68, 10, 68, 12⟩).compare #[CmpOp.lt]
    #[Expr.name "hi" ⟨68, 15, 68, 17⟩] ⟨68, 10, 68, 17⟩

def blBody : List Stmt :=
  [Stmt.assign #[Expr.name "mid" ⟨69, 8, 69, 11⟩]
      (((Expr.name "lo" ⟨69, 15, 69, 17⟩).binOp BinOp.add
          (Expr.name "hi" ⟨69, 18, 69, 20⟩) ⟨69, 15, 69, 20⟩).binOp
        BinOp.floorDiv (Expr.constant (Const.int 2) ⟨69, 23, 69, 24⟩)
        ⟨69, 14, 69, 24⟩)
      ⟨69, 8, 69, 24⟩,
    Stmt.ifStmt
      (((Expr.name "a" ⟨71, 11, 71, 12⟩).subscript
          (Expr.name "mid" ⟨71, 13, 71, 16⟩) ⟨71, 11, 71, 17⟩).compare
        #[CmpOp.lt] #[Expr.name "x" ⟨71, 20, 71, 21⟩] ⟨71, 11, 71, 21⟩)
      #[Stmt.assign #[Expr.name "lo" ⟨71, 23, 71, 25⟩]
          ((Expr.name "mid" ⟨71, 28, 71, 31⟩).binOp BinOp.add
            (Expr.constant (Const.int 1) ⟨71, 32, 71, 33⟩) ⟨71, 28, 71, 33⟩)
          ⟨71, 23, 71, 33⟩]
      #[Stmt.assign #[Expr.name "hi" ⟨72, 14, 72, 16⟩]
          (Expr.name "mid" ⟨72, 19, 72, 22⟩) ⟨72, 14, 72, 22⟩]
      ⟨71, 8, 72, 22⟩]

/- Transcription check: statement 3 of the loaded `bisect_left` body IS
this while loop. -/
#guard ((findFunction bench_bisect "bisect_left").map (fun f => f.body[3]?)
    == some (some (Stmt.whileLoop blTest ⟨blBody⟩ #[] ⟨68, 4, 72, 22⟩)))

/-! ## The five obligations of `execWhile_total_of_invariant` -/

theorem htvB (xs : List Int) (x : Int) :
    ∀ s : SB, InvB xs x s → truthy (tvB s) = .ok (ContB s) :=
  fun _ _ => rfl

theorem htestB (xs : List Int) (x : Int) :
    ∀ s : SB, InvB xs x s →
      ∃ f₀, ∀ F, f₀ ≤ F →
        evalExpr bench_bisect F ⟨pw, toEnvB xs x s⟩ blTest
          = .ok ⟨pw, toEnvB xs x s⟩ (tvB s) := by
  rintro ⟨lo, hi, om⟩ -
  rcases om with _ | mv <;>
    py_threshold 8 [pw, blTest, toEnvB, midEnv, tvB, ContB, ite_ok_bool]

-- H1-proper: the heap-aware helper layers (indexValH/truthyH) deepen the
-- symbolic terms; the body execution needs a larger heartbeat budget.
set_option maxHeartbeats 800000 in
theorem hbodyB (xs : List Int) (x : Int) :
    ∀ s : SB, InvB xs x s → ContB s = true →
      ∃ f₀, ∀ F, f₀ ≤ F →
        execStmts bench_bisect F ⟨pw, toEnvB xs x s⟩ blBody
          = .ok ⟨pw, toEnvB xs x (stepB xs x s)⟩ .next := by
  rintro ⟨lo, hi, om⟩ hInv hc
  obtain ⟨h0, hlh, hhl, hlow, hhigh⟩ : MIB xs x lo hi := hInv
  have hlt : lo < hi := by simpa [ContB] using hc
  have hfd : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  have hm0 : 0 ≤ Int.fdiv (lo + hi) 2 := by omega
  have hmlt : Int.fdiv (lo + hi) 2 < (xs.length : Int) := by omega
  have hnn : ¬ Int.fdiv (lo + hi) 2 < 0 := by omega
  have hmn : (Int.fdiv (lo + hi) 2).toNat < xs.length := by omega
  have hgd := arr_getD xs (Int.fdiv (lo + hi) 2).toNat hmn
  by_cases hbr : xs.getD (Int.fdiv (lo + hi) 2).toNat 0 < x <;>
    rcases om with _ | mv <;>
      py_threshold 32 [pw, blBody, toEnvB, midEnv, stepB, hgd, hm0, hmlt, hnn, hbr] <;>
      (try py_simp []) <;> (try exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩)

theorem hinvB (xs : List Int) (x : Int) (hs : List.Pairwise (· ≤ ·) xs) :
    ∀ s : SB, InvB xs x s → ContB s = true → InvB xs x (stepB xs x s) := by
  rintro ⟨lo, hi, om⟩ hInv hc
  obtain ⟨h0, hlh, hhl, hlow, hhigh⟩ : MIB xs x lo hi := hInv
  have hlt : lo < hi := by simpa [ContB] using hc
  have hfd : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  have hm0 : 0 ≤ Int.fdiv (lo + hi) 2 := by omega
  have hmlt : Int.fdiv (lo + hi) 2 < (xs.length : Int) := by omega
  have hmn : (Int.fdiv (lo + hi) 2).toNat < xs.length := by omega
  by_cases hbr : xs.getD (Int.fdiv (lo + hi) 2).toNat 0 < x
  · simp only [stepB, if_pos hbr, InvB, MIB]
    refine ⟨by omega, by omega, hhl, ?_, hhigh⟩
    intro j hj
    by_cases hjlo : (j : Int) < lo
    · exact hlow j hjlo
    · have hjm : j ≤ (Int.fdiv (lo + hi) 2).toNat := by omega
      have := sorted_getD hs hjm hmn
      omega
  · have hxle : x ≤ xs.getD (Int.fdiv (lo + hi) 2).toNat 0 := Int.not_lt.mp hbr
    simp only [stepB, if_neg hbr, InvB, MIB]
    refine ⟨h0, by omega, by omega, hlow, ?_⟩
    intro j hj hjlen
    have hjm : (Int.fdiv (lo + hi) 2).toNat ≤ j := by omega
    have := sorted_getD hs hjm hjlen
    omega

theorem hdecB (xs : List Int) (x : Int) :
    ∀ s : SB, InvB xs x s → ContB s = true → μB (stepB xs x s) < μB s := by
  rintro ⟨lo, hi, om⟩ hInv hc
  obtain ⟨h0, hlh, hhl, -, -⟩ : MIB xs x lo hi := hInv
  have hlt : lo < hi := by simpa [ContB] using hc
  have hfd : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  by_cases hbr : xs.getD (Int.fdiv (lo + hi) 2).toNat 0 < x
  · simp only [stepB, μB, if_pos hbr]; omega
  · simp only [stepB, μB, if_neg hbr]; omega

theorem hinitB (xs : List Int) (x : Int) :
    InvB xs x ((0 : Int), (xs.length : Int), (Option.none : Option Int)) := by
  simp only [InvB, MIB]
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro j hj; exact absurd hj (by omega)
  · intro j h1 h2; exact absurd h2 (by omega)

/-! ## The relational core: one run of the whole function, with the
post-loop invariant facts attached to the returned index. -/

theorem bisect_left_core (xs : List Int) (x : Int)
    (hs : List.Pairwise (· ≤ ·) xs) :
    ∃ i : Int,
      CallsTo bench_bisect "bisect_left" #[ToVal.toVal xs, ToVal.toVal x]
        (Val.int i) ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) ∧
      (∀ j : Nat, (j : Int) < i → xs.getD j 0 < x) ∧
      (∀ j : Nat, i ≤ (j : Int) → j < xs.length → x ≤ xs.getD j 0) := by
  obtain ⟨⟨lo', hi', om'⟩, hInv', hcont', hex⟩ :=
    execWhile_total_of_invariant bench_bisect blTest blBody pw (toEnvB xs x)
      (InvB xs x) ContB (stepB xs x) μB tvB (htestB xs x) (htvB xs x)
      (hbodyB xs x) (hinvB xs x hs) (hdecB xs x)
      ((0 : Int), (xs.length : Int), (Option.none : Option Int)) (hinitB xs x)
  obtain ⟨h0', hlh', hhl', hlow', hhigh'⟩ : MIB xs x lo' hi' := hInv'
  have hcont'' : ¬ lo' < hi' := by simpa [ContB] using hcont'
  refine ⟨lo', ?_, h0', by omega, hlow',
    fun j hj hjl => hhigh' j (by omega) hjl⟩
  obtain ⟨f₀, hloopT⟩ := execWhile_at_least hex
  rcases om' with _ | mv <;>
    (simp only [pw, bench_bisect, blTest, blBody, toEnvB, midEnv] at hloopT
     refine ⟨f₀ + 64, ?_⟩
     py_simp [callFunction, callIn, bench_bisect]
     simp (disch := omega) only [hloopT]
     py_simp []
     all_goals omega)

/-! ## Bounds-only variant (no sortedness): termination on ANY list -/

def MIT (xs : List Int) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ xs.length

def InvT (xs : List Int) : SB → Prop
  | (lo, hi, _) => MIT xs lo hi

theorem htvT (xs : List Int) :
    ∀ s : SB, InvT xs s → truthy (tvB s) = .ok (ContB s) :=
  fun _ _ => rfl

theorem htestT (xs : List Int) (x : Int) :
    ∀ s : SB, InvT xs s →
      ∃ f₀, ∀ F, f₀ ≤ F →
        evalExpr bench_bisect F ⟨pw, toEnvB xs x s⟩ blTest
          = .ok ⟨pw, toEnvB xs x s⟩ (tvB s) := by
  rintro ⟨lo, hi, om⟩ -
  rcases om with _ | mv <;>
    py_threshold 8 [pw, blTest, toEnvB, midEnv, tvB, ContB, ite_ok_bool]

theorem hbodyT (xs : List Int) (x : Int) :
    ∀ s : SB, InvT xs s → ContB s = true →
      ∃ f₀, ∀ F, f₀ ≤ F →
        execStmts bench_bisect F ⟨pw, toEnvB xs x s⟩ blBody
          = .ok ⟨pw, toEnvB xs x (stepB xs x s)⟩ .next := by
  rintro ⟨lo, hi, om⟩ hInv hc
  obtain ⟨h0, hlh, hhl⟩ : MIT xs lo hi := hInv
  have hlt : lo < hi := by simpa [ContB] using hc
  have hfd : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  have hm0 : 0 ≤ Int.fdiv (lo + hi) 2 := by omega
  have hmlt : Int.fdiv (lo + hi) 2 < (xs.length : Int) := by omega
  have hnn : ¬ Int.fdiv (lo + hi) 2 < 0 := by omega
  have hmn : (Int.fdiv (lo + hi) 2).toNat < xs.length := by omega
  have hgd := arr_getD xs (Int.fdiv (lo + hi) 2).toNat hmn
  by_cases hbr : xs.getD (Int.fdiv (lo + hi) 2).toNat 0 < x <;>
    rcases om with _ | mv <;>
      py_threshold 32 [pw, blBody, toEnvB, midEnv, stepB, hgd, hm0, hmlt, hnn, hbr] <;>
      (try py_simp []) <;> (try exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩)

theorem hinvT (xs : List Int) (x : Int) :
    ∀ s : SB, InvT xs s → ContB s = true → InvT xs (stepB xs x s) := by
  rintro ⟨lo, hi, om⟩ hInv hc
  obtain ⟨h0, hlh, hhl⟩ : MIT xs lo hi := hInv
  have hlt : lo < hi := by simpa [ContB] using hc
  have hfd : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  by_cases hbr : xs.getD (Int.fdiv (lo + hi) 2).toNat 0 < x
  · simp only [stepB, if_pos hbr, InvT, MIT]
    refine ⟨by omega, by omega, hhl⟩
  · simp only [stepB, if_neg hbr, InvT, MIT]
    refine ⟨h0, by omega, by omega⟩

theorem hdecT (xs : List Int) (x : Int) :
    ∀ s : SB, InvT xs s → ContB s = true → μB (stepB xs x s) < μB s := by
  rintro ⟨lo, hi, om⟩ hInv hc
  obtain ⟨h0, hlh, hhl⟩ : MIT xs lo hi := hInv
  have hlt : lo < hi := by simpa [ContB] using hc
  have hfd : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  by_cases hbr : xs.getD (Int.fdiv (lo + hi) 2).toNat 0 < x
  · simp only [stepB, μB, if_pos hbr]; omega
  · simp only [stepB, μB, if_neg hbr]; omega

theorem hinitT (xs : List Int) :
    InvT xs ((0 : Int), (xs.length : Int), (Option.none : Option Int)) := by
  simp only [InvT, MIT]
  refine ⟨by omega, by omega, by omega⟩

end BL

/-! ## `bisect_left` — the four public theorems -/

open BL in
/-- **Unconditional termination.** On EVERY list — sorted or not —
`bisect_left(xs, x)` terminates and returns an index in `[0, len(xs)]`.
No hypothesis on `xs` at all. -/
theorem bisect_left_terminates (xs : List PyInt) (x : PyInt) :
    ∃ i : PyInt, bench_bisect.bisect_left(xs, x) ==> i ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) := by
  obtain ⟨⟨lo', hi', om'⟩, hInv', hcont', hex⟩ :=
    execWhile_total_of_invariant bench_bisect blTest blBody pw (toEnvB xs x)
      (InvT xs) ContB (stepB xs x) μB tvB (htestT xs x) (htvT xs)
      (hbodyT xs x) (hinvT xs x) (hdecT xs x)
      ((0 : Int), (xs.length : Int), (Option.none : Option Int)) (hinitT xs)
  obtain ⟨h0', hlh', hhl'⟩ : MIT xs lo' hi' := hInv'
  refine ⟨lo', ?_, h0', Int.le_trans hlh' hhl'⟩
  obtain ⟨f₀, hloopT⟩ := execWhile_at_least hex
  rcases om' with _ | mv <;>
    (simp only [pw, bench_bisect, blTest, blBody, toEnvB, midEnv] at hloopT
     refine ⟨f₀ + 64, ?_⟩
     py_simp [callFunction, callIn, bench_bisect]
     simp (disch := omega) only [hloopT]
     py_simp []
     all_goals omega)

open BL in
/-- **Main theorem.** For every sorted list `xs` and every `x`, the real
CPython `bisect_left(xs, x)` — run through the deep-embedded interpreter,
with `lo`/`hi` taking their defaults — terminates and returns the length
of the strict-lower prefix of `xs`: the leftmost insertion point for `x`. -/
theorem bisect_left_sorted (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_left(xs, x) ==>
      (xs.takeWhile (fun v => decide (v < x))).length := by
  obtain ⟨i, hc, h0, hle, hlow, hhigh⟩ := bisect_left_core xs x hs
  have hN : (xs.takeWhile (fun v => decide (v < x))).length = i.toNat :=
    takeWhile_length_eq xs i.toNat (by omega)
      (fun j hj => hlow j (by omega))
      (fun hklen => by have := hhigh i.toNat (by omega) hklen; omega)
  have hv : (ToVal.toVal ((xs.takeWhile (fun v => decide (v < x))).length) : Val)
      = Val.int i := by
    rw [toVal_nat]; congr 1; omega
  rw [show (ToVal.toVal ((xs.takeWhile (fun v => decide (v < x))).length) : Val)
      = Val.int i from hv]
  exact hc

open BL in
/-- **Docstring characterization** (the contract stated in `bisect_left`'s
own docstring): on sorted input, the returned index `i` is in range, all of
`a[:i]` is `< x`, and all of `a[i:]` is `≥ x`. Stated relationally against
any observed run (`⇓`). -/
theorem bisect_left_insertion_point (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) {i : PyInt}
    (h : bench_bisect.bisect_left(xs, x) ⇓ i) :
    0 ≤ i ∧ i ≤ (xs.length : Int) ∧
    (∀ j : Nat, (j : Int) < i → xs.getD j 0 < x) ∧
    (∀ j : Nat, i ≤ (j : Int) → j < xs.length → x ≤ xs.getD j 0) := by
  obtain ⟨i₀, hc, h0, hle, hlow, hhigh⟩ := bisect_left_core xs x hs
  have heq : (ToVal.toVal i : Val) = Val.int i₀ :=
    CallsTo.eq_of_partialTo h hc.partialTo
  have hii : i = i₀ := by simpa using heq
  subst hii
  exact ⟨h0, hle, hlow, hhigh⟩

/-- **Strengthened partial correctness** (`~~>`): every run of
`bisect_left(xs, x)` on sorted `xs`, at every fuel, either times out or
returns exactly the insertion point — no exception, no `unsupported`, no
other value. Free from totality via fuel determinism. -/
theorem bisect_left_partial (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_left(xs, x) ~~>
      (xs.takeWhile (fun v => decide (v < x))).length :=
  (bisect_left_sorted xs x hs).partialTo

/-! # Part 2 — `bisect_right` (cold prover 1, adapted; the ∃-form core is
the prover's verbatim claim, the deterministic `takeWhile` forms are the
adaptation-time strengthening recorded in docs/benchmark.md) -/

theorem getD_eq_getElem (a : List Int) (n : Nat) (h : n < a.length) : a.getD n 0 = a[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem arrVal_getElem (a : List Int) (n : Nat) (h : n < a.length) :
    (Option.map (RVal.thaw ∘ ToVal.toVal) a[n]?).getD RVal.none
      = RVal.int (a.getD n 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem a n h]
  rfl

namespace BR

variable (a : List Int) (x : Int)

/-- Loop state: `(lo, hi, storedMid, grown)` — `grown` records whether the
body has run at least once, i.e. whether the interpreter environment
already carries a `"mid"` slot (appended by `Env.set` the first time
`mid = …` executes, then overwritten in place on every subsequent
iteration); `storedMid` mirrors whatever value that slot currently holds
(the last `mid` computed) so `toEnv` matches the interpreter's environment
*exactly*, even though `mid`'s stored value never affects the program's
behaviour (it is always overwritten before being read again). The entry
environment (`py_begin`'s `env0`) has no `"mid"` key, so `toEnv` must
special-case it. -/
abbrev State := Int × Int × Int × Bool

def Inv (p : State) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ (a.length : Int) ∧
  (∀ j : Int, 0 ≤ j → j < p.1 → a.getD j.toNat 0 ≤ x) ∧
  (∀ j : Int, p.2.1 ≤ j → j < (a.length : Int) → x < a.getD j.toNat 0)

/-- Bounds-only invariant (no sortedness) — enough for termination. -/
def InvT (p : State) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ (a.length : Int)

def toEnv (p : State) : Env :=
  if p.2.2.2 then
    [("a", RVal.listV (List.map (RVal.thaw ∘ ToVal.toVal) a).toArray),
     ("x", RVal.int x),
     ("lo", RVal.int p.1), ("hi", RVal.int p.2.1), ("mid", RVal.int p.2.2.1)]
  else
    [("a", RVal.listV (List.map (RVal.thaw ∘ ToVal.toVal) a).toArray),
     ("x", RVal.int x),
     ("lo", RVal.int p.1), ("hi", RVal.int p.2.1)]

def Cont (p : State) : Bool := decide (p.1 < p.2.1)

def mid (p : State) : Int := (p.1 + p.2.1) / 2

def step (p : State) : State :=
  if x < a.getD (mid p).toNat 0 then (p.1, mid p, mid p, true) else (mid p + 1, p.2.1, mid p, true)

def mu (p : State) : Nat := (p.2.1 - p.1).toNat

def tv (p : State) : RVal := RVal.bool (decide (p.1 < p.2.1))

end BR

/-- The concrete `while` statement inside `bisect_right`, pulled out of the
loaded module by pattern-matching instead of hand transcription. -/
def BR.whileStmt : Stmt := (bench_bisect.functions[0]!).body[3]!

@[reducible] def BR.testE : Expr :=
  match BR.whileStmt with
  | .whileLoop t _ _ _ => t
  | _ => Expr.constant .none ⟨0,0,0,0⟩

@[reducible] def BR.bodyE : List Stmt :=
  match BR.whileStmt with
  | .whileLoop _ b _ _ => b.toList
  | _ => []

/-- Specialization of the generic while rule to `bisect_right`'s loop state. -/
theorem BR.loop_lemma (a : List Int) (x : Int) (test : Expr) (body : List Stmt)
    (htest : ∀ p, BR.Inv a x p → ∃ f0, ∀ F, f0 ≤ F →
      evalExpr bench_bisect F ⟨pw, BR.toEnv a x p⟩ test
        = .ok ⟨pw, BR.toEnv a x p⟩ (BR.tv p))
    (htv : ∀ p, BR.Inv a x p → truthy (BR.tv p) = .ok (BR.Cont p))
    (hbody : ∀ p, BR.Inv a x p → BR.Cont p = true → ∃ f0, ∀ F, f0 ≤ F →
      execStmts bench_bisect F ⟨pw, BR.toEnv a x p⟩ body
        = .ok ⟨pw, BR.toEnv a x (BR.step a x p)⟩ .next)
    (hinv : ∀ p, BR.Inv a x p → BR.Cont p = true → BR.Inv a x (BR.step a x p))
    (hdec : ∀ p, BR.Inv a x p → BR.Cont p = true → BR.mu (BR.step a x p) < BR.mu p) :
    ∀ p, BR.Inv a x p → ∃ p', BR.Inv a x p' ∧ BR.Cont p' = false ∧
      ∃ F, execWhile bench_bisect F ⟨pw, BR.toEnv a x p⟩ test body []
        = .ok ⟨pw, BR.toEnv a x p'⟩ .next :=
  execWhile_total_of_invariant bench_bisect test body pw (BR.toEnv a x) (BR.Inv a x) BR.Cont
    (BR.step a x) BR.mu BR.tv htest htv hbody hinv hdec

theorem BR.htv_pf (a : List Int) (x : Int) :
    ∀ p, BR.Inv a x p → truthy (BR.tv p) = .ok (BR.Cont p) := by
  intro p _; simp [BR.tv, BR.Cont, truthy]

set_option linter.unusedSimpArgs false in
theorem BR.htest_pf (a : List Int) (x : Int) :
    ∀ p, BR.Inv a x p → ∃ f0, ∀ F, f0 ≤ F →
      evalExpr bench_bisect F ⟨pw, BR.toEnv a x p⟩ BR.testE
        = .ok ⟨pw, BR.toEnv a x p⟩ (BR.tv p) := by
  intro p _
  unfold BR.testE BR.whileStmt
  refine ⟨32, ?_⟩
  intro F hF
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  unfold BR.toEnv BR.tv
  by_cases hgrown : p.2.2.2 <;> simp only [hgrown, if_true, if_false] <;>
    py_simp [pw, bench_bisect, ite_ok_bool]

theorem BR.hdec_pf (a : List Int) (x : Int) :
    ∀ p, BR.Inv a x p → BR.Cont p = true → BR.mu (BR.step a x p) < BR.mu p := by
  rintro ⟨lo, hi, _mid, grown⟩ hinv hcont
  try dsimp only at hinv hcont ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  simp only [BR.Cont, decide_eq_true_eq] at hcont
  have hfd := Int.fmod_add_mul_fdiv (lo + hi) 2
  have hfnn := Int.fmod_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hdnn := Int.fdiv_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  unfold BR.mu BR.step BR.mid
  by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0 <;> simp only [hlt, if_true, if_false] <;>
    omega

theorem BR.hinit_pf (a : List Int) (x : Int) : BR.Inv a x (0, (a.length : Int), 0, false) := by
  unfold BR.Inv; dsimp only
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro j hj0 hjlt; omega
  · intro j hj0 hjlt; omega

theorem BR.hinv_pf (a : List Int) (x : Int) (hsorted : a.Pairwise (· ≤ ·)) :
    ∀ p, BR.Inv a x p → BR.Cont p = true → BR.Inv a x (BR.step a x p) := by
  rintro ⟨lo, hi, _mid, grown⟩ hinv hcont
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  dsimp only at h1 h2 h3 h4 h5 ⊢
  simp only [BR.Cont, decide_eq_true_eq] at hcont
  have hfd := Int.fmod_add_mul_fdiv (lo + hi) 2
  have hfnn := Int.fmod_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hdnn := Int.fdiv_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hmidlb : lo ≤ (lo + hi) / 2 := by omega
  have hmidub : (lo + hi) / 2 < hi := by omega
  have hmid0 : (0:Int) ≤ (lo + hi) / 2 := by omega
  have hmidN : (lo + hi) / 2 < (a.length : Int) := by omega
  -- pairwise sortedness as an index-comparison fact
  have hsortedIdx : ∀ i j : Nat, i ≤ j → j < a.length → a.getD i 0 ≤ a.getD j 0 := by
    intro i j hij hjlt
    rcases (show i = j ∨ i < j from by omega) with heq | hlt2
    · subst heq; omega
    · have hilt : i < a.length := by omega
      have hij2 := List.pairwise_iff_getElem.mp hsorted i j hilt hjlt hlt2
      have hgi := getD_eq_getElem a i hilt
      have hgj := getD_eq_getElem a j hjlt
      omega
  simp only [BR.step, BR.mid]
  unfold BR.Inv
  by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0
  · simp only [hlt, if_true]
    refine ⟨h1, by omega, by omega, ?_, ?_⟩
    · intro j hj0 hjlt; exact h4 j hj0 (by omega)
    · intro j hj0 hjlt
      rcases (show (0:Int) = j ∨ 0 < j from by omega) with heq | hgt
      · rw [show (lo + hi) / 2 = j from by omega] at hlt; simpa using hlt
      · have hmidj : ((lo + hi) / 2).toNat ≤ j.toNat := by omega
        have hjltN : j.toNat < a.length := by omega
        have hsi := hsortedIdx ((lo + hi) / 2).toNat j.toNat hmidj hjltN
        have hcast : ((((lo + hi) / 2).toNat : Int)) = (lo + hi) / 2 := by omega
        have hcast2 : ((j.toNat : Int)) = j := by omega
        omega
  · simp only [hlt, if_false]
    replace hlt : a.getD ((lo + hi) / 2).toNat 0 ≤ x := by omega
    refine ⟨by omega, by omega, h3, ?_, ?_⟩
    · intro j hj0 hjlt
      rcases (show j = (lo + hi) / 2 ∨ j < (lo + hi) / 2 from by omega) with heq | hlt2
      · rw [show j = (lo + hi) / 2 from heq]; simpa using hlt
      · have hjmid : j.toNat ≤ ((lo + hi) / 2).toNat := by omega
        have hmidltN : ((lo + hi) / 2).toNat < a.length := by omega
        have hsi := hsortedIdx j.toNat ((lo + hi) / 2).toNat hjmid hmidltN
        have hcast : ((((lo + hi) / 2).toNat : Int)) = (lo + hi) / 2 := by omega
        have hcast2 : ((j.toNat : Int)) = j := by omega
        omega
    · intro j hj0 hjlt; exact h5 j (by omega) hjlt

set_option linter.unusedSimpArgs false in
theorem BR.hbody_pf (a : List Int) (x : Int) :
    ∀ p : BR.State, BR.Inv a x p → BR.Cont p = true → ∃ f0, ∀ F, f0 ≤ F →
      execStmts bench_bisect F ⟨pw, BR.toEnv a x p⟩ BR.bodyE
        = .ok ⟨pw, BR.toEnv a x (BR.step a x p)⟩ .next := by
  rintro ⟨lo, hi, _mid, grown⟩ hinv hcont
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  dsimp only at h1 h2 h3 h4 h5 ⊢
  simp only [BR.Cont, decide_eq_true_eq] at hcont
  have hfd := Int.fmod_add_mul_fdiv (lo + hi) 2
  have hfnn := Int.fmod_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hdnn := Int.fdiv_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hmid0 : (0:Int) ≤ (lo + hi) / 2 := by omega
  have hmidN : (lo + hi) / 2 < (a.length : Int) := by omega
  have hmidNat : ((lo + hi) / 2).toNat < a.length := by omega
  have harr := arrVal_getElem a ((lo + hi) / 2).toNat hmidNat
  have hmidToNat : (((lo + hi) / 2).toNat : Int) = (lo + hi) / 2 := by omega
  have hnn : ¬ (lo + hi) / 2 < 0 := by omega
  have hfe : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 := Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  unfold BR.bodyE BR.whileStmt BR.toEnv BR.step BR.mid
  cases grown
  · by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0
    · have hltE : x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]
    · have hltE : ¬ x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]
  · by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0
    · have hltE : x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]
    · have hltE : ¬ x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]

/-! ### Bounds-only obligations (termination without sortedness) -/

set_option linter.unusedSimpArgs false in
theorem BR.htestT_pf (a : List Int) (x : Int) :
    ∀ p, BR.InvT a p → ∃ f0, ∀ F, f0 ≤ F →
      evalExpr bench_bisect F ⟨pw, BR.toEnv a x p⟩ BR.testE
        = .ok ⟨pw, BR.toEnv a x p⟩ (BR.tv p) := by
  intro p _
  unfold BR.testE BR.whileStmt
  refine ⟨32, ?_⟩
  intro F hF
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  unfold BR.toEnv BR.tv
  by_cases hgrown : p.2.2.2 <;> simp only [hgrown, if_true, if_false] <;>
    py_simp [pw, bench_bisect, ite_ok_bool]

theorem BR.htvT_pf (a : List Int) :
    ∀ p, BR.InvT a p → truthy (BR.tv p) = .ok (BR.Cont p) := by
  intro p _; simp [BR.tv, BR.Cont, truthy]

set_option linter.unusedSimpArgs false in
theorem BR.hbodyT_pf (a : List Int) (x : Int) :
    ∀ p : BR.State, BR.InvT a p → BR.Cont p = true → ∃ f0, ∀ F, f0 ≤ F →
      execStmts bench_bisect F ⟨pw, BR.toEnv a x p⟩ BR.bodyE
        = .ok ⟨pw, BR.toEnv a x (BR.step a x p)⟩ .next := by
  rintro ⟨lo, hi, _mid, grown⟩ hinv hcont
  obtain ⟨h1, h2, h3⟩ := hinv
  dsimp only at h1 h2 h3 ⊢
  simp only [BR.Cont, decide_eq_true_eq] at hcont
  have hfd := Int.fmod_add_mul_fdiv (lo + hi) 2
  have hfnn := Int.fmod_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hdnn := Int.fdiv_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hmid0 : (0:Int) ≤ (lo + hi) / 2 := by omega
  have hmidN : (lo + hi) / 2 < (a.length : Int) := by omega
  have hmidNat : ((lo + hi) / 2).toNat < a.length := by omega
  have harr := arrVal_getElem a ((lo + hi) / 2).toNat hmidNat
  have hmidToNat : (((lo + hi) / 2).toNat : Int) = (lo + hi) / 2 := by omega
  have hnn : ¬ (lo + hi) / 2 < 0 := by omega
  have hfe : Int.fdiv (lo + hi) 2 = (lo + hi) / 2 := Int.fdiv_eq_ediv_of_nonneg (lo + hi) (by omega)
  unfold BR.bodyE BR.whileStmt BR.toEnv BR.step BR.mid
  cases grown
  · by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0
    · have hltE : x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]
    · have hltE : ¬ x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]
  · by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0
    · have hltE : x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]
    · have hltE : ¬ x < a[((lo + hi) / 2).toNat] := by
        rw [← getD_eq_getElem a _ hmidNat]; exact hlt
      refine ⟨64, ?_⟩
      intro F hF
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF
      rw [Nat.add_comm]
      simp only [hlt, if_true, if_false]
      py_simp [pw, bench_bisect, hfe, harr, hmidToNat, hmid0, hmidN, hnn, hltE,
        getD_eq_getElem a ((lo + hi) / 2).toNat hmidNat, List.getElem?_eq_getElem hmidNat]

theorem BR.hinvT_pf (a : List Int) (x : Int) :
    ∀ p, BR.InvT a p → BR.Cont p = true → BR.InvT a (BR.step a x p) := by
  rintro ⟨lo, hi, _mid, grown⟩ hinv hcont
  obtain ⟨h1, h2, h3⟩ := hinv
  dsimp only at h1 h2 h3 ⊢
  simp only [BR.Cont, decide_eq_true_eq] at hcont
  have hfd := Int.fmod_add_mul_fdiv (lo + hi) 2
  have hfnn := Int.fmod_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hdnn := Int.fdiv_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  simp only [BR.step, BR.mid]
  unfold BR.InvT
  by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0
  · simp only [hlt, if_true]
    exact ⟨h1, by omega, by omega⟩
  · simp only [hlt, if_false]
    exact ⟨by omega, by omega, h3⟩

theorem BR.hdecT_pf (a : List Int) (x : Int) :
    ∀ p, BR.InvT a p → BR.Cont p = true → BR.mu (BR.step a x p) < BR.mu p := by
  rintro ⟨lo, hi, _mid, grown⟩ hinv hcont
  try dsimp only at hinv hcont ⊢
  obtain ⟨h1, h2, h3⟩ := hinv
  simp only [BR.Cont, decide_eq_true_eq] at hcont
  have hfd := Int.fmod_add_mul_fdiv (lo + hi) 2
  have hfnn := Int.fmod_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  have hdnn := Int.fdiv_nonneg (show (0:Int) ≤ lo + hi by omega) (show (0:Int) ≤ 2 by omega)
  unfold BR.mu BR.step BR.mid
  by_cases hlt : x < a.getD ((lo + hi) / 2).toNat 0 <;> simp only [hlt, if_true, if_false] <;>
    omega

theorem BR.hinitT_pf (a : List Int) : BR.InvT a (0, (a.length : Int), 0, false) := by
  unfold BR.InvT; dsimp only
  exact ⟨by omega, by omega, by omega⟩

/-! ### The `bisect_right` cores -/

/-- The cold prover's verbatim total-correctness core, over unbranded
`Int` (the shape the surface theorems below consume — `omega` reads
`Int`-headed comparisons only). -/
private theorem bisect_right_core (a : List Int) (x : Int) (hsorted : a.Pairwise (· ≤ ·)) :
    ∃ i : Int, bench_bisect.bisect_right(a, x) ==> i ∧
      0 ≤ i ∧ i ≤ (a.length : Int) ∧
      (∀ j : Int, 0 ≤ j → j < i → a.getD j.toNat 0 ≤ x) ∧
      (∀ j : Int, i ≤ j → j < (a.length : Int) → x < a.getD j.toNat 0) := by
  have key := BR.loop_lemma a x BR.testE BR.bodyE
    (BR.htest_pf a x) (BR.htv_pf a x) (BR.hbody_pf a x) (BR.hinv_pf a x hsorted) (BR.hdec_pf a x)
    (0, (a.length:Int), 0, false) (BR.hinit_pf a x)
  obtain ⟨p', hInv', hCont', Fl, hex⟩ := key
  obtain ⟨h1, h2, h3, h4, h5⟩ := hInv'
  have heq : p'.1 = p'.2.1 := by
    simp only [BR.Cont, decide_eq_false_iff_not] at hCont'
    omega
  obtain ⟨fl, hthresh⟩ := execWhile_at_least ⟨Fl, hex⟩
  unfold pw BR.testE BR.bodyE BR.whileStmt BR.toEnv bench_bisect at hthresh
  simp at hthresh
  refine ⟨p'.1, ?_, by omega, by omega, fun j hj0 hjlt => h4 j hj0 hjlt, fun j hj0 hjlt => ?_⟩
  · py_begin [bench_bisect]
    refine CallsTo.intro (fl + 32) ?_
    rw [hentry]
    rw [hthresh (fl + 26) (by omega)]
    try unfold BR.toEnv
    rcases p' with ⟨lo', hi', _mid', grown'⟩
    cases grown' <;> py_simp
  · exact h5 j (by omega) hjlt

/-- Bounds-only core: termination and range on EVERY list. -/
private theorem bisect_right_terminates_core (a : List Int) (x : Int) :
    ∃ i : Int, bench_bisect.bisect_right(a, x) ==> i ∧
      0 ≤ i ∧ i ≤ (a.length : Int) := by
  have key := execWhile_total_of_invariant bench_bisect BR.testE BR.bodyE pw (BR.toEnv a x)
    (BR.InvT a) BR.Cont (BR.step a x) BR.mu BR.tv
    (BR.htestT_pf a x) (BR.htvT_pf a) (BR.hbodyT_pf a x) (BR.hinvT_pf a x) (BR.hdecT_pf a x)
    (0, (a.length:Int), 0, false) (BR.hinitT_pf a)
  obtain ⟨p', hInv', _hCont', Fl, hex⟩ := key
  obtain ⟨h1, h2, h3⟩ := hInv'
  obtain ⟨fl, hthresh⟩ := execWhile_at_least ⟨Fl, hex⟩
  unfold pw BR.testE BR.bodyE BR.whileStmt BR.toEnv bench_bisect at hthresh
  simp at hthresh
  refine ⟨p'.1, ?_, by omega, by omega⟩
  py_begin [bench_bisect]
  refine CallsTo.intro (fl + 32) ?_
  rw [hentry]
  rw [hthresh (fl + 26) (by omega)]
  try unfold BR.toEnv
  rcases p' with ⟨lo', hi', _mid', grown'⟩
  cases grown' <;> py_simp

/-! ## `bisect_right` — the five public theorems -/

/-- **Unconditional termination.** On EVERY list — sorted or not —
`bisect_right(xs, x)` terminates and returns an index in `[0, len(xs)]`. -/
theorem bisect_right_terminates (xs : List PyInt) (x : PyInt) :
    ∃ i : PyInt, bench_bisect.bisect_right(xs, x) ==> i ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) :=
  bisect_right_terminates_core xs x

/-- **Total correctness, relational form** (the cold prover's verbatim
claim): on sorted input the returned index `i` is in range, everything
before `i` is `≤ x`, everything from `i` on is `> x` — CPython's own
docstring contract for `bisect_right`. -/
theorem bisect_right_total (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    ∃ i : PyInt, bench_bisect.bisect_right(xs, x) ==> i ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) ∧
      (∀ j : Int, 0 ≤ j → j < i → xs.getD j.toNat 0 ≤ x) ∧
      (∀ j : Int, i ≤ j → j < (xs.length : Int) → x < xs.getD j.toNat 0) :=
  bisect_right_core xs x hs

open BL in
/-- **Main theorem (deterministic form).** For every sorted list `xs` and
every `x`, `bisect_right(xs, x)` with `lo`/`hi` defaulted terminates and
returns the length of the weak prefix `xs.takeWhile (· ≤ x)` — the
rightmost insertion point (the count of elements `≤ x`). -/
theorem bisect_right_sorted (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_right(xs, x) ==>
      (xs.takeWhile (fun v => decide (v ≤ x))).length := by
  obtain ⟨i, hc, h0, hle, hlow, hhigh⟩ := bisect_right_core xs x hs
  -- NOTE: consume `hlow`/`hhigh` directly — they are `Int`-headed (the core
  -- is stated over unbranded `Int`), so `omega` ingests them; a restatement
  -- here would re-elaborate at the `PyInt` brand and be skipped (AGENTS.md
  -- failure table, mode "omega ignores a PyInt-typed hypothesis").
  have hN : (xs.takeWhile (fun v => decide (v ≤ x))).length = i.toNat := by
    refine takeWhile_le_length_eq xs i.toNat (by omega) ?_ ?_
    · intro j hj
      have h := hlow (j : Int) (by omega) (by omega)
      have hjt : ((j : Int)).toNat = j := by omega
      rwa [hjt] at h
    · intro hklen
      have h := hhigh (i.toNat : Int) (by omega) (by omega)
      have hjt : ((i.toNat : Int)).toNat = i.toNat := by omega
      rw [hjt] at h
      omega
  have hv : (ToVal.toVal ((xs.takeWhile (fun v => decide (v ≤ x))).length) : Val)
      = Val.int i := by
    rw [toVal_nat]; congr 1; omega
  rw [show (ToVal.toVal ((xs.takeWhile (fun v => decide (v ≤ x))).length) : Val)
      = Val.int i from hv]
  simpa using hc

/-- **Docstring characterization** (`⇓`-relational): any observed result of
`bisect_right(xs, x)` on sorted input is in range, with all of `a[:i]`
`≤ x` and all of `a[i:]` `> x`. -/
theorem bisect_right_insertion_point (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) {i : PyInt}
    (h : bench_bisect.bisect_right(xs, x) ⇓ i) :
    0 ≤ i ∧ i ≤ (xs.length : Int) ∧
    (∀ j : Int, 0 ≤ j → j < i → xs.getD j.toNat 0 ≤ x) ∧
    (∀ j : Int, i ≤ j → j < (xs.length : Int) → x < xs.getD j.toNat 0) := by
  obtain ⟨i₀, hc, h0, hle, hlow, hhigh⟩ := bisect_right_core xs x hs
  have heq : (ToVal.toVal i : Val) = ToVal.toVal i₀ :=
    CallsTo.eq_of_partialTo h hc.partialTo
  have hii : i = i₀ := by simpa using heq
  subst hii
  exact ⟨h0, hle, hlow, hhigh⟩

/-- **Strengthened partial correctness** (`~~>`): every run either times
out or returns exactly the rightmost insertion point. -/
theorem bisect_right_partial (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_right(xs, x) ~~>
      (xs.takeWhile (fun v => decide (v ≤ x))).length :=
  (bisect_right_sorted xs x hs).partialTo

end Examples.python.bench_bisect.proof
