/-
Proof module for `Examples/python/bench_statistics/spec.lean` (three-file
example layout). Every theorem stated in spec.lean is proved here under the
same name; the spec side is `:= by proofs`, which resolves
`Examples.python.bench_statistics.proof.<decl>` (Surface.lean).

BENCHMARK FLAGSHIP (Band C, docs/benchmark.md rows 4-5): CPython's own
`statistics.median_low`/`median_high` — byte-verbatim 3.9.25 stdlib
source — proved totally correct through the deep-embedded interpreter,
the first proofs through the builtin `sorted` (the call:sorted tier
feature). The empty-input `raise StatisticsError` guard is the vendored
`Unsupported Raise` node, discharged by the `data ≠ []` hypothesis
(unreached-guard rule, rsa_inverse/bisect precedent).

Both bodies are STRAIGHT-LINE (no loops): the cores are one `py_simp`
symbolic execution each, with the branch facts (`n == 0` guard false,
`n % 2` parity split for `median_low`, index bounds for `normIndex`)
precomputed by `omega` and passed as rewrite rules.

Sort bridge: the interpreter's `sortInts` (structural insertion sort —
kernel-reducible on purpose; core's `List.mergeSort` is well-founded
recursion and does NOT kernel-reduce, which would break
`#py_check`/`py_check`) is bridged to Mathlib's `List.insertionSort`
(`sortInts_eq` below) to harvest `Pairwise`/`Perm`; only the Mathlib-free
`sortInts_length`/`asIntList_map_int` live in `LeanModels/Python`
(Logic.lean), because symbolic execution needs them.

Import note: `LeanModels.Python` (not bare `LeanModels` — the Python lane
must not build the other lanes) plus `Mathlib.Data.List.Sort` for the
insertion-sort lemmas. On this Mathlib pin the sortedness lemma is named
`List.pairwise_insertionSort` (`List.sorted_insertionSort` is gone).
-/
import LeanModels.Python
import Mathlib.Data.List.Sort

namespace Examples.python.bench_statistics.proof

open LeanModels LeanModels.Python

load_program bench_statistics from "Examples/python/bench_statistics/bench_statistics.json"

/-! ## `sortInts` ↔ Mathlib bridge -/

/-- `insertLe` is Mathlib's `orderedInsert` at `(· ≤ ·)`. -/
theorem insertLe_eq (x : Int) (l : List Int) :
    insertLe x l = List.orderedInsert (· ≤ ·) x l := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp [insertLe, List.orderedInsert, ih]

/-- The interpreter's `sortInts` is Mathlib's `insertionSort` at `(· ≤ ·)`. -/
theorem sortInts_eq (l : List Int) :
    sortInts l = List.insertionSort (· ≤ ·) l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortInts, List.insertionSort, ih, insertLe_eq]

/-- The sort output is ascending (`Pairwise (· ≤ ·)`). -/
theorem sortInts_pairwise (l : List Int) : (sortInts l).Pairwise (· ≤ ·) := by
  rw [sortInts_eq]; exact List.pairwise_insertionSort _ l

/-- The sort output is a permutation of the input. -/
theorem sortInts_perm (l : List Int) : (sortInts l).Perm l := by
  rw [sortInts_eq]; exact List.perm_insertionSort _ l

/-- Sorting preserves membership. (`sortInts_length` is Mathlib-free and
lives in `LeanModels/Python/Logic.lean`.) -/
theorem sortInts_mem (a : Int) (l : List Int) : a ∈ sortInts l ↔ a ∈ l :=
  (sortInts_perm l).mem_iff

/-- An already-sorted list is a fixpoint of `sortInts`. -/
theorem sortInts_of_pairwise {l : List Int} (h : l.Pairwise (· ≤ ·)) :
    sortInts l = l := by
  rw [sortInts_eq]; exact h.insertionSort_eq

/-- The `Val`-level bridge: `sortedVal` on a marshalled int list succeeds
with the (freshly) sorted marshalled list. -/
theorem sortedVal_int_list (l : List Int) :
    sortedVal (.listV ((l.map RVal.int).toArray))
      = .ok (.listV (((sortInts l).map RVal.int).toArray)) := by
  simp [sortedVal, asIntList_map_int]

/-! ## Pure list lemmas (getD access, sortedness monotonicity, counting) -/

-- `getD_eq_getElem` is the SHARED spec-side lemma now (VCTactic.lean
-- §marshalled-list indexing); it was copied here from `bench_bisect`.

/-- Sorted (`Pairwise (· ≤ ·)`) lists are monotone under `getD`-indexing
(bisect's `sorted_getD`, copied — the shared home is a later refactor). -/
theorem sorted_getD {xs : List Int} (hs : List.Pairwise (· ≤ ·) xs)
    {i j : Nat} (hij : i ≤ j) (hj : j < xs.length) :
    xs.getD i 0 ≤ xs.getD j 0 := by
  have hi : i < xs.length := Nat.lt_of_le_of_lt hij hj
  rcases Nat.lt_or_eq_of_le hij with h | h
  · have := (List.pairwise_iff_getElem.mp hs) i j hi hj h
    rw [getD_eq_getElem _ _ hi, getD_eq_getElem _ _ hj]
    exact this
  · subst h; exact Int.le_refl _
/-- This example's marshalling of the shared subscript-read lemma
(VCTactic.lean §marshalled-list indexing): `RVal.int` mapped directly, and
the right-hand side in the `Option.getD` form this file's residuals carry.
Unbounded it would be FALSE — out of range the left side is `RVal.none`,
the right `RVal.int 0`. -/
theorem arrVal_getElem (xs : List Int) (n : Nat) (h : n < xs.length) :
    (Option.map RVal.int xs[n]?).getD RVal.none = RVal.int (xs[n]?.getD 0) := by
  rw [map_getElem?_getD RVal.int RVal.none xs n h, List.getElem?_eq_getElem h]
  rfl

/-- A list all of whose elements satisfy `p` counts them all. -/
theorem countP_of_all {p : Int → Bool} :
    ∀ (l : List Int), (∀ a ∈ l, p a = true) → l.countP p = l.length
  | [], _ => rfl
  | a :: as, h => by
    have ha : p a = true := h a (by simp)
    have ih := countP_of_all as (fun x hx => h x (by simp [hx]))
    simp [ha, ih]

/-- **Rank characterization, membership**: the element at sorted rank `k`
is an element of the data. -/
theorem rank_mem (data : List Int) (k : Nat) (hk : k < data.length) :
    (sortInts data).getD k 0 ∈ data := by
  have hk' : k < (sortInts data).length := by rw [sortInts_length]; omega
  have : (sortInts data).getD k 0 ∈ sortInts data := by
    rw [getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  exact (sortInts_mem _ _).mp this

/-- **Rank characterization, lower count**: at least `k + 1` elements of
the data are `≤` the element at sorted rank `k` (the first `k + 1` sorted
elements are, and counting is permutation-invariant). -/
theorem rank_count_le (data : List Int) (k : Nat) (hk : k < data.length) :
    k + 1 ≤ data.countP (fun v => decide (v ≤ (sortInts data).getD k 0)) := by
  set s := sortInts data with hs_def
  have hsp : s.Pairwise (· ≤ ·) := sortInts_pairwise data
  have hslen : s.length = data.length := sortInts_length data
  have hperm : s.Perm data := sortInts_perm data
  rw [← hperm.countP_eq]
  have hk' : k < s.length := by omega
  have hall : ∀ a ∈ s.take (k + 1),
      (fun v => decide (v ≤ s.getD k 0)) a = true := by
    intro a ha
    rw [List.mem_iff_getElem] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hi' : i < k + 1 := by
      have := List.length_take (i := k + 1) (l := s)
      omega
    rw [List.getElem_take, ← getD_eq_getElem]
    simpa using sorted_getD hsp (by omega) hk'
  have hlen : (s.take (k + 1)).length = k + 1 := by
    rw [List.length_take]; omega
  calc k + 1
      = (s.take (k + 1)).countP (fun v => decide (v ≤ s.getD k 0)) := by
        rw [countP_of_all _ hall, hlen]
    _ ≤ s.countP (fun v => decide (v ≤ s.getD k 0)) :=
        (List.take_sublist _ _).countP_le

/-- **Rank characterization, upper count**: at least `n − k` elements of
the data are `≥` the element at sorted rank `k` (the sorted elements from
rank `k` on are). -/
theorem rank_count_ge (data : List Int) (k : Nat) (hk : k < data.length) :
    data.length - k
      ≤ data.countP (fun v => decide ((sortInts data).getD k 0 ≤ v)) := by
  set s := sortInts data with hs_def
  have hsp : s.Pairwise (· ≤ ·) := sortInts_pairwise data
  have hslen : s.length = data.length := sortInts_length data
  have hperm : s.Perm data := sortInts_perm data
  rw [← hperm.countP_eq]
  have hk' : k < s.length := by omega
  have hall : ∀ a ∈ s.drop k,
      (fun v => decide (s.getD k 0 ≤ v)) a = true := by
    intro a ha
    rw [List.mem_iff_getElem] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hi' : k + i < s.length := by
      have := List.length_drop (i := k) (l := s)
      omega
    rw [List.getElem_drop, ← getD_eq_getElem]
    simpa using sorted_getD hsp (Nat.le_add_right k i) hi'
  have hlen : (s.drop k).length = s.length - k := List.length_drop
  calc data.length - k
      = (s.drop k).countP (fun v => decide (s.getD k 0 ≤ v)) := by
        rw [countP_of_all _ hall, hlen, hslen]
    _ ≤ s.countP (fun v => decide (s.getD k 0 ≤ v)) :=
        (List.drop_sublist _ _).countP_le

/-! ## The total-correctness cores

Straight-line symbolic execution: `refine ⟨64, ?_⟩` (fuel is a depth
bound; 64 is generous), then one `py_simp` per branch with the guard and
index-bound facts precomputed. The `n == 0` raise guard is decided false
by `data ≠ []`; `median_low`'s `n % 2 == 1` splits by `by_cases` on the
interpreter's own `Int.fmod` form (passing the hypothesis in `fmod` form
keeps the rewrite aligned — normalizing to `%` first would unalign it). -/

private theorem length_pos (data : List Int) (hne : data ≠ []) :
    0 < data.length := by
  cases data with
  | nil => exact absurd rfl hne
  | cons a l => simp

/-- **Main theorem (`median_high`).** For every nonempty int list,
CPython's `median_high` — run byte-verbatim through the interpreter —
terminates and returns the element at sorted rank `⌊n/2⌋`. -/
theorem median_high_total (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_high(data) ==>
      (sortInts data).getD (data.length / 2) 0 := by
  have hpos : 0 < data.length := length_pos data hne
  have hfd : Int.fdiv ((data.length : Int)) 2 = (data.length : Int) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hnn : ¬((data.length : Int) / 2 < 0) := by omega
  have h0le : (0 : Int) ≤ (data.length : Int) / 2 := by omega
  have hlt : (data.length : Int) / 2 < (data.length : Int) := by omega
  have htn : (((data.length : Int)) / 2).toNat = data.length / 2 := by omega
  have hq := arrVal_getElem (sortInts data) (data.length / 2)
    (by rw [sortInts_length]; omega)
  refine ⟨64, ?_⟩
  py_simp [callFunction, callIn, bench_statistics, asIntList_map_toVal,
    asIntList_map_thaw_comp,
    hne, hfd, hnn, h0le, hlt, htn, hq]

/-- **Main theorem (`median_low`).** For every nonempty int list,
CPython's `median_low` terminates and returns the element at sorted rank
`⌊(n−1)/2⌋` — for odd `n` this is the middle rank `n/2` (`n//2` odd =
`(n−1)/2`), for even `n` the lower middle `n/2 − 1` (= `(n−1)/2`), so one
rank expression covers both vendored branches. -/
theorem median_low_total (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_low(data) ==>
      (sortInts data).getD ((data.length - 1) / 2) 0 := by
  have hpos : 0 < data.length := length_pos data hne
  have hfd : Int.fdiv ((data.length : Int)) 2 = (data.length : Int) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hm : Int.fmod ((data.length : Int)) 2 = (data.length : Int) % 2 :=
    Int.fmod_eq_emod_of_nonneg _ (by omega)
  have hq := arrVal_getElem (sortInts data) ((data.length - 1) / 2)
    (by rw [sortInts_length]; omega)
  refine ⟨64, ?_⟩
  by_cases hpar : Int.fmod ((data.length : Int)) 2 = 1
  · -- odd length: return data[n // 2], and n//2 = (n-1)/2
    have hmod : (data.length : Int) % 2 = 1 := by rw [← hm]; exact hpar
    have hnn : ¬((data.length : Int) / 2 < 0) := by omega
    have h0le : (0 : Int) ≤ (data.length : Int) / 2 := by omega
    have hlt : (data.length : Int) / 2 < (data.length : Int) := by omega
    have htn : (((data.length : Int)) / 2).toNat = (data.length - 1) / 2 := by
      omega
    py_simp [callFunction, callIn, bench_statistics, asIntList_map_toVal,
    asIntList_map_thaw_comp,
      hne, hfd, hpar, hnn, h0le, hlt, htn, hq]
  · -- even length: return data[n // 2 - 1], and n//2 − 1 = (n-1)/2
    have hmod : (data.length : Int) % 2 = 0 := by
      rw [hm] at hpar; omega
    have hL2 : 2 ≤ data.length := by omega
    have hnn : ¬((data.length : Int) / 2 - 1 < 0) := by omega
    have h1le : (1 : Int) ≤ (data.length : Int) / 2 := by omega
    have hlt : (data.length : Int) / 2 - 1 < (data.length : Int) := by omega
    have htn : ((((data.length : Int)) / 2) - 1).toNat = (data.length - 1) / 2 := by
      omega
    py_simp [callFunction, callIn, bench_statistics, asIntList_map_toVal,
    asIntList_map_thaw_comp,
      hne, hfd, hpar, hnn, h1le, hlt, htn, hq]

/-! ## The public corollaries -/

/-- **Rank characterization (`median_low`, `⇓`-relational)**: any observed
result is an element of the data, with at least `⌊(n−1)/2⌋ + 1` data
elements `≤` it and at least `n − ⌊(n−1)/2⌋` data elements `≥` it — the
order-statistics contract over SYMBOLIC data, not "index into sorted()". -/
theorem median_low_rank (data : List PyInt) (hne : data ≠ []) {r : PyInt}
    (h : bench_statistics.median_low(data) ⇓ r) :
    r ∈ data ∧
      (data.length - 1) / 2 + 1 ≤ data.countP (fun v => decide (v ≤ r)) ∧
      data.length - (data.length - 1) / 2
        ≤ data.countP (fun v => decide (r ≤ v)) := by
  have htot := median_low_total data hne
  have heq : (ToVal.toVal r : Val)
      = ToVal.toVal ((sortInts data).getD ((data.length - 1) / 2) 0) :=
    CallsTo.eq_of_partialTo h htot.partialTo
  have hr : r = (sortInts data).getD ((data.length - 1) / 2) 0 := by
    simpa using heq
  subst hr
  have hpos : 0 < data.length := length_pos data hne
  have hk : (data.length - 1) / 2 < data.length := by omega
  exact ⟨rank_mem data _ hk, rank_count_le data _ hk, rank_count_ge data _ hk⟩

/-- **Rank characterization (`median_high`, `⇓`-relational)**: at least
`⌊n/2⌋ + 1` data elements `≤` it, at least `n − ⌊n/2⌋` data elements
`≥` it. -/
theorem median_high_rank (data : List PyInt) (hne : data ≠ []) {r : PyInt}
    (h : bench_statistics.median_high(data) ⇓ r) :
    r ∈ data ∧
      data.length / 2 + 1 ≤ data.countP (fun v => decide (v ≤ r)) ∧
      data.length - data.length / 2
        ≤ data.countP (fun v => decide (r ≤ v)) := by
  have htot := median_high_total data hne
  have heq : (ToVal.toVal r : Val)
      = ToVal.toVal ((sortInts data).getD (data.length / 2) 0) :=
    CallsTo.eq_of_partialTo h htot.partialTo
  have hr : r = (sortInts data).getD (data.length / 2) 0 := by
    simpa using heq
  subst hr
  have hpos : 0 < data.length := length_pos data hne
  have hk : data.length / 2 < data.length := by omega
  exact ⟨rank_mem data _ hk, rank_count_le data _ hk, rank_count_ge data _ hk⟩

/-- **Strengthened partial correctness (`median_low`, `~~>`)**: every run,
at every fuel, either times out or returns exactly the low median — no
exception, no `unsupported`, no other value. Free via fuel determinism. -/
theorem median_low_partial (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_low(data) ~~>
      (sortInts data).getD ((data.length - 1) / 2) 0 :=
  (median_low_total data hne).partialTo

/-- **Strengthened partial correctness (`median_high`, `~~>`)**. -/
theorem median_high_partial (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_high(data) ~~>
      (sortInts data).getD (data.length / 2) 0 :=
  (median_high_total data hne).partialTo

/-- **Low ≤ high**: on the same data, any observed `median_low` result is
`≤` any observed `median_high` result (ranks `⌊(n−1)/2⌋ ≤ ⌊n/2⌋` in an
ascending list). -/
theorem median_low_le_median_high (data : List PyInt) (hne : data ≠ [])
    {lo hi : PyInt} (hlo : bench_statistics.median_low(data) ⇓ lo)
    (hhi : bench_statistics.median_high(data) ⇓ hi) :
    lo ≤ hi := by
  have hpos : 0 < data.length := length_pos data hne
  have hloEq : lo = (sortInts data).getD ((data.length - 1) / 2) 0 := by
    simpa using CallsTo.eq_of_partialTo hlo (median_low_partial data hne)
  have hhiEq : hi = (sortInts data).getD (data.length / 2) 0 := by
    simpa using CallsTo.eq_of_partialTo hhi (median_high_partial data hne)
  subst hloEq hhiEq
  exact sorted_getD (sortInts_pairwise data) (by omega)
    (by rw [sortInts_length]; omega)

/-- **Pre-sorted input (`median_low`)**: on already-ascending data the low
median is literally `data[(n−1)/2]` (`sortInts` fixpoint). -/
theorem median_low_presorted (data : List PyInt) (hne : data ≠ [])
    (hs : data.Pairwise (· ≤ ·)) :
    bench_statistics.median_low(data) ==>
      data.getD ((data.length - 1) / 2) 0 := by
  have h := median_low_total data hne
  rwa [sortInts_of_pairwise hs] at h

/-- **Pre-sorted input (`median_high`)**: `data[n/2]`. -/
theorem median_high_presorted (data : List PyInt) (hne : data ≠ [])
    (hs : data.Pairwise (· ≤ ·)) :
    bench_statistics.median_high(data) ==> data.getD (data.length / 2) 0 := by
  have h := median_high_total data hne
  rwa [sortInts_of_pairwise hs] at h

end Examples.python.bench_statistics.proof
