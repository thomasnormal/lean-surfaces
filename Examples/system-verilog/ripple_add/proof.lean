/-
Proof module for `Examples/system-verilog/ripple_add/spec.lean` (three-file
example layout, SV lane; the Design2 proof layer's acceptance example):

  ripple_add.sv      — the design (`N`-bit ripple-carry adder, one
                       `generate for` over the bit index)
  ripple_add.sv.json — generated envelope (extractors/sv/extract.py)
  gen.lean           — `load_design_sv2` + the instantiated process list and
                       declarations at SYMBOLIC `N` (`ripple_sem_processes`,
                       `ripple_sem_decls`)
  proof.lean         — THIS FILE: the real proofs (namespace
                       `Examples.«system-verilog».ripple_add.proof`)
  spec.lean          — concrete `run2` rows, and the statements, each proved
                       `:= by proofs`
-/
import Examples.«system-verilog».ripple_add.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2

/-!
# The ripple-carry adder is correct, for every width `N ≥ 1`

`ripple_add.sem N` (the `load_design_sv2` family of `ripple_add.sv`) is, by
`gen.lean`, the process list

    0:      c[0]   = cin
    1:      cout   = c[N]
    2i+2:   s[i]   = a[i] ^ b[i] ^ c[i]                       (i < N)
    2i+3:   c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]))   (i < N)

over the declarations `a b s : N`, `cin cout : 1`, `c : N + 1`. This file
proves, for EVERY `N ≥ 1`, every schedule, every stimulus, and every completed
run, that a snapshot whose inputs hold known values `x y : BitVec N`,
`ci : Bool` carries `x + y + ci` (mod `2^N`) on `s` and the carry-out
`2^N ≤ x + y + ci` on `cout`; and that every run completes.

Nothing is unrolled at a fixed width and nothing is bit-blasted: `N` stays a
variable from the envelope to the conclusion. The proof is the
`Comb2Example.lean` template (the full adder) scaled to a generate family.

## API index

* The process table: `ripple_proc` (index `j` holds `p` iff one of the four
  rows above), its forward instances `ripple_proc_cin`/`_cout`/`_sum`/`_carry`,
  and the list lemma under it, `getElem?_flatMap_pair`.
* Declarations (`1 ≤ N`): `ripple_declWidth` (+ `_s`, `_cout`, `_c`),
  `ripple_inputNames`; write windows `ripple_writes`; driven signals
  `ripple_driven`.
* The profile and the certificate: `ripple_comb : CombDesign`,
  `ripple_acyclic : Acyclic` (rank `rippleRank`: carry-in 0, bit `i`'s two
  cells `i + 1`, carry-out `N + 1`).
* Gate algebra on known 1-bit values: `eval_bit` (`x[i]` of a known
  signal), `eval_win` (a 1-bit window of a PARTIALLY known signal — the carry
  chain `c` is known one bit at a time), `eval_xor3` (the sum cell),
  `eval_carry` (the carry cell is `Bool.atLeastTwo`, core's ripple-carry
  majority).
* The settled state: `ripple_settled` — in any state solving the design's
  equations (`CombEqs`) with the comb shape (`StateShape`), known inputs give
  the sum on `s` and the carry-out on `cout`; `ripple_arith` is the
  arithmetic reading `cout · 2^N + s = x + y + ci`.
* The theorems: `ripple_terminates`, `ripple_correct`,
  `ripple_correct_stim`, `ripple_correct_nat`, and the packaged non-vacuity
  `example`.

## Design laws

* **Induction on the bit index, never on fuel or `N`.** The carry chain is
  proved window by window (`hcarry` inside `ripple_settled`: induction on
  `k ≤ N`, the window `c[k]` holds core's `BitVec.carry k x y ci`), so the
  inductive step is ONE process equation (`CombEqs.extract_slice` on the
  carry cell `2k+3`) plus `BitVec.carry_succ`. The sum bit `i` is then
  `BitVec.getLsbD_add_add_bool`, and `s` is assembled from its 1-bit windows
  by `LVec.eq_ofBitVec_of_extract_one`; `cout` is `BitVec.carry_width`.
* **The carry chain is never known as a whole.** `c` is only ever read
  through 1-bit windows whose value has been proved (`eval_win`); nothing
  claims `c` holds an `ofBitVec`, and nothing needs to.
* **Run level is the layer's.** `Models2.of_comb_pointwise` /
  `Models2.of_comb_inputs` reduce `⊨₂` to `ripple_settled`;
  `Terminates2.of_acyclic` gives `Terminates2`. No `Runs2`/`run2`/fuel/
  schedule appears in any proof here.
* **`decide` only on closed design data** (the six declaration names in
  `ripple_comb.nodup`, the three input names in `notInput`, the signal-name
  disequalities in `disjoint`, and `0 < 2` in `ripple_arith`); every
  input-dependent fact is symbolic.

## Lemmas that belong in the layer

`getElem?_flatMap_pair` (a `List` fact), `eval_win` / `eval_bit` /
`eval_xor3` / `eval_carry` (`Known2`-level gate algebra over 1-bit windows),
and `ripple_arith` (the `BitVec` carry-out identity) are design-agnostic;
they live here until a second consumer needs them, and are candidates for
promotion into `Known2.lean` / `Comb2.lean`.
-/

namespace Examples.«system-verilog».ripple_add.proof

open LeanModels.Sv
open Examples.«system-verilog».ripple_add.gen

/-! ## The process table -/

/-- Indexing the bit-interleaved family `[f 0, g 0, f 1, g 1, …]`: entry `m`
is `f (m / 2)` at even `m`, `g (m / 2)` at odd `m`, below `2N`. -/
theorem getElem?_flatMap_pair {α : Type} (N : Nat) : ∀ (f g : Nat → α) (m : Nat),
    ((List.range N).flatMap fun i => [f i, g i])[m]? =
      if m < 2 * N then some (if m % 2 = 0 then f (m / 2) else g (m / 2)) else none := by
  induction N with
  | zero => intro f g m; simp
  | succ N ih =>
    intro f g m
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    match m with
    | 0 => simp
    | 1 => simp; omega
    | m + 2 =>
      rw [List.cons_append, List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem?_cons_succ]
      rw [ih (fun i => f (i + 1)) (fun i => g (i + 1)) m]
      have h1 : (m + 2) / 2 = m / 2 + 1 := by omega
      have h2 : (m + 2) % 2 = m % 2 := by omega
      rw [h1, h2]
      by_cases h : m < 2 * N
      · have h' : m + 2 < 2 * (N + 1) := by omega
        simp only [h, h', if_true]
      · have h' : ¬ (m + 2 < 2 * (N + 1)) := by omega
        simp only [h, h', if_false]

/-- The process array of `ripple_add.sem N` is `rippleProcs N` (`gen.lean`). -/
theorem ripple_getElem? (N j : Nat) :
    (ripple_add.sem N).processes[j]? = (rippleProcs N)[j]? := by
  rw [← Array.getElem?_toList, ripple_sem_processes]

/-- **The process table, by index** (every `N`): carry-in at 0, carry-out at
1, then bit `i`'s sum cell at `2i + 2` and carry cell at `2i + 3`. -/
theorem ripple_proc {N j : Nat} {p : Process2} :
    (ripple_add.sem N).processes[j]? = some p ↔
      (j = 0 ∧ p = cinProc) ∨ (j = 1 ∧ p = coutProc N) ∨
      ∃ i < N, (j = 2 * i + 2 ∧ p = sumProc i) ∨ (j = 2 * i + 3 ∧ p = carryProc i) := by
  rw [ripple_getElem?]
  match j with
  | 0 => simp [rippleProcs, eq_comm]
  | 1 => simp [rippleProcs, eq_comm]
  | m + 2 =>
    simp only [rippleProcs, List.getElem?_cons_succ, getElem?_flatMap_pair]
    constructor
    · intro h
      by_cases hm : m < 2 * N
      · rw [if_pos hm] at h
        right; right
        refine ⟨m / 2, by omega, ?_⟩
        by_cases h2 : m % 2 = 0
        · rw [if_pos h2, Option.some.injEq] at h
          exact Or.inl ⟨by omega, h.symm⟩
        · rw [if_neg h2, Option.some.injEq] at h
          exact Or.inr ⟨by omega, h.symm⟩
      · rw [if_neg hm] at h
        cases h
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨i, hi, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩)
      · omega
      · omega
      · obtain rfl : m = 2 * i := by omega
        rw [if_pos (by omega), if_pos (by omega), Nat.mul_div_cancel_left _ (by omega)]
      · obtain rfl : m = 2 * i + 1 := by omega
        rw [if_pos (by omega), if_neg (by omega)]
        congr 2
        omega

/-- Process 0 is the carry-in `c[0] = cin`. -/
theorem ripple_proc_cin (N : Nat) : (ripple_add.sem N).processes[0]? = some cinProc :=
  ripple_proc.mpr (Or.inl ⟨rfl, rfl⟩)

/-- Process 1 is the carry-out `cout = c[N]`. -/
theorem ripple_proc_cout (N : Nat) : (ripple_add.sem N).processes[1]? = some (coutProc N) :=
  ripple_proc.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- Process `2i + 2` is bit `i`'s sum cell. -/
theorem ripple_proc_sum {N i : Nat} (hi : i < N) :
    (ripple_add.sem N).processes[2 * i + 2]? = some (sumProc i) :=
  ripple_proc.mpr (Or.inr (Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩))

/-- Process `2i + 3` is bit `i`'s carry cell. -/
theorem ripple_proc_carry {N i : Nat} (hi : i < N) :
    (ripple_add.sem N).processes[2 * i + 3]? = some (carryProc i) :=
  ripple_proc.mpr (Or.inr (Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩))

/-! ## Declarations, windows, driven signals (`1 ≤ N`) -/

section Decls

variable {N : Nat} (hN : 1 ≤ N)
include hN

/-- Declared widths are looked up in `rippleDecls N`. -/
theorem ripple_declWidth (n : String) :
    (ripple_add.sem N).declWidth n =
      ((rippleDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, ripple_sem_decls N hN]

/-- `s` is `N` bits. -/
theorem ripple_declWidth_s : (ripple_add.sem N).declWidth "s" = some N := by
  simp [ripple_declWidth hN, rippleDecls]

/-- `cout` is 1 bit. -/
theorem ripple_declWidth_cout : (ripple_add.sem N).declWidth "cout" = some 1 := by
  simp [ripple_declWidth hN, rippleDecls]

/-- The carry chain `c` is `N + 1` bits. -/
theorem ripple_declWidth_c : (ripple_add.sem N).declWidth "c" = some (N + 1) := by
  simp [ripple_declWidth hN, rippleDecls]

/-- The input ports, in declaration order. -/
theorem ripple_inputNames : (ripple_add.sem N).inputNames.toList = ["a", "b", "cin"] := by
  simp [Design2.inputNames, ripple_sem_decls N hN, rippleDecls]

/-- **The write windows**: carry-in writes `c[0]`, carry-out the whole 1-bit
`cout`, bit `i`'s sum cell `s[i]` and its carry cell `c[i+1]`. -/
theorem ripple_writes {j : Nat} {wn : Win} : (ripple_add.sem N).Writes j wn ↔
    (j = 0 ∧ wn = ("c", 0, 1)) ∨ (j = 1 ∧ wn = ("cout", 0, 1)) ∨
    ∃ i < N, (j = 2 * i + 2 ∧ wn = ("s", i, 1)) ∨
      (j = 2 * i + 3 ∧ wn = ("c", i + 1, 1)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases ripple_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨i, hi, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;>
      simp [ripple_declWidth_cout hN] at hw <;> subst hw
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact ⟨_, _, ripple_proc_cin N, by simp⟩
    · exact ⟨_, _, ripple_proc_cout N, by simp [ripple_declWidth_cout hN]⟩
    · exact ⟨_, _, ripple_proc_sum hi, by simp⟩
    · exact ⟨_, _, ripple_proc_carry hi, by simp⟩

/-- The driven signals: the carry chain, the carry-out, the sum. -/
theorem ripple_driven {n : String} : Driven (ripple_add.sem N) n ↔
    n = "c" ∨ n = "cout" ∨ n = "s" := by
  constructor
  · rintro ⟨j, lo, w, h⟩
    rcases (ripple_writes hN).mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, 1, (ripple_writes hN).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨1, 0, 1, (ripple_writes hN).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨2, 0, 1,
        (ripple_writes hN).mpr (Or.inr (Or.inr ⟨0, hN, Or.inl ⟨rfl, rfl⟩⟩))⟩

end Decls

/-! ## The comb profile and the acyclicity certificate -/

/-- **The ripple adder is in the comb profile** (every `N ≥ 1`): continuous
assigns over 1-bit windows, in range, one driver per bit, no input driven,
no loud node, every read declared, no initializers. -/
theorem ripple_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) where
  nodup := by
    rw [ripple_sem_decls N hN]
    simp only [rippleDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hp
    rcases ripple_proc.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, _, rfl, rfl⟩
    · exact ⟨_, _, [("cout", 0, 1)], rfl, by simp [ripple_declWidth_cout hN]⟩
    · exact ⟨_, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, rfl, rfl⟩
  inWidth := by
    intro j n lo w h
    rcases (ripple_writes hN).mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, hi, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h
    · exact ⟨_, ripple_declWidth_c hN, by omega⟩
    · exact ⟨_, ripple_declWidth_cout hN, by omega⟩
    · exact ⟨_, ripple_declWidth_s hN, by omega⟩
    · exact ⟨_, ripple_declWidth_c hN, by omega⟩
  notInput := by
    intro n hn
    rw [ripple_inputNames hN]
    rcases (ripple_driven hN).mp hn with rfl | rfl | rfl <;> decide
  disjoint := by
    intro j k wj wk hjk hj hk
    rcases (ripple_writes hN).mp hj with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    rcases (ripple_writes hN).mp hk with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i', hi', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      rw [Win.overlaps_eq_false] <;> first | (left; decide) | (right; omega) | omega
  selfDisjoint := by
    intro j t e hp
    rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro j t e hp
    rw [ripple_sem_decls N hN]
    rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> simp [Expr2.idents, rippleDecls]
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [ripple_sem_decls N hN] at hdc
    simp [rippleDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [ripple_sem_decls N hN] at hdc
    simp [rippleDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The rank certificate: carry-in 0, bit `i`'s sum and carry cells (indices
`2i + 2`, `2i + 3`) both `i + 1`, carry-out `N + 1`. -/
def rippleRank (N : Nat) (j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then N + 1 else (j - 2) / 2 + 1

/-- **The ripple adder is acyclic**: bit `i`'s cells read `a[i]`, `b[i]` (inputs,
never written) and `c[i]`, written by the carry-in (`i = 0`, rank 0) or by bit
`i - 1`'s carry cell (rank `i`); the carry-out reads `c[N]`, written by bit
`N - 1`'s carry cell (rank `N`). -/
theorem ripple_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  refine ⟨rippleRank N, ?_⟩
  intro j k tj ej tk ek wk hj hk hw hex
  have hWk := (ripple_writes hN).mp ⟨tk, ek, hk, hw⟩
  rcases ripple_proc.mp hj with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨i, hi, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ <;>
    simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
    obtain ⟨-, rfl⟩ := h <;>
    rcases hWk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i', hi', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    simp [Expr2.reads, Expr2.sliceReads, ReadWin.overlaps, Win.overlaps_eq_true] at hex <;>
    unfold rippleRank <;> (repeat' split) <;> omega

/-! ## Gate algebra on known 1-bit values -/

section Gates

variable {st : SvState}

/-- A bit select `n[i]` of a known signal (in range). -/
theorem eval_bit {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice (.ident n) i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

/-- A 1-bit window `n[k]` of a signal whose OTHER bits may be unknown: only the
window's own value matters (the carry chain is known one bit at a time). -/
theorem eval_win {n : String} {u : LVec} {k : Nat} {b : Bool}
    (h : SvState.lookup st n = some u) (hk : u.extract k 1 = LVec.ofBitVec (BitVec.ofBool b)) :
    evalPure2 st (.slice (.ident n) k 1) = .ok (LVec.ofBitVec (BitVec.ofBool b)) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    hk]

/-- The sum cell `l ^ m ^ r` over known bits. -/
theorem eval_xor3 {l m r : Expr2} {p q b : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hm : evalPure2 st m = .ok (LVec.ofBitVec (BitVec.ofBool q)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    evalPure2 st (.binary .xor (.binary .xor l m) r) =
      .ok (LVec.ofBitVec (BitVec.ofBool (p ^^ q ^^ b))) := by
  rw [evalPure2_xor_ofBitVec (evalPure2_xor_ofBitVec hl hm) hr, BitVec.ofBool_xor_ofBool,
    BitVec.ofBool_xor_ofBool]

/-- The carry cell `(l & m) | (r & (l ^ m))` over known bits is core's
majority `Bool.atLeastTwo` (the gate of `BitVec.carry_succ`). -/
theorem eval_carry {l m r : Expr2} {p q b : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hm : evalPure2 st m = .ok (LVec.ofBitVec (BitVec.ofBool q)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    evalPure2 st (.binary .or (.binary .and l m) (.binary .and r (.binary .xor l m))) =
      .ok (LVec.ofBitVec (BitVec.ofBool (Bool.atLeastTwo p q b))) := by
  rw [evalPure2_or_ofBitVec (evalPure2_and_ofBitVec hl hm)
    (evalPure2_and_ofBitVec hr (evalPure2_xor_ofBitVec hl hm)), BitVec.ofBool_xor_ofBool,
    BitVec.ofBool_and_ofBool, BitVec.ofBool_and_ofBool, BitVec.ofBool_or_ofBool]
  cases p <;> cases q <;> cases b <;> rfl

end Gates

/-! ## The settled state -/

/-- **The ripple adder, one settled state.** In any state that solves the
design's equations and has the comb shape, known inputs `x y : BitVec N`,
`ci : Bool` on `a b cin` give `x + y + ci` (mod `2^N`) on `s` and the carry-out
`2^N ≤ x + y + ci` on `cout`. -/
theorem ripple_settled {N : Nat} (hN : 1 ≤ N) {st : SvState}
    (heqs : CombEqs (ripple_add.sem N) st) (hs : StateShape (ripple_add.sem N) st)
    {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
      SvState.lookup st "cout" =
        some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  obtain ⟨u, hu, -⟩ := hs.driven "c" ((ripple_driven hN).mpr (Or.inl rfl))
  -- the carry chain, window by window: `c[k]` holds core's `carry k`
  have hcarry : ∀ k, k ≤ N →
      u.extract k 1 = LVec.ofBitVec (BitVec.ofBool (BitVec.carry k x y ci)) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨old, hold, hext⟩ :=
        CombEqs.extract_slice heqs (ripple_proc_cin N) (evalPure2_ident_ofBitVec hc)
      rw [hu, Option.some.injEq] at hold
      subst hold
      rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_zero]
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs (ripple_proc_carry hkN)
        (eval_carry (eval_bit ha hkN) (eval_bit hb hkN) (eval_win hu (ih (by omega))))
      rw [hu, Option.some.injEq] at hold
      subst hold
      rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_succ]
  -- the sum, from its 1-bit windows
  obtain ⟨sv, hsv, hsw⟩ := hs.driven "s" ((ripple_driven hN).mpr (Or.inr (Or.inr rfl)))
  rw [ripple_declWidth_s hN, Option.some.injEq] at hsw
  have hS : sv = LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N) := by
    apply LVec.eq_ofBitVec_of_extract_one hsw.symm
    intro i hi
    obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs (ripple_proc_sum hi)
      (eval_xor3 (eval_bit ha hi) (eval_bit hb hi) (eval_win hu (hcarry i (by omega))))
    rw [hsv, Option.some.injEq] at hold
    subst hold
    rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.getLsbD_add_add_bool hi,
      Bool.xor_assoc]
  -- the carry-out: `c[N]` is the final carry
  have hco := CombEqs.lookup_ident (ripple_comb N hN) heqs hs (ripple_proc_cout N)
    (eval_win hu (hcarry N (Nat.le_refl N))) (ripple_declWidth_cout hN)
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_width] at hco
  exact ⟨hS ▸ hsv, hco⟩

/-- **The arithmetic reading** of the two outputs: carry-out times `2^N` plus
the truncated sum is the full sum `x + y + ci`. -/
theorem ripple_arith {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    (decide (2 ^ N ≤ x.toNat + y.toNat + ci.toNat)).toNat * 2 ^ N +
      (x + y + (BitVec.ofBool ci).setWidth N).toNat = x.toNat + y.toNat + ci.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hcM : ci.toNat < 2 ^ N := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  rw [Nat.mod_eq_of_lt hcM, Nat.mod_add_mod]
  generalize 2 ^ N = M at *
  by_cases h : M ≤ x.toNat + y.toNat + ci.toNat
  · rw [decide_eq_true h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.toNat_true]
    omega
  · rw [decide_eq_false h, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.toNat_false]
    omega

/-! ## The theorems -/

/-- **Non-vacuity**: for every `N ≥ 1`, every run of the ripple adder
completes, under every schedule and every stimulus. -/
theorem ripple_terminates (N : Nat) (hN : 1 ≤ N) : Terminates2 (ripple_add.sem N) :=
  Terminates2.of_acyclic (ripple_comb N hN) (ripple_acyclic N hN)

/-- **Ripple-adder correctness** (snapshot form, every `N ≥ 1`): on every
snapshot of every completed run whose inputs hold known values, `s` holds the
`N`-bit sum `x + y + ci` and `cout` holds the carry-out. -/
theorem ripple_correct (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) :=
  Models2.of_comb_pointwise (ripple_comb N hN) fun _ heqs hs _ _ _ ha hb hc =>
    ripple_settled hN heqs hs ha hb hc

/-- **Ripple-adder correctness** (stimulus form): whenever cycle `c`'s
stimulus entry drives `a`, `b`, `cin` with known values, snapshot `c` carries
their sum on `s` and the carry-out on `cout`. -/
theorem ripple_correct_stim (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
      stim[c]? = some inputs → tr[c]? = some st → ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup inputs "a" = some (LVec.ofBitVec x) →
        SvState.lookup inputs "b" = some (LVec.ofBitVec y) →
        SvState.lookup inputs "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  apply Models2.of_comb_inputs (ripple_comb N hN)
  intro stim tr h c inputs st hi hc x y ci ha hb hci
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  have hmem : ∀ n, n = "a" ∨ n = "b" ∨ n = "cin" →
      n ∈ (ripple_add.sem N).inputNames.toList := by
    rw [ripple_inputNames hN]
    rintro n (rfl | rfl | rfl) <;> simp
  exact ripple_settled hN heqs hs
    (hin inputs hi "a" (hmem _ (Or.inl rfl)) _ ha)
    (hin inputs hi "b" (hmem _ (Or.inr (Or.inl rfl))) _ hb)
    (hin inputs hi "cin" (hmem _ (Or.inr (Or.inr rfl))) _ hci)

/-- **Ripple-adder correctness** (arithmetic form): on every snapshot with
known inputs, the outputs are known, and carry-out · `2^N` + sum is exactly
`x + y + ci` as natural numbers (no `BitVec` wrap in sight). -/
theorem ripple_correct_nat (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        ∃ (sv : BitVec N) (co : Bool),
          SvState.lookup st "s" = some (LVec.ofBitVec sv) ∧
          SvState.lookup st "cout" = some (LVec.ofBitVec (BitVec.ofBool co)) ∧
          co.toNat * 2 ^ N + sv.toNat = x.toNat + y.toNat + ci.toNat :=
  Models2.imp (fun _ _ h c st hc x y ci ha hb hci =>
    ⟨_, _, (h c st hc x y ci ha hb hci).1, (h c st hc x y ci ha hb hci).2,
      ripple_arith hN x y ci⟩) (ripple_correct N hN)

/-- Non-vacuity, packaged: under every schedule and stimulus a completed run
EXISTS, and it satisfies the correctness statement. -/
example (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 (ripple_add.sem N) σ stim tr ∧ ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) :=
  Models2.exists_of_terminates (ripple_terminates N hN) (ripple_correct N hN) σ stim

/-! ## Axiom pins

Standard axioms only — no `sorry`, no `native_decide`, no `bv_decide`. The
`#guard_msgs` wrappers make the build fail if any of these drifts. They
compare with `whitespace := lax`: the fully qualified names make some
messages longer than the pretty-printer's line width, and lax matching keeps
the pins independent of where (or whether) Lean breaks such a line.
`spec.lean` pins the spec-side twins of the four main theorems separately. -/

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_terminates

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_correct

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_correct_stim' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_correct_stim

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_correct_nat' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_correct_nat

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_settled' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_settled

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_comb' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_comb

/--
info: 'Examples.«system-verilog».ripple_add.proof.ripple_acyclic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ripple_acyclic

end Examples.«system-verilog».ripple_add.proof
