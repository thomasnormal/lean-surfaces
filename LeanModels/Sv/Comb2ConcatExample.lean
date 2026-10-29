import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2

/-!
# The combinational settle theorem on CONCATENATED targets (`LeanModels.Sv` — Design2)

The acceptance example for concatenation targets in the comb profile
(`Comb2Base`: `Lhs2.windows?`, `Win.placed`, `combWrite`, the generalized
`CombEqs`; `Comb2`: `CombEqs.concat_part` / `CombEqs.concat_part_ident`).
Two designs, both hand-built in exactly the shape the sv-0.2 instantiation
produces:

1. **`caddDesign N`** — the one-line adder

       assign {cout, s} = a + b + cin;      // a, b, s : N bits; cin, cout : 1 bit

   at EVERY width `N` (no unrolling, `N` stays a variable), with the
   right-hand side at its context width `N + 1` (each operand zero-extended,
   LRM §11.6 — the `resize` nodes `fitExpr2` inserts). Proved: every run
   completes (`cadd_terminates`), and on every snapshot with known inputs `s`
   holds `x + y + ci` mod `2^N` and `cout` the carry-out — the SAME statement
   `Examples/system-verilog/ripple_add` proves of the gate-level ripple adder
   (`cadd_correct`, `cadd_correct_stim`), plus the arithmetic reading
   `cout · 2^N + s = x + y + ci` (`cadd_correct_nat`).
2. **`splitDesign`** — a NESTED concatenation mixing constant slices and a
   whole signal, two windows of the same signal in one target:

       assign {y[3:2], {z, y[1:0]}} = x;    // x : 5 bits; y : 4 bits; z : 1 bit

   Proved: `y = {x[4:3], x[1:0]}` and `z = x[2]` on every snapshot with known
   `x` (`split_correct`), and termination (`split_terminates`). The `#guard`s
   check the MSB-first distribution against `run2`.

## The proof pattern for a concatenated target

* The profile obligations are those of a leaf design plus
  `CombDesign.selfDisjoint` (the target's windows are pairwise disjoint —
  `Win.overlaps` on distinct names is `false` by `simp`). The windows come
  from `Lhs2.wins` by `simp` (`cadd_wins`), and so do their offsets
  (`Win.placed`) and the total width (`Win.sumWidth`).
* `CombEqs.concat_part_ident` reads a whole-signal part back as a slice of
  the resized right-hand side; `CombEqs.concat_part` reads a slice part back
  as a window equation.
* `sv2_known` evaluates the right-hand side to `ofBitVec` of a `BitVec` term;
  `LVec.resizeU_ofBitVec` / `LVec.extract_ofBitVec` /
  `LVec.extract_one_ofBitVec` turn the slices into `extractLsb'` / `getLsbD`;
  what remains is `BitVec`/`Nat` arithmetic (`cadd_toNat`, `cadd_low`,
  `cadd_carry`). `LVec.eq_ofBitVec_append_of_extract` assembles an output
  from two adjacent windows.

No `decide` over input values, no `bv_decide`, no `native_decide`; `decide`
appears only on closed design data (signal names).

## Lemmas that belong in the layer

`LVec.eq_ofBitVec_append_of_extract` (assembling a known vector from two
adjacent windows) is design-agnostic `Known2`-level algebra; it lives here
until a second consumer needs it.
-/

namespace LeanModels.Sv

namespace Comb2ConcatExample

/-! ## Assembling a known vector from two windows -/

/-- **Two adjacent windows assemble a known vector**: a vector of width
`k + m` whose low `k` bits hold `y` and whose next `m` bits hold `x` is
`ofBitVec (x ++ y)` (`++` puts its left operand in the high bits). -/
theorem LVec.eq_ofBitVec_append_of_extract {v : LVec} {m k : Nat} {x : BitVec m}
    {y : BitVec k} (hw : v.width = m + k) (hlo : v.extract 0 k = LVec.ofBitVec y)
    (hhi : v.extract k m = LVec.ofBitVec x) : v = LVec.ofBitVec (x ++ y) := by
  apply LVec.eq_ofBitVec_of_extract_one hw
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases hik : i < k
  · rw [if_pos hik]
    have := LVec.extract_extract v (lo := 0) (w := k) (lo' := i) (w' := 1) (by omega)
    rw [Nat.zero_add] at this
    rw [← this, hlo, LVec.extract_one_ofBitVec _ hik]
  · rw [if_neg hik]
    have := LVec.extract_extract v (lo := k) (w := m) (lo' := i - k) (w' := 1) (by omega)
    rw [Nat.add_sub_cancel' (by omega)] at this
    rw [← this, hhi, LVec.extract_one_ofBitVec _ (by omega)]

/-! ## The concatenated-target adder `assign {cout, s} = a + b + cin;` -/

/-- The target `{cout, s}`: MSB-first, so `cout` receives the top bit. -/
def caddTarget : Lhs2 := .concat [.ident "cout", .ident "s"]

/-- The right-hand side `a + b + cin` at the target's context width `N + 1`:
every operand zero-extended to `N + 1` bits (the `resize` nodes the sv-0.2
instantiation inserts for a rigid operand in a wider context, LRM §11.6/§11.8.2),
so the addition keeps its carry. -/
def caddRhs (N : Nat) : Expr2 :=
  .binary .add (.binary .add (.resize (N + 1) (.ident "a")) (.resize (N + 1) (.ident "b")))
    (.resize (N + 1) (.ident "cin"))

/-- The concatenated-target adder at width `N`. -/
def caddDesign (N : Nat) : Design2 where
  name := "cadd"
  decls := #[
    { name := "a", width := N, isInput := true },
    { name := "b", width := N, isInput := true },
    { name := "cin", width := 1, isInput := true },
    { name := "s", width := N, isOutput := true },
    { name := "cout", width := 1, isOutput := true }]
  processes := #[.assign caddTarget (caddRhs N)]

/-- The process table: one assign. -/
theorem cadd_proc {N i : Nat} {p : Process2} :
    (caddDesign N).processes[i]? = some p ↔ i = 0 ∧ p = .assign caddTarget (caddRhs N) := by
  match i with
  | 0 => simp [caddDesign, eq_comm]
  | i + 1 => simp [caddDesign]

/-- The process, by index. -/
theorem cadd_proc0 (N : Nat) :
    (caddDesign N).processes[0]? = some (.assign caddTarget (caddRhs N)) :=
  cadd_proc.mpr ⟨rfl, rfl⟩

/-- `s` is `N` bits. -/
theorem cadd_declWidth_s (N : Nat) : (caddDesign N).declWidth "s" = some N := by
  simp [Design2.declWidth, caddDesign]

/-- `cout` is 1 bit. -/
theorem cadd_declWidth_cout (N : Nat) : (caddDesign N).declWidth "cout" = some 1 := by
  simp [Design2.declWidth, caddDesign]

/-- **The target's windows**, MSB-first: `cout` (1 bit), then `s` (`N` bits). -/
theorem cadd_wins (N : Nat) : caddTarget.wins (caddDesign N) = [("cout", 0, 1), ("s", 0, N)] := by
  simp [caddTarget, cadd_declWidth_s, cadd_declWidth_cout]

/-- The write windows of the design. -/
theorem cadd_writes {N i : Nat} {wn : Win} :
    (caddDesign N).Writes i wn ↔ i = 0 ∧ (wn = ("cout", 0, 1) ∨ wn = ("s", 0, N)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    obtain ⟨rfl, h⟩ := cadd_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [cadd_wins] at hw
    simpa using hw
  · rintro ⟨rfl, h⟩
    exact ⟨_, _, cadd_proc0 N, by rw [cadd_wins]; simpa using h⟩

/-- The driven signals: `cout` and `s`. -/
theorem cadd_driven {N : Nat} {n : String} : Driven (caddDesign N) n ↔ n = "cout" ∨ n = "s" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases (cadd_writes.mp h).2 with h | h <;> simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl)
    · exact ⟨0, 0, 1, cadd_writes.mpr ⟨rfl, Or.inl rfl⟩⟩
    · exact ⟨0, 0, N, cadd_writes.mpr ⟨rfl, Or.inr rfl⟩⟩

/-- **The adder is in the comb profile** (every `N`): one assign whose
concatenated target has two disjoint in-range windows on non-input signals. -/
theorem cadd_comb (N : Nat) : CombDesign (caddDesign N) where
  nodup := by simp [caddDesign]
  assign := by
    intro i p hp
    obtain ⟨rfl, rfl⟩ := cadd_proc.mp hp
    exact ⟨_, _, [("cout", 0, 1), ("s", 0, N)], rfl,
      by simp [caddTarget, cadd_declWidth_s, cadd_declWidth_cout]⟩
  inWidth := by
    intro i n lo w h
    rcases (cadd_writes.mp h).2 with h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h
    · exact ⟨_, cadd_declWidth_cout _, by omega⟩
    · exact ⟨_, cadd_declWidth_s _, by omega⟩
  notInput := by
    intro n hn
    rcases cadd_driven.mp hn with rfl | rfl <;> simp [Design2.inputNames, caddDesign]
  disjoint := by
    intro i j wi wj hij hi hj
    exact absurd ((cadd_writes.mp hi).1.trans (cadd_writes.mp hj).1.symm) hij
  selfDisjoint := by
    intro i t e hp
    obtain ⟨-, h⟩ := cadd_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rw [cadd_wins]
    simp [Win.overlaps]
  rhsFree := by
    intro i t e hp
    obtain ⟨-, h⟩ := cadd_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  rhsDeclared := by
    intro i t e hp
    obtain ⟨-, h⟩ := cadd_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.idents, caddRhs, caddDesign]
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [caddDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [caddDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The adder is acyclic**: its one process reads only the inputs, which
nothing writes (any rank works). -/
theorem cadd_acyclic (N : Nat) : Acyclic (caddDesign N) := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  exfalso
  obtain ⟨-, h⟩ := cadd_proc.mp hi
  simp only [Process2.assign.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hWj := (cadd_writes.mp ⟨tj, ej, hj, hw⟩).2
  obtain ⟨r, hr, hov⟩ := hex
  simp only [caddRhs, Expr2.reads, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rcases hWj with rfl | rfl <;>
    simp [ReadWin.overlaps] at hov

/-! ## `BitVec` arithmetic: the `N + 1`-bit sum read as `{carry, sum}` -/

/-- The `N + 1`-bit sum of the zero-extended operands does not wrap: its
value is the full sum `x + y + ci`. -/
theorem cadd_toNat {N : Nat} (x y : BitVec N) (ci : Bool) :
    (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1)).toNat =
      x.toNat + y.toNat + ci.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, Nat.pow_succ]
  generalize 2 ^ N = M at *
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := ci.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **The low `N` bits** of the `N + 1`-bit sum are the `N`-bit sum. -/
theorem cadd_low {N : Nat} (x y : BitVec N) (ci : Bool) :
    (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1)).extractLsb' 0 N =
      x + y + (BitVec.ofBool ci).setWidth N := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, cadd_toNat, Nat.shiftRight_zero]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  rw [Nat.mod_add_mod, Nat.add_mod_mod]

/-- **The top bit** of the `N + 1`-bit sum is the carry-out `2^N ≤ x + y + ci`. -/
theorem cadd_carry {N : Nat} (x y : BitVec N) (ci : Bool) :
    (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1)).getLsbD N =
      decide (2 ^ N ≤ x.toNat + y.toNat + ci.toNat) := by
  rw [← BitVec.testBit_toNat, cadd_toNat, Nat.testBit_eq_decide_div_mod_eq]
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  have hpos : 0 < 2 ^ N := Nat.two_pow_pos N
  have hn : x.toNat + y.toNat + ci.toNat < 2 * 2 ^ N := by omega
  generalize x.toNat + y.toNat + ci.toNat = n at *
  have hq : n / 2 ^ N < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr hn
  have hle : 1 ≤ n / 2 ^ N ↔ 1 * 2 ^ N ≤ n := Nat.le_div_iff_mul_le hpos
  rw [Nat.one_mul] at hle
  generalize n / 2 ^ N = q at *
  rw [decide_eq_decide]
  obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (hle.mpr h) (by decide)⟩
  · exact ⟨fun _ => hle.mp (Nat.le_refl 1), fun _ => rfl⟩

/-- The carry-out times `2^N` plus the `N`-bit sum is the full sum. -/
theorem cadd_arith {N : Nat} (x y : BitVec N) (ci : Bool) :
    (decide (2 ^ N ≤ x.toNat + y.toNat + ci.toNat)).toNat * 2 ^ N +
      (x + y + (BitVec.ofBool ci).setWidth N).toNat = x.toNat + y.toNat + ci.toNat := by
  rw [← cadd_low, BitVec.extractLsb'_toNat, cadd_toNat, Nat.shiftRight_zero]
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  generalize 2 ^ N = M at *
  by_cases h : M ≤ x.toNat + y.toNat + ci.toNat
  · rw [decide_eq_true h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.toNat_true]
    omega
  · rw [decide_eq_false h, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.toNat_false]
    omega

/-! ## The settled state -/

/-- **The adder, one settled state.** In any state that solves the design's
equations and has the comb shape, known inputs `x y : BitVec N`, `ci : Bool`
on `a b cin` give `x + y + ci` (mod `2^N`) on `s` and the carry-out
`2^N ≤ x + y + ci` on `cout`. -/
theorem cadd_settled {N : Nat} {st : SvState}
    (heqs : CombEqs (caddDesign N) st) (hs : StateShape (caddDesign N) st)
    {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
      SvState.lookup st "cout" =
        some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  -- the right-hand side, evaluated on known inputs
  have hv : evalPure2 st (caddRhs N) = .ok (LVec.ofBitVec
      (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1))) := by
    sv2_known [caddRhs, ha, hb, hc]
  -- the two parts of `{cout, s}`, read back as slices of the `N + 1`-bit value
  have htot : Win.sumWidth (caddTarget.wins (caddDesign N)) = N + 1 := by
    rw [cadd_wins]; simp; omega
  have hS := CombEqs.concat_part_ident (cadd_comb N) heqs hs (cadd_proc0 N) hv
    (n := "s") (w := N) (off := 0) (by rw [cadd_wins]; simp) (cadd_declWidth_s N)
  have hCO := CombEqs.concat_part_ident (cadd_comb N) heqs hs (cadd_proc0 N) hv
    (n := "cout") (w := 1) (off := N) (by rw [cadd_wins]; simp) (cadd_declWidth_cout N)
  rw [htot, LVec.resizeU_ofBitVec, BitVec.setWidth_eq] at hS hCO
  rw [LVec.extract_ofBitVec _ (by omega), cadd_low] at hS
  rw [LVec.extract_one_ofBitVec _ (by omega), cadd_carry] at hCO
  exact ⟨hS, hCO⟩

/-! ## The theorems -/

/-- **Non-vacuity**: for every `N`, every run of the adder completes, under
every schedule and every stimulus. -/
theorem cadd_terminates (N : Nat) : Terminates2 (caddDesign N) :=
  Terminates2.of_acyclic (cadd_comb N) (cadd_acyclic N)

/-- **Concatenated-target adder correctness** (snapshot form, every `N`): on
every snapshot of every completed run whose inputs hold known values, `s`
holds the `N`-bit sum `x + y + ci` and `cout` the carry-out — the statement
`ripple_add`'s `ripple_correct` proves of the gate-level adder. -/
theorem cadd_correct (N : Nat) :
    caddDesign N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) :=
  Models2.of_comb_pointwise (cadd_comb N) fun _ heqs hs _ _ _ ha hb hc =>
    cadd_settled heqs hs ha hb hc

/-- **Concatenated-target adder correctness** (stimulus form): whenever
cycle `c`'s stimulus entry drives `a`, `b`, `cin` with known values,
snapshot `c` carries their sum on `s` and the carry-out on `cout`. -/
theorem cadd_correct_stim (N : Nat) :
    caddDesign N ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
      stim[c]? = some inputs → tr[c]? = some st → ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup inputs "a" = some (LVec.ofBitVec x) →
        SvState.lookup inputs "b" = some (LVec.ofBitVec y) →
        SvState.lookup inputs "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  apply Models2.of_comb_inputs (cadd_comb N)
  intro stim tr h c inputs st hi hc x y ci ha hb hci
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  have hmem : ∀ n, n = "a" ∨ n = "b" ∨ n = "cin" →
      n ∈ (caddDesign N).inputNames.toList := by
    rintro n (rfl | rfl | rfl) <;> simp [Design2.inputNames, caddDesign]
  exact cadd_settled heqs hs
    (hin inputs hi "a" (hmem _ (Or.inl rfl)) _ ha)
    (hin inputs hi "b" (hmem _ (Or.inr (Or.inl rfl))) _ hb)
    (hin inputs hi "cin" (hmem _ (Or.inr (Or.inr rfl))) _ hci)

/-- **Concatenated-target adder correctness** (arithmetic form): on every
snapshot with known inputs the outputs are known, and carry-out · `2^N` +
sum is exactly `x + y + ci` as natural numbers. -/
theorem cadd_correct_nat (N : Nat) :
    caddDesign N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
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
      cadd_arith x y ci⟩) (cadd_correct N)

/-- Non-vacuity, packaged: under every schedule and stimulus a completed run
EXISTS, and it satisfies the correctness statement. -/
example (N : Nat) (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 (caddDesign N) σ stim tr ∧ ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) :=
  Models2.exists_of_terminates (cadd_terminates N) (cadd_correct N) σ stim

/-! ## Concrete runs (`N = 4`): the interpreter agrees with the theorem

`11 + 6 + 1 = 18 = 0b1_0010`; `15 + 15 + 1 = 31 = 0b1_1111`; `0 + 0 + 0`;
an `x` input bit collapses the whole arithmetic result to `x` (LRM §11.4.2),
so both parts of the concatenation read `x`. -/

private def caddStim : List SvState :=
  [[("a", .lit "1011"), ("b", .lit "0110"), ("cin", .lit "1")],
   [("a", .lit "1111"), ("b", .lit "1111"), ("cin", .lit "1")],
   [("a", .lit "0000"), ("b", .lit "0000"), ("cin", .lit "0")],
   [("a", .lit "x000"), ("b", .lit "0001"), ("cin", .lit "0")]]

private def caddView (st : SvState) : String × String :=
  (SvState.showSignal st "cout", SvState.showSignal st "s")

#guard (run2 (caddDesign 4) σ_src 64 caddStim).toOption.map (·.map caddView) ==
  some [("1", "0010"), ("1", "1111"), ("0", "0000"), ("x", "xxxx")]
#guard (run2 (caddDesign 4) σ_rev 64 caddStim).toOption.map (·.map caddView) ==
  some [("1", "0010"), ("1", "1111"), ("0", "0000"), ("x", "xxxx")]

/-! ## A nested concatenation of slices and a whole signal

`assign {y[3:2], {z, y[1:0]}} = x;` — the windows, MSB-first, are
`y[3:2]` (offset 3), `z` (offset 2), `y[1:0]` (offset 0): one process drives
two disjoint windows of `y` and all of `z`. -/

/-- The nested target `{y[3:2], {z, y[1:0]}}`. -/
def splitTarget : Lhs2 := .concat [.slice "y" 2 2, .concat [.ident "z", .slice "y" 0 2]]

/-- `assign {y[3:2], {z, y[1:0]}} = x;` with `x` 5 bits, `y` 4 bits, `z` 1 bit. -/
def splitDesign : Design2 where
  name := "split"
  decls := #[
    { name := "x", width := 5, isInput := true },
    { name := "y", width := 4, isOutput := true },
    { name := "z", width := 1, isOutput := true }]
  processes := #[.assign splitTarget (.ident "x")]

/-- The process table: one assign. -/
theorem split_proc {i : Nat} {p : Process2} :
    splitDesign.processes[i]? = some p ↔ i = 0 ∧ p = .assign splitTarget (.ident "x") := by
  match i with
  | 0 => simp [splitDesign, eq_comm]
  | i + 1 => simp [splitDesign]

/-- **The nested target's windows**, flattened MSB-first. -/
theorem split_wins : splitTarget.wins splitDesign = [("y", 2, 2), ("z", 0, 1), ("y", 0, 2)] := by
  simp [splitTarget, Design2.declWidth, splitDesign]

/-- The windows with their offsets in `x`. -/
theorem split_placed : Win.placed (splitTarget.wins splitDesign) =
    [(("y", 2, 2), 3), (("z", 0, 1), 2), (("y", 0, 2), 0)] := by
  rw [split_wins]; rfl

/-- The write windows of the design. -/
theorem split_writes {i : Nat} {wn : Win} : splitDesign.Writes i wn ↔
    i = 0 ∧ (wn = ("y", 2, 2) ∨ wn = ("z", 0, 1) ∨ wn = ("y", 0, 2)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    obtain ⟨rfl, h⟩ := split_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [split_wins] at hw
    simpa using hw
  · rintro ⟨rfl, h⟩
    exact ⟨_, _, split_proc.mpr ⟨rfl, rfl⟩, by rw [split_wins]; simpa using h⟩

/-- **The nested design is in the comb profile.** -/
theorem split_comb : CombDesign splitDesign where
  nodup := by decide
  assign := by
    intro i p hp
    obtain ⟨rfl, rfl⟩ := split_proc.mp hp
    exact ⟨_, _, [("y", 2, 2), ("z", 0, 1), ("y", 0, 2)], rfl,
      by simp [splitTarget, Design2.declWidth, splitDesign]⟩
  inWidth := by
    intro i n lo w h
    rcases (split_writes.mp h).2 with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [Design2.declWidth, splitDesign]
  notInput := by
    intro n ⟨i, lo, w, h⟩
    rcases (split_writes.mp h).2 with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -, -⟩ := h <;> simp [Design2.inputNames, splitDesign]
  disjoint := by
    intro i j wi wj hij hi hj
    exact absurd ((split_writes.mp hi).1.trans (split_writes.mp hj).1.symm) hij
  selfDisjoint := by
    intro i t e hp
    obtain ⟨-, h⟩ := split_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rw [split_wins]
    decide
  rhsFree := by
    intro i t e hp
    obtain ⟨-, h⟩ := split_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  rhsDeclared := by
    intro i t e hp
    obtain ⟨-, h⟩ := split_proc.mp hp
    simp only [Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.idents, splitDesign]
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [splitDesign] at hdc
    rcases hdc with rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [splitDesign] at hdc
    rcases hdc with rfl | rfl | rfl <;> rfl

/-- **The nested design is acyclic** (it reads only its input). -/
theorem split_acyclic : Acyclic splitDesign := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  exfalso
  obtain ⟨-, h⟩ := split_proc.mp hi
  simp only [Process2.assign.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hWj := (split_writes.mp ⟨tj, ej, hj, hw⟩).2
  obtain ⟨r, hr, hov⟩ := hex
  simp only [Expr2.reads, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rcases hWj with rfl | rfl | rfl <;> simp [ReadWin.overlaps] at hov

/-- **The nested design, one settled state**: with `x` known, `y` holds
`{x[4:3], x[1:0]}` and `z` holds `x[2]` — the MSB-first distribution. -/
theorem split_settled {st : SvState} (heqs : CombEqs splitDesign st)
    (hs : StateShape splitDesign st) {x : BitVec 5}
    (hx : SvState.lookup st "x" = some (LVec.ofBitVec x)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x.extractLsb' 3 2 ++ x.extractLsb' 0 2)) ∧
      SvState.lookup st "z" = some (LVec.ofBitVec (BitVec.ofBool (x.getLsbD 2))) := by
  have hv : evalPure2 st (.ident "x") = .ok (LVec.ofBitVec x) := evalPure2_ident_ofBitVec hx
  have hp : splitDesign.processes[0]? = some (.assign splitTarget (.ident "x")) :=
    split_proc.mpr ⟨rfl, rfl⟩
  have htot : Win.sumWidth (splitTarget.wins splitDesign) = 5 := by rw [split_wins]; rfl
  have hval : (LVec.ofBitVec x).resizeU (Win.sumWidth (splitTarget.wins splitDesign)) =
      LVec.ofBitVec x := by
    rw [htot, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  -- `z`: a whole-signal part at offset 2
  have hZ := CombEqs.concat_part_ident split_comb heqs hs hp hv (n := "z") (w := 1) (off := 2)
    (by rw [split_placed]; simp) (by simp [Design2.declWidth, splitDesign])
  rw [hval, LVec.extract_one_ofBitVec _ (by omega)] at hZ
  -- `y`: two slice parts, at offsets 3 and 0
  obtain ⟨u, hu, hhi⟩ := CombEqs.concat_part heqs hp hv (n := "y") (lo := 2) (w := 2) (off := 3)
    (by rw [split_placed]; simp)
  obtain ⟨u', hu', hlo⟩ := CombEqs.concat_part heqs hp hv (n := "y") (lo := 0) (w := 2) (off := 0)
    (by rw [split_placed]; simp)
  rw [hu] at hu'
  cases hu'
  rw [hval, LVec.extract_ofBitVec _ (by omega)] at hhi hlo
  obtain ⟨u'', hu'', hw⟩ := hs.driven "y" ⟨0, 2, 2, split_writes.mpr ⟨rfl, Or.inl rfl⟩⟩
  rw [hu] at hu''
  cases hu''
  have hw4 : u.width = 2 + 2 := by
    have : splitDesign.declWidth "y" = some 4 := by simp [Design2.declWidth, splitDesign]
    rw [this, Option.some.injEq] at hw
    omega
  exact ⟨by rw [hu, LVec.eq_ofBitVec_append_of_extract hw4 hlo hhi], hZ⟩

/-- **Non-vacuity**: every run of the nested design completes. -/
theorem split_terminates : Terminates2 splitDesign :=
  Terminates2.of_acyclic split_comb split_acyclic

/-- **Nested-concatenation correctness**: on every snapshot with `x` known,
`y = {x[4:3], x[1:0]}` and `z = x[2]`. -/
theorem split_correct : splitDesign ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState),
    tr[c]? = some st → ∀ x : BitVec 5, SvState.lookup st "x" = some (LVec.ofBitVec x) →
      SvState.lookup st "y" = some (LVec.ofBitVec (x.extractLsb' 3 2 ++ x.extractLsb' 0 2)) ∧
      SvState.lookup st "z" = some (LVec.ofBitVec (BitVec.ofBool (x.getLsbD 2))) :=
  Models2.of_comb_pointwise split_comb fun _ heqs hs _ hx => split_settled heqs hs hx

private def splitStim : List SvState :=
  [[("x", .lit "10110")], [("x", .lit "01001")], [("x", .lit "1x0z1")]]

private def splitView (st : SvState) : String × String :=
  (SvState.showSignal st "y", SvState.showSignal st "z")

-- `x = 1_0110`: y = {10, 10}, z = 1; `0_1001`: y = {01, 01}, z = 0; a plain
-- (non-arithmetic) concatenation keeps `x`/`z` bits in place.
#guard (run2 splitDesign σ_src 64 splitStim).toOption.map (·.map splitView) ==
  some [("1010", "1"), ("0101", "0"), ("1xz1", "0")]
#guard (run2 splitDesign σ_rev 64 splitStim).toOption.map (·.map splitView) ==
  some [("1010", "1"), ("0101", "0"), ("1xz1", "0")]

/-! ## Axiom pins

Standard axioms only — no `sorry`, no `native_decide`, no `bv_decide`. The
`#guard_msgs` wrappers make the build fail if any of these drifts. -/

/--
info: 'LeanModels.Sv.Comb2ConcatExample.cadd_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cadd_terminates

/--
info: 'LeanModels.Sv.Comb2ConcatExample.cadd_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cadd_correct

/--
info: 'LeanModels.Sv.Comb2ConcatExample.cadd_correct_stim' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cadd_correct_stim

/--
info: 'LeanModels.Sv.Comb2ConcatExample.cadd_correct_nat' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cadd_correct_nat

/--
info: 'LeanModels.Sv.Comb2ConcatExample.split_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms split_terminates

/--
info: 'LeanModels.Sv.Comb2ConcatExample.split_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms split_correct

end Comb2ConcatExample

end LeanModels.Sv
