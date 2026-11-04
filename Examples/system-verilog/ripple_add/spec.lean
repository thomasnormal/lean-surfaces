/-
Examples/system-verilog/ripple_add — the three-file example layout (SV lane,
the Design2 proof layer's acceptance example):

  ripple_add.sv      — the design (`N`-bit ripple-carry adder: `c[0] = cin`,
                       one `generate for` over the bit index for the sum and
                       carry cells, `cout = c[N]`)
  ripple_add.sv.json — generated envelope (extractors/sv/extract.py)
  gen.lean           — `load_design_sv2 ripple_add`, and the instantiated
                       design at SYMBOLIC `N` (process list and declarations)
  spec.lean          — THIS FILE: concrete `run2` rows (non-vacuity), and the
                       theorem STATEMENTS, each proved `:= by proofs`
  proof.lean         — the real proofs (namespace
                       `Examples.«system-verilog».ripple_add.proof`)

`proofs` (LeanModels/Python/Surface.lean — the tactic is lane-agnostic)
resolves each declaration's name against the sibling proof module; the
statement duplication between spec and proof is BY DESIGN and typechecked by
the `:= by proofs` reference. The design constant is `gen.lean`'s
`ripple_add` (one `load_design_sv2`, shared by both files), so there is no
envelope-certification step here: the constant IS the envelope, read at
elaboration time.

The theorems hold for EVERY width `N ≥ 1` (no unrolling at a fixed width, no
bit-blasting); the `#guard` rows below exercise the default `N = 4`.
-/
import Examples.«system-verilog».ripple_add.proof
import LeanModels.Python.Surface
import LeanModels.Sv.Mono2
-- Not used below: imported so that the `Examples` build (which does not go
-- through the `LeanModels` umbrella) also checks the layer's worked full adder
-- and its axiom pins.
import LeanModels.Sv.Comb2Example

open LeanModels.Sv
open Examples.«system-verilog».ripple_add.gen

/-! ## Non-vacuity: concrete runs at `N = 4`

`run2` of the instantiated family member `ripple_add.sem 4` under the
source-order schedule `σ_src` (and the reversed schedule `σ_rev`), fuel 64;
one stimulus entry, one snapshot. Rows show `(s, cout)` as binary strings,
MSB first. -/

/-- One stimulus entry driving `a`, `b`, `cin` from literal strings. -/
private def rippleStim (a b ci : String) : List SvState :=
  [[("a", LVec.lit a), ("b", LVec.lit b), ("cin", LVec.lit ci)]]

/-- The outputs of a snapshot: `(s, cout)`. -/
private def rippleView (st : SvState) : String × String :=
  (SvState.showSignal st "s", SvState.showSignal st "cout")

-- (a) 11 + 6 + 1 = 18 = 16 + 2: s = 0010, carry-out 1.
#guard (run2 (ripple_add.sem 4) σ_src 64 (rippleStim "1011" "0110" "1")).toOption.map
    (·.map rippleView) == some [("0010", "1")]

-- (b) 15 + 1 + 0 = 16: the carry ripples through all four cells.
#guard (run2 (ripple_add.sem 4) σ_src 64 (rippleStim "1111" "0001" "0")).toOption.map
    (·.map rippleView) == some [("0000", "1")]

-- (c) 4-state, bit-precise: a = 1x00. The `x` in bit 2 reaches only s[2]
-- (`x ^ 0 ^ 0`); its carry is `(x & 0) | (0 & (x ^ 0)) = 0`, so bit 3 and the
-- carry-out stay known. Contrast the `adder` example, whose single `+`
-- x-collapses the WHOLE result (LRM §11.4.3): a gate-level adder does not.
#guard (run2 (ripple_add.sem 4) σ_src 64 (rippleStim "1x00" "0001" "0")).toOption.map
    (·.map rippleView) == some [("1x01", "0")]

-- (c') `x` THROUGH the carry chain: a = 01x1, b = 0011. c[2] = x | (x ^ 1) = x
-- poisons s[1..3], but bit 3's carry `(0 & 0) | (x & (0 ^ 0)) = 0` is known.
#guard (run2 (ripple_add.sem 4) σ_src 64 (rippleStim "01x1" "0011" "0")).toOption.map
    (·.map rippleView) == some [("xxx0", "0")]

-- With no stimulus the inputs stay `x` from startup: every output bit is `x`.
#guard (run2 (ripple_add.sem 4) σ_src 64 [[]]).toOption.map (·.map rippleView) ==
  some [("xxxx", "x")]

-- Two cycles, the second driving only `b`: `a` and `cin` hold (12 + 5 + 1 = 18).
#guard (run2 (ripple_add.sem 4) σ_src 64
    (rippleStim "1100" "0011" "1" ++ [[("b", LVec.lit "0101")]])).toOption.map
    (·.map rippleView) == some [("0000", "1"), ("0010", "1")]

/-! ### Stimulus conventions (`Spec2.lean`, "Stimulus conventions")

`applyInputs2` stores an entry's value verbatim and reads only declared
inputs. These rows pin both conventions on the real design; they are why the
theorems below quantify over `x : BitVec N` at the declared width. -/

-- A 2-bit value on the 4-bit port `a` is NOT zero-extended: `a` holds `11`, the
-- reads `a[2]`, `a[3]` are out of range (`x`), so `s = xx00` and `cout = x`
-- (SV port assignment would give 3 + 1 = 4: `s = 0100`, `cout = 0`).
#guard (run2 (ripple_add.sem 4) σ_src 64
    [[("a", LVec.ofNat 2 3), ("b", LVec.lit "0001"), ("cin", LVec.lit "0")]]).toOption.map
    (·.map rippleView) == some [("xx00", "x")]

-- A key that names no input is ignored: the misspelled `"A"` leaves `a` at `x`.
#guard (run2 (ripple_add.sem 4) σ_src 64
    [[("A", LVec.lit "0011"), ("b", LVec.lit "0001"), ("cin", LVec.lit "0")]]).toOption.map
    (·.map rippleView) == some [("xxxx", "x")]

-- An entry for the OUTPUT `s` is ignored too: the design computes 3 + 1 = 4.
#guard (run2 (ripple_add.sem 4) σ_src 64
    [[("a", LVec.lit "0011"), ("b", LVec.lit "0001"), ("cin", LVec.lit "0"),
      ("s", LVec.lit "1111")]]).toOption.map (·.map rippleView) == some [("0100", "0")]

/-- Every known input combination at width `N` under schedule `σ`: the run
completes with one snapshot whose `s` is `(a + b + ci) mod 2^N` and whose
`cout` is `(a + b + ci) / 2^N`, compared against `Nat` arithmetic. Evaluated
by the compiler (a TEST, not a proof — the proof is `ripple_correct`). -/
private def rippleExhaustive (σ : ScheduleOracle) (N : Nat) : Bool :=
  (List.range (2 ^ (2 * N + 1))).all fun k =>
    let a := k % 2 ^ N
    let b := k / 2 ^ N % 2 ^ N
    let ci := k / 2 ^ (2 * N)
    match run2 (ripple_add.sem N) σ 64
        [[("a", LVec.ofNat N a), ("b", LVec.ofNat N b), ("cin", LVec.ofNat 1 ci)]] with
    | .ok [st] =>
        SvState.lookup st "s" == some (LVec.ofNat N ((a + b + ci) % 2 ^ N)) &&
          SvState.lookup st "cout" == some (LVec.ofNat 1 ((a + b + ci) / 2 ^ N))
    | _ => false

-- (d) EXHAUSTIVE at N = 4: all 2^9 = 512 input combinations, both schedules.
#guard rippleExhaustive σ_src 4
#guard rippleExhaustive σ_rev 4
-- … and every smaller width, N = 1, 2, 3.
#guard [1, 2, 3].all (rippleExhaustive σ_src)

/-! ## The theorems (every `N ≥ 1`) -/

/-- **Non-vacuity**: every run of the ripple adder completes, under every
schedule and every stimulus. -/
theorem ripple_terminates (N : Nat) (hN : 1 ≤ N) : Terminates2 (ripple_add.sem N) := by
  proofs

/-- **Ripple-adder correctness** (snapshot form): on every snapshot of every
completed run whose inputs hold known values `x y : BitVec N`, `ci : Bool`,
`s` holds the `N`-bit sum `x + y + ci` and `cout` the carry-out
`2^N ≤ x + y + ci`. -/
theorem ripple_correct (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  proofs

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
  proofs

/-- **Ripple-adder correctness** (arithmetic form): on every snapshot with
known inputs the outputs are known, and carry-out · `2^N` + sum is exactly
`x + y + ci` as natural numbers. -/
theorem ripple_correct_nat (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        ∃ (sv : BitVec N) (co : Bool),
          SvState.lookup st "s" = some (LVec.ofBitVec sv) ∧
          SvState.lookup st "cout" = some (LVec.ofBitVec (BitVec.ofBool co)) ∧
          co.toNat * 2 ^ N + sv.toNat = x.toNat + y.toNat + ci.toNat := by
  proofs

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

/-- Non-vacuity with uniqueness (`Terminates2.existsUnique`, `Mono2.lean`):
under every schedule and stimulus there is EXACTLY one completed run, so the
trace that `ripple_correct` describes is THE trace. -/
example (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 (ripple_add.sem N) σ stim tr ∧
      ∀ tr', Runs2 (ripple_add.sem N) σ stim tr' → tr' = tr :=
  Terminates2.existsUnique (ripple_terminates N hN) σ stim

/-! ## Axiom pins (no `sorry`, no `native_decide`, no `bv_decide`: standard
axioms only) -/

/-- info: 'ripple_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ripple_terminates

/-- info: 'ripple_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ripple_correct

/-- info: 'ripple_correct_stim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ripple_correct_stim

/-- info: 'ripple_correct_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ripple_correct_nat
