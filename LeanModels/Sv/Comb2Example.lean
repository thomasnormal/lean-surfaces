import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2

/-!
# The combinational settle theorem, end to end: a full adder (`LeanModels.Sv` — Design2)

A worked example of the whole comb pipeline (`Comb2Base` → `Comb2Sound` /
`Comb2Term` → `Comb2`) on `Comb2Base`'s hand-built full adder
`Comb2Smoke.faDesign`

    s  = a ^ b ^ ci
    co = (a & b) | (ci & (a ^ b))
    y[1] = co          (slice target)
    y[0] = s           (constant-index target)

proving, for EVERY schedule, every stimulus, and every completed run:

1. `fa_terminates : Terminates2 faDesign` — every run completes
   (`Terminates2.of_acyclic` on the profile `fa_comb` and the rank
   certificate `fa_acyclic`);
2. `fa_correct` — on every snapshot whose inputs hold known 1-bit values
   `x y z`, `s` holds `x ^^^ y ^^^ z`, `co` holds the MAJORITY
   `x &&& y ||| x &&& z ||| y &&& z`, and the bus `y` holds `co ++ s`;
3. `fa_correct_stim` — the same stated against the STIMULUS: whenever cycle
   `c`'s stimulus entry drives `a`, `b`, `ci` with known values, snapshot `c`
   carries the sum and the majority.

## The proof pattern (what a challenge proof looks like)

* `Models2.of_comb_pointwise` / `Models2.of_comb_inputs` (`Comb2.lean`)
  reduce the `⊨₂` goal to ONE state that solves the design's equations
  (`CombEqs`) and has the comb shape (`StateShape`) — no run, no fuel, no
  schedule.
* `CombEqs.lookup_ident` / `extract_slice` / `extract_index` read one
  process's equation back as a fact about the target signal, given the
  right-hand side's `evalPure2` value.
* The `evalPure2` value of a gate-level right-hand side over known inputs is
  computed by `sv2_known` (`Known2.lean`): `ofBitVec` of a `BitVec` term.
* What remains is `BitVec` algebra (`maj_gate`: the carry gate IS the
  majority, at every width, bit by bit through `Bool` case analysis) and the
  per-bit window conclusion `LVec.eq_ofBitVec_of_extract_one` for the bus.

No `decide` over input values, no `bv_decide`, no `native_decide`: the
theorems are about symbolic `x y z`.
-/

namespace LeanModels.Sv

namespace Comb2Example

open Comb2Smoke

/-! ## `BitVec` algebra -/

/-- **The carry gate is the majority function** (every width, bit by bit). -/
theorem maj_gate {w : Nat} (x y z : BitVec w) :
    x &&& y ||| z &&& (x ^^^ y) = x &&& y ||| x &&& z ||| y &&& z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem ofBool_getLsbD_zero (x : BitVec 1) : BitVec.ofBool (x.getLsbD 0) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-! ## The settled values -/

/-- Declared widths of the driven signals. -/
theorem fa_declWidth_s : faDesign.declWidth "s" = some 1 := by
  simp [Design2.declWidth, faDesign]

/-- (see `fa_declWidth_s`) -/
theorem fa_declWidth_co : faDesign.declWidth "co" = some 1 := by
  simp [Design2.declWidth, faDesign]

/-- (see `fa_declWidth_s`) -/
theorem fa_declWidth_y : faDesign.declWidth "y" = some 2 := by
  simp [Design2.declWidth, faDesign]

/-- **The full adder, one settled state.** In any state that solves the
full adder's equations and has the comb shape, known 1-bit inputs `x y z` on
`a b ci` give the sum on `s`, the majority on `co`, and `co ++ s` on the bus
`y`. -/
theorem fa_settled {st : SvState} (heqs : CombEqs faDesign st) (hs : StateShape faDesign st)
    {x y z : BitVec 1}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "ci" = some (LVec.ofBitVec z)) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
      SvState.lookup st "co" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) ∧
      SvState.lookup st "y" =
        some (LVec.ofBitVec ((x &&& y ||| x &&& z ||| y &&& z) ++ (x ^^^ y ^^^ z))) := by
  -- the two gates, evaluated on known inputs
  have hsum : evalPure2 st (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "ci")) =
      .ok (LVec.ofBitVec (x ^^^ y ^^^ z)) := by
    sv2_known [ha, hb, hc]
  have hcar : evalPure2 st (.binary .or (.binary .and (.ident "a") (.ident "b"))
      (.binary .and (.ident "ci") (.binary .xor (.ident "a") (.ident "b")))) =
      .ok (LVec.ofBitVec (x &&& y ||| z &&& (x ^^^ y))) := by
    sv2_known [ha, hb, hc]
  -- processes 0 and 1: whole-signal targets
  have hS : SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) := by
    rw [CombEqs.lookup_ident fa_comb heqs hs (i := 0) rfl hsum fa_declWidth_s]
    simp
  have hCO : SvState.lookup st "co" =
      some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) := by
    rw [CombEqs.lookup_ident fa_comb heqs hs (i := 1) rfl hcar fa_declWidth_co, maj_gate]
    simp
  refine ⟨hS, hCO, ?_⟩
  -- processes 2 and 3: the two 1-bit windows of the bus
  obtain ⟨u, hu, hu1⟩ := CombEqs.extract_slice heqs (i := 2) rfl
    (evalPure2_ident_ofBitVec hCO)
  obtain ⟨u', hu', hu0⟩ := CombEqs.extract_index heqs (i := 3) (k := 0) rfl
    (by rw [LVec.toNat?_ofNat]) (evalPure2_ident_ofBitVec hS)
  rw [hu] at hu'
  cases hu'
  obtain ⟨u'', hu'', hw⟩ := hs.driven "y" (fa_driven.mpr (by simp))
  rw [hu] at hu''
  cases hu''
  rw [fa_declWidth_y, Option.some.injEq] at hw
  rw [hu, Option.some.injEq]
  apply LVec.eq_ofBitVec_of_extract_one hw.symm
  intro i hi
  match i, hi with
  | 0, _ =>
      rw [Nat.zero_mul] at hu0
      rw [hu0, BitVec.getLsbD_append, if_pos Nat.zero_lt_one, ofBool_getLsbD_zero,
        LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  | 1, _ =>
      rw [hu1, BitVec.getLsbD_append, if_neg (Nat.lt_irrefl 1), Nat.sub_self,
        ofBool_getLsbD_zero, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

/-! ## The theorems -/

/-- **Non-vacuity**: every run of the full adder completes, under every
schedule and every stimulus. -/
theorem fa_terminates : Terminates2 faDesign :=
  Terminates2.of_acyclic fa_comb fa_acyclic

/-- **Full-adder correctness** (snapshot form): on every snapshot of every
completed run whose inputs hold known 1-bit values `x y z`, the sum output
holds `x ^^^ y ^^^ z`, the carry output holds the majority of `x y z`, and the
bus holds `carry ++ sum`. -/
theorem fa_correct : faDesign ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState),
    tr[c]? = some st → ∀ x y z : BitVec 1,
      SvState.lookup st "a" = some (LVec.ofBitVec x) →
      SvState.lookup st "b" = some (LVec.ofBitVec y) →
      SvState.lookup st "ci" = some (LVec.ofBitVec z) →
      SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
      SvState.lookup st "co" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) ∧
      SvState.lookup st "y" =
        some (LVec.ofBitVec ((x &&& y ||| x &&& z ||| y &&& z) ++ (x ^^^ y ^^^ z))) :=
  Models2.of_comb_pointwise fa_comb fun _ heqs hs _ _ _ ha hb hc => fa_settled heqs hs ha hb hc

/-- **Full-adder correctness** (stimulus form): whenever cycle `c`'s stimulus
entry drives `a`, `b`, `ci` with known 1-bit values `x y z`, snapshot `c`
carries their sum on `s` and their majority on `co`. -/
theorem fa_correct_stim : faDesign ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
    stim[c]? = some inputs → tr[c]? = some st → ∀ x y z : BitVec 1,
      SvState.lookup inputs "a" = some (LVec.ofBitVec x) →
      SvState.lookup inputs "b" = some (LVec.ofBitVec y) →
      SvState.lookup inputs "ci" = some (LVec.ofBitVec z) →
      SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
      SvState.lookup st "co" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) := by
  apply Models2.of_comb_inputs fa_comb
  intro stim tr h c inputs st hi hc x y z ha hb hci
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  have hmem : ∀ n, n = "a" ∨ n = "b" ∨ n = "ci" → n ∈ faDesign.inputNames.toList := by
    rintro n (rfl | rfl | rfl) <;> simp [Design2.inputNames, faDesign]
  obtain ⟨hS, hCO, -⟩ := fa_settled heqs hs
    (hin inputs hi "a" (hmem _ (by simp)) _ ha)
    (hin inputs hi "b" (hmem _ (by simp)) _ hb)
    (hin inputs hi "ci" (hmem _ (by simp)) _ hci)
  exact ⟨hS, hCO⟩

/-- Non-vacuity, packaged: under every schedule and stimulus a completed run
EXISTS, and it satisfies the correctness statement. -/
example (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 faDesign σ stim tr ∧ ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ x y z : BitVec 1,
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "ci" = some (LVec.ofBitVec z) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
        SvState.lookup st "co" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) ∧
        SvState.lookup st "y" =
          some (LVec.ofBitVec ((x &&& y ||| x &&& z ||| y &&& z) ++ (x ^^^ y ^^^ z))) :=
  Models2.exists_of_terminates fa_terminates fa_correct σ stim

/-! ## Axiom pins

Standard axioms only — no `sorry`, no `native_decide`, no `bv_decide`. The
`#guard_msgs` wrappers make the build fail if any of these drifts. -/

/--
info: 'LeanModels.Sv.Comb2Example.fa_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fa_terminates

/--
info: 'LeanModels.Sv.Comb2Example.fa_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fa_correct

/--
info: 'LeanModels.Sv.Comb2Example.fa_correct_stim' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fa_correct_stim

/--
info: 'LeanModels.Sv.Comb2Example.fa_settled' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fa_settled

/--
info: 'LeanModels.Sv.Comb2Example.maj_gate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs in
#print axioms maj_gate

end Comb2Example

end LeanModels.Sv
