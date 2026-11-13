import Examples.«system-verilog».lp_shift.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# Localparams defined by shifts, read by `sv_structure` (and, read as a value, by `sv_equations`)

At a symbolic parameter the instantiation computes a shift of an `int` localparam by deciding the sign of the amount (a
negative one shifts every bit out, 0: IEEE 1800-2023 §11.4.10, `evalIntExactRec`) and multiplies by a power of two, or,
for `>>`, divides the 32-bit pattern of the operand by one; `sv_structure` decides the sign by `omega` from the premises,
and places the value in the 32-bit range with the bounds of the power (`2 ^ (K - 1) ≤ 2 ^ 31` from `K ≤ 32`).
A premise that the value is an `int` is part of every statement: `S = N << 1` is `2 * N` only while `2 * N < 2^31`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».lp_shift.gen

namespace Examples.«system-verilog».lp_shift.comb_proof

/-- The ripple adder with an unused `S = N << 1` (the former negative fixture): a combinational design. -/
theorem lp_shl_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 1073741824) : CombDesign (lp_shift.sem N) := by
  sv_structure
  all_goals (intros; omega)

/-- `M = N << 1`, `H = M >> 1`, `Q = (N <<< 2) >>> 2` as a width and select bounds, and `P = (1 << (K - 1)) - 1` by a
parameter amount: a combinational design wherever every value is an `int`. The obligations read `Q` as the arithmetic
shift of the 32-bit value of `N <<< 2` (`canonInt 32 true (N * 4) / 4`), which `canonInt32_of_bounds` removes where
`4 * N` is an `int`. -/
theorem lp_shifts_comb (N K : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 536870912) (hK : 1 ≤ K) (hK' : K ≤ 32) :
    CombDesign (lp_shifts.sem N K) := by
  sv_structure
  -- `Q`'s value is the arithmetic shift of the 32-bit value of `N <<< 2` (`canonInt 32 true`), an `int` here
  all_goals (intros; (try simp (disch := omega) only [canonInt32_of_bounds] at *); omega)

/-- **The clean-room repro**: `BIAS = (1 << (E - 1)) - 1` read as a value in `y = x + BIAS` (its conversion marker, a
signed `int` in the unsigned context of `x`, IEEE 1800-2023 §11.8.2): a combinational design for every `1 ≤ E ≤ 32` (at
`E = 0` the negative amount and from `E = 33` on the amount 32 or more shift every bit out, where `BIAS` is -1 and the
summary's value `2^(E-1) - 1`, unbounded, is not an `int`). -/
theorem localparam_shift_comb (E : Nat) (hE : 1 ≤ E) (hE' : E ≤ 32) : CombDesign (localparam_shift.sem E) := by
  sv_structure
  all_goals (intros; omega)

theorem localparam_shift_acyclic (E : Nat) (hE : 1 ≤ E) (hE' : E ≤ 32) : Acyclic (localparam_shift.sem E) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- A signal holding the port value `z` has `XF.bv` equal to `z`. -/
theorem bv_of_lookup {N : Nat} {st : SvState} {n : String} {z : BitVec N}
    (h : SvState.lookup st n = some (LVec.ofBitVec z)) : XF.bv N (st.boolAt n) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec h hi]

/-- The sum with a constant of `M` bits, truncated back to `N ≤ M` bits, is the `N`-bit sum. -/
theorem setWidth_add_ofNat {N M : Nat} (h : N ≤ M) (x : BitVec N) (b : Nat) :
    ((x.setWidth M + BitVec.ofNat M b).setWidth N) = x + BitVec.ofNat N b := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq,
    BitVec.setWidth_ofNat_of_le h]

/-- **The clean-room repro, its equations**: `y = x + BIAS` with `BIAS = (1 << (E - 1)) - 1`, for every `1 ≤ E ≤ 32`.
`sv_equations` reads `BIAS` as a value (`Sk.zc`): the 32-bit `int`, materialized at the 32-bit width of the sum (the sum
of an `E`-bit `x` and an `int` is 32 bits wide, IEEE 1800-2023 §11.6.1) and truncated to `y`'s `E` bits; the summary's
value of `BIAS` is `2^(E-1) - 1` (`(E - 1) % 2^32` is `E - 1`), also at `E = 32`, where the instantiation wraps `1 << 31`
to `-2^31` and the difference back to `2^31 - 1`. -/
theorem localparam_shift_correct (E : Nat) (hE : 1 ≤ E) (hE' : E ≤ 32) :
    localparam_shift.sem E ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec E), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x + BitVec.ofNat E (2 ^ (E - 1) - 1))) := by
  have hc := localparam_shift_comb E hE hE'
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  have ha := localparam_shift_acyclic E hE hE'
  sv_equations
  · have eW : ((↑E : Int) + -1).natAbs + 1 = E := by omega
    have eM : max E 32 = 32 := by omega
    have eB : (2 : Int) ^ (((E : Int) - 1) % 4294967296).toNat - 1 = ((2 ^ (E - 1) - 1 : Nat) : Int) := by
      have e1 : ((E : Int) - 1) % 4294967296 = ((E - 1 : Nat) : Int) := by omega
      have h2 : 1 ≤ 2 ^ (E - 1) := Nat.one_le_two_pow
      have e3 : ((2 ^ (E - 1) - 1 : Nat) : Int) = ((2 ^ (E - 1) : Nat) : Int) - 1 := by omega
      rw [e1, Int.toNat_natCast, e3, Int.natCast_pow]
      rfl
    rw [eW] at eq_y_plain_0 known_y_plain_0
    rw [eM] at eq_y_plain_0
    have ey : ∀ k, k < E → st.boolAt "y" k =
        XF.zext 32 (fun x => XF.addBits 32 (fun x => XF.zext E (fun k => st.boolAt "x" k) x) 32
          (fun x => XF.constBit ((2 ^ (E - 1) - 1 : Nat) : Int) 32 x) x) k := fun k hk => by
      rw [eq_y_plain_0 k hk, if_neg (by omega), eB]
    obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_0 0 (by omega)
    rw [SvState.lookup_eq_ofBitVec_bv hvy hvyw (fun k hk => (known_y_plain_0 k hk).2)] at hvy
    rw [hvy]
    congr 1
    rw [XF.bv_congr_lt ey, XF.bv_zext_trunc (n := 32) (m := E) _ hE', XF.bv_addBits (fun k _ => rfl),
      XF.bv_zext (n := E) (m := 32) _ hE', bv_of_lookup hA, XF.bv_constBit, BitVec.ofInt_natCast]
    exact congrArg LVec.ofBitVec (setWidth_add_ofNat hE' x _)
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- info: 'Examples.«system-verilog».lp_shift.comb_proof.localparam_shift_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localparam_shift_correct

/-- info: 'Examples.«system-verilog».lp_shift.comb_proof.localparam_shift_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localparam_shift_comb

/-- info: 'Examples.«system-verilog».lp_shift.comb_proof.lp_shifts_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_shifts_comb

end Examples.«system-verilog».lp_shift.comb_proof
