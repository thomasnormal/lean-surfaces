import Examples.«system-verilog».comb_case.gen
import LeanModels.Sv.CombProcTactic

/-!
# A look-up table, proved (WP-G S3a)

`case_lut.sv` is a 4-entry table: constant items, constant values, a `default`. `sv_equations` states its
equation as ONE fold (`XF.caseSel`, `comb_hint.lean`); `XF.caseSel_out` turns it into the lookup in the table of
NUMBERS, and the one fact it asks for is a closed `decide`: the lookup is the function the player means
(`lut`). It is the small version of `tasks/aes_sbox/reference/sbox_table.lean` (256 items).

* `lutTbl`, `lutDflt`: the items and the default as `sv_equations?` prints them (bit 0 first);
* `lut_widths`, `lut_nat`, `lut_dflt`, `lut_correct`: the table's patterns are as wide as the subject, the table
  as numbers, the default as a number, and the lookup on every input;
* `lut_settles`: in every settled state of the lowered design whose `x` is `x`, `y` is `lut x`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_case.gen

namespace Examples.«system-verilog».comb_case.comb_proof

/-- The items of `case_lut.sv`, in source order: (pattern, value). -/
def lutTbl : List (LVec × LVec) :=
  [(⟨#[Logic.l0, Logic.l0]⟩, ⟨#[Logic.l1, Logic.l0, Logic.l0, Logic.l1]⟩),
   (⟨#[Logic.l1, Logic.l0]⟩, ⟨#[Logic.l0, Logic.l0, Logic.l1, Logic.l0]⟩),
   (⟨#[Logic.l0, Logic.l1]⟩, ⟨#[Logic.l0, Logic.l1, Logic.l1, Logic.l1]⟩)]

/-- The `default` value (`4'd1`). -/
def lutDflt : LVec := ⟨#[Logic.l1, Logic.l0, Logic.l0, Logic.l0]⟩

/-- The function the design computes. -/
def lut (x : BitVec 2) : BitVec 4 :=
  if x = 0 then 9 else if x = 1 then 4 else if x = 2 then 14 else 1

theorem lut_widths : ∀ e ∈ lutTbl, e.1.width = 2 := by decide

theorem lut_nat : XF.tblNat lutTbl = [(0, 9), (1, 4), (2, 14)] := by decide

theorem lut_dflt : lutDflt.nat = 1 := by decide

theorem lut_correct : ∀ n : Fin (2 ^ 2),
    XF.lookupNat [(0, 9), (1, 4), (2, 14)] 1 n.val = (lut (BitVec.ofFin n)).toNat := by
  decide

/-- The structure theorem of `case_lut`. -/
theorem lut_struct : ∃ d', case_lut.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **The table, proved**: in every settled state of the lowered design whose `x` is `x`, `y` is `lut x`. -/
theorem lut_settles {d' : Design2} (_hl : case_lut.sem.lowerComb = some d') (_hc : CombDesign d')
    (_ha : Acyclic d') (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st) (x : BitVec 2)
    (hx : SvState.lookup st "x" = some (LVec.ofBitVec x)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (lut x)) := by
  sv_equations
  · obtain ⟨vs, hvs, hvsw⟩ := (known_y_1 0 (by omega)).1
    exact XF.caseSel_out lutTbl lutDflt lut lut_widths (by rw [lut_dflt, lut_nat]; exact lut_correct)
      "x" "y" (fun i hi => SvState.boolAt_ofBitVec hx hi) eq_y_1 hvs hvsw
      (fun k hk => (known_y_1 k hk).2)
  case inputsKnown => exact inKnown_ofBitVec hx (by omega)

/-- info: 'Examples.«system-verilog».comb_case.comb_proof.lut_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lut_settles

end Examples.«system-verilog».comb_case.comb_proof
