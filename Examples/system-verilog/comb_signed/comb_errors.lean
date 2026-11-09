import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.CombProcTactic

/-!
# Signed reads: what stays refused, and why

The tactics read a signed signal as the same bits wherever it is a whole operand of a continuous assign
(`comb_proof.lean`). The constructs whose meaning signedness changes are refused, each with its reason:

* `neg/sg_cmp.sv`: a signed comparison `a < b` (the operands compare as two's-complement integers);
* `neg/sg_asr.sv`: an arithmetic shift right `a >>> 1` (it fills with the sign bit);
* `neg/sg_sel.sv`: a select of a signed signal `a[W-1]` (read through the unsigned twin only as a whole operand).
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_signed.comb_errors

load_design_sv2 sg_cmp from "Examples/system-verilog/comb_signed/neg/sg_cmp.sv.json"
load_design_sv2 sg_asr from "Examples/system-verilog/comb_signed/neg/sg_asr.sv.json"
load_design_sv2 sg_sel from "Examples/system-verilog/comb_signed/neg/sg_sel.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison (`<`, `<=`, `>`, `>=` of signed operands: the operands are ordered as two's-complement integers, which the fragment does not model; it has the unsigned comparisons)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_cmp.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an arithmetic shift right `>>>` (it fills with the sign bit of a signed operand, which the fragment does not model; it has the logical shifts `<<` and unsigned `>>`)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_asr.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a select of the signed signal `a` (outside the v1 fragment: the tactics read a signed signal through its unsigned twin only as a whole operand)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_sel.sem W) := by
  sv_structure

end Examples.«system-verilog».comb_signed.comb_errors
