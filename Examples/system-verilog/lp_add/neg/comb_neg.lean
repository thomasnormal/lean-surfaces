import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombViewTactic

/-!
# Negative tests: localparams the tactics do not accept

One-localparam variants of a plain ripple adder (the `.sv` files and the envelopes the extractor
made from them are in this directory; a fifth, `S = N << 1`, is read since the localparams have the shifts
of an `int`, and is now `lp_shift/lp_shl.sv`). The localparam is unused: it is refused by what it IS, not by
where it is read. Each refusal is a message of the tactic naming the localparam and the reason, never a
Lean elaboration error (the case `lp_logic` is a checker-legal design, only outside
what the tactics read):

* `lp_divvar` `localparam integer H = N / N;` — a division by a non-literal;
* `lp_intdiv` `localparam int H = (N + 1) / 2;` — a 2-STATE `int` initialised by `/`: the elaborated
  design squashes it (`Squash2`). It is READ now (no longer a negative case): the instantiation evaluates the squashed
  INT-class operand exactly as it evaluates an `integer`'s (`evalIntTarget`), both wrap at 2^31, and the summary's
  agreement with it (`hag`) is checked under the range premise, as for `lp_add.sv` (`lp_intdiv_comb` below);
* `lp_mulvar` `localparam integer Q = N * N;` — a product of two non-literals (not linear);
* `lp_logic`  `localparam logic [7:0] K = 8'd3;` — a type other than `int`/`integer`.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».lp_add.neg

load_design_sv2 lp_divvar from "Examples/system-verilog/lp_add/neg/lp_divvar.sv.json"
load_design_sv2 lp_intdiv from "Examples/system-verilog/lp_add/neg/lp_intdiv.sv.json"
load_design_sv2 lp_mulvar from "Examples/system-verilog/lp_add/neg/lp_mulvar.sv.json"
load_design_sv2 lp_logic from "Examples/system-verilog/lp_add/neg/lp_logic.sv.json"

/--
error: sv_structure: outside the supported fragment — localparam `H`: `/` by a non-literal is outside the v1 fragment (a localparam may divide by an integer literal)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_divvar.sem N) := by
  sv_structure?

/-- The squashed 2-state `int` `H = (N + 1) / 2` is read through its operand (the range premise keeps `N + 1` an `int`). -/
theorem lp_intdiv_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (lp_intdiv.sem N) := by
  sv_structure
  all_goals (intros; omega)

/--
error: sv_structure: outside the supported fragment — localparam `Q`: a product of two non-constant factors is outside the v1 fragment (`*` needs an integer-literal factor, so that the obligations stay linear)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_mulvar.sem N) := by
  sv_structure?

/--
error: sv_structure: outside the supported fragment — localparam `K`: only `int`/`integer` (32-bit signed) localparams are in the v1 fragment
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_logic.sem N) := by
  sv_structure?

end Examples.«system-verilog».lp_add.neg
