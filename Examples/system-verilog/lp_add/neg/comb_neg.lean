import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombViewTactic

/-!
# Negative tests: localparams the tactics do not accept

Six one-localparam variants of a plain ripple adder (the `.sv` files and the envelopes the extractor
made from them are in this directory). The localparam is unused: it is refused by what it IS, not by
where it is read. Each refusal is a message of the tactic naming the localparam and the reason, never a
Lean elaboration error (the cases `lp_intdiv` and `lp_logic` are checker-legal designs, only outside
what the tactics read):

* `lp_clog2`  `localparam int L = $clog2(N + 1);` — not a linear function of `N` (the Sklansky and
  Kogge-Stone baselines); `paramEnv2` cannot even evaluate it at a symbolic `N`;
* `lp_divvar` `localparam integer H = N / N;` — a division by a non-literal;
* `lp_intdiv` `localparam int H = (N + 1) / 2;` — a 2-STATE `int` initialised by `/`: the elaborated
  design squashes it (`Squash2`) and wraps it at 2^31, which is false for the huge `N` a `∀ N` theorem
  quantifies over (write `localparam integer`, the 4-state twin, as `lp_add.sv` does);
* `lp_mulvar` `localparam integer Q = N * N;` — a product of two non-literals (not linear);
* `lp_shift`  `localparam integer S = N << 1;` — an operator outside `+ - *` and `/ %` by a literal;
* `lp_logic`  `localparam logic [7:0] K = 8'd3;` — a type other than `int`/`integer`.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».lp_add.neg

load_design_sv2 lp_clog2 from "Examples/system-verilog/lp_add/neg/lp_clog2.sv.json"
load_design_sv2 lp_divvar from "Examples/system-verilog/lp_add/neg/lp_divvar.sv.json"
load_design_sv2 lp_intdiv from "Examples/system-verilog/lp_add/neg/lp_intdiv.sv.json"
load_design_sv2 lp_mulvar from "Examples/system-verilog/lp_add/neg/lp_mulvar.sv.json"
load_design_sv2 lp_shift from "Examples/system-verilog/lp_add/neg/lp_shift.sv.json"
load_design_sv2 lp_logic from "Examples/system-verilog/lp_add/neg/lp_logic.sv.json"

/--
error: sv_structure: outside the supported fragment — localparam `L`: `$clog2` is outside the v1 fragment (it is not a linear function of the parameters; a localparam may use + - *, and / % by an integer literal)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_clog2.sem N) := by
  sv_structure?

/--
error: sv_structure: outside the supported fragment — localparam `H`: `/` by a non-literal is outside the v1 fragment (a localparam may divide by an integer literal)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_divvar.sem N) := by
  sv_structure?

/--
error: sv_structure: outside the supported fragment — localparam `H`: a 2-state `int` localparam initialised by `/` or `%` is squashed to 2 states and wraps at 2^31 in the elaborated design (its closed arithmetic form would be false for huge parameters); declare it `localparam integer H = …;` (outside the v1 fragment)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_intdiv.sem N) := by
  sv_structure?

/--
error: sv_structure: outside the supported fragment — localparam `Q`: a product of two non-constant factors is outside the v1 fragment (`*` needs an integer-literal factor, so that the obligations stay linear)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_mulvar.sem N) := by
  sv_structure?

/--
error: sv_structure: outside the supported fragment — localparam `S`: operator `<<` is outside the v1 fragment (a localparam may use + - *, and / % by an integer literal)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_shift.sem N) := by
  sv_structure?

/--
error: sv_structure: outside the supported fragment — localparam `K`: only `int`/`integer` (32-bit signed) localparams are in the v1 fragment
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_logic.sem N) := by
  sv_structure?

end Examples.«system-verilog».lp_add.neg
