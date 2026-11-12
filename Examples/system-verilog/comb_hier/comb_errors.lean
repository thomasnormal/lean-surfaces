import Examples.«system-verilog».comb_hier.gen
import LeanModels.Sv.CombProcTactic

/-!
# Module instances the hierarchy summary does not read, and why

The tactics read a design whose instances are all at module level through its flat twin (`comb_proof.lean`). The shapes
v1 does not read are refused, each with its reason:

* `neg/gen_loop.sv`: an instance inside a generate loop (one instance per iteration would make the child's sites a generate
  family whose names carry the loop index, which the summary does not build yet);
* `neg/odd_split.sv`: the halves at an odd width, the low half `(W+1)/2` bits wide. The bounds read a quotient of a SUM,
  `(W+1)/2`; the affine forms the summary reads hold a quotient of ONE named constant by a positive literal (`W/2`,
  `hier_param.sv`), so the connection's window is refused, and the refusal says so. (The halves with `wire` ports, pinned
  here before, are now read: `wire_out.sv`, `hier_param.sv`.)
* `hier_param.sv` (the clean-room repro, read at every EVEN width in `comb_proof.lean`) at an ODD width `W = 2K+1`: `W/2`
  is `K`, so the instance `hi` has a `K`-bit port while its windows `a[W-1:W/2]` and `y[W-1:W/2]` are `K+1` bits: the
  input actual is truncated to the port and the output port zero-extended into its window (Icarus 12 warns "Port 2 (y) of
  leaf expects 3 bits, got 4. Padding" at `W = 7` and gives `y = {1'b0, a[W-2:0]}`). The flat twin reads a connection only
  at the port's own width (`conn_in_eq`, `conn_out_eq`), so its width obligation is false at every odd width;
  `sv_structure` samples it and names the connection. The next wall is ours (`CombHier.lean`): a twin site for a
  width-changing connection, the lowering `connProcs` gives it (`fitExpr2`, `portOut`: the port read at its own width, then
  zero-extended or truncated, the shape `Sk.fit` has inside a shift operand), with its shape theorem and the per-site
  obligations of a top-level `Sk.fit`.
* `neg/hier_param_utf8.sv`: `hier_param.sv` byte for byte below a header with one non-ASCII character. The extractor
  keeps the parent's `wire` output as the loud member `PortSymbol:net-z` instead of a net-as-variable: it compares the
  driver's text sliced from the DECODED source with slang's BYTE offsets, so the character shifts the slice (ls-sv's
  `lower_proc.py`, `net_driver_reason`; reported). The refusal names that cause.
* `neg/signed_port_wide.sv`: a whole signed 4-bit input connected to an 8-bit port. The connection sign-extends the
  actual (IEEE 1800-2023 §23.3.3, §10.7, §11.8.2; the envelope marks it `SignedResize`, and local Icarus 12.0 pads the
  port's high bits with the sign: `x = 4'b1010` gives `y = 11111010`). The twin reads a signed actual through its unsigned
  twin only where it is exactly as wide as its port, so this connection stays refused. (A select of a signed input as an
  actual, the clean-room repros `sel_signed.sv` and `part_signed.sv`, was refused here as "a select of the signed signal
  `x` in a position the tactics do not read through the unsigned twin"; both are now proved, `comb_proof.lean`.)
* `neg/signed_child.sv`: a select of a signed signal inside the instantiated child: the child's own processes are read as
  a flat design without signed reads, so the child is refused with that reason.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_hier.comb_errors

load_design_sv2 gen_loop from "Examples/system-verilog/comb_hier/neg/gen_loop.sv.json"
load_design_sv2 odd_split from "Examples/system-verilog/comb_hier/neg/odd_split.sv.json"
load_design_sv2 hier_param_utf8 from "Examples/system-verilog/comb_hier/neg/hier_param_utf8.sv.json"
load_design_sv2 signed_port_wide from "Examples/system-verilog/comb_hier/neg/signed_port_wide.sv.json"
load_design_sv2 signed_child from "Examples/system-verilog/comb_hier/neg/signed_child.sv.json"

/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (gen_loop.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a bound of `a[hi:lo]` is not affine (dynamic or nonlinear) — it holds a quotient the affine forms do not read: a quotient is read only as `n / d`, one named constant `n` (a parameter, a localparam or a genvar) divided by a positive literal `d` (in the flat twin of this design: instance `lo`, the connection of port `a`)
-/
#guard_msgs (whitespace := lax) in
example (K : Nat) (hK : 1 ≤ K) (hR : (2 * K + 1 : Int) < 2147483648) : CombDesign (odd_split.sem (2 * K + 1)) := by
  sv_structure

-- `hier_param.sv` at an odd width: the instance `hi`'s connections change width.
/--
error: sv_structure: the flat twin's width obligation fails at site `plain#3` (instance `hi`, the connection of port `a`): the actual is 2 bits wide and the port 1 bit. The hierarchy summary reads a port connection whose actual (an input) or target (an output) is exactly as wide as the port; a connection that changes width, an input actual truncated to the port or an output port zero-extended into a wider target (IEEE 1800-2023 §23.3.3, §10.7), is outside it (sampled at [W] = [3]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
example (K : Nat) (hK : 1 ≤ K) (hR : (2 * K + 1 : Int) < 2147483648) :
    CombDesign (gen.hier_param.sem (2 * K + 1)) := by
  sv_structure

-- One non-ASCII character in a comment: the extractor keeps `y` loud.
/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: the module has a member outside the semantic tier (`PortSymbol:net-z`: y), which the instantiation keeps as a loud process (`PortSymbol:net-z` is the extractor's refusal of a `wire` port it did not read as one driven variable; it reads a `wire` output driven by continuous assignments, or by instance output ports that tile it at the default point, as a net-as-variable, and `y` has such a driver here. A known cause: a non-ASCII character in the source above the driver — the extractor compares the driver's text sliced from the DECODED source with slang's BYTE offsets (ls-sv's `lower_proc.py`, `net_driver_reason`), so the character shifts the slice)
-/
#guard_msgs (whitespace := lax) in
example (K : Nat) (hK : 1 ≤ K) (hR : (2 * K : Int) < 2147483648) : CombDesign (hier_param_utf8.sem (2 * K)) := by
  sv_structure

-- A whole signed input into a wider port: the connection sign-extends the actual (`SignedResize`), refused.
/--
error: sv_structure: outside the supported fragment — site `plain#0`: sign extension (a signed operand narrower than its context is extended with its sign bit, IEEE 1800-2023 §11.8.2, and the envelope marks it `SignedResize`; the fragment reads that marker as an operand of a signed comparison or inside the left operand of a shift, not here) (in the flat twin of this design: instance `leaf`, the connection of port `a`)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign signed_port_wide.sem := by
  sv_structure

-- A select of a signed signal inside the child: the child is refused.
/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: instance `leaf`: module `signed_child_leaf` is outside the supported fragment — site `plain#0`: a select of the signed signal `a` in a position the tactics do not read through the unsigned twin (they read a select of a signed signal, an unsigned value, IEEE 1800-2023 §11.8.1, where it is an operand of a continuous assign, the actual of a module's input port or the left operand of a shift; an index, a shift amount and an `always_comb` body are outside the fragment)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign signed_child.sem := by
  sv_structure

end Examples.«system-verilog».comb_hier.comb_errors
