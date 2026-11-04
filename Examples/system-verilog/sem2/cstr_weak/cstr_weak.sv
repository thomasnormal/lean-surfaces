// SPDX-License-Identifier: Apache-2.0
// A drive strength with no high-impedance term on a continuous assignment to a variable: `(weak0, weak1)` on the only
// driver of `y` gives y = a in Icarus 12, Xcelium 24.03 (`*W,CAVSTR`, ignored) and Verilator 5.042, but Yosys 0.53
// cannot read a strength on `assign` (syntax error), so there is no scored netlist. Refused all the same
// (`ContinuousAssignSymbol:strength`, P-SAME-PROGRAM): the rule is the syntactic one, not a case analysis of the
// strength pair (nothing in the surveyed corpora writes one).
module cstr_weak (
  input  logic [1:0] a,
  output logic [1:0] y
);
  assign (weak0, weak1) y = a;
endmodule
