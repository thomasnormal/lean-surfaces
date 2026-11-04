// Round 7 folds (round 6 FOLDS verifier major 4, repro `vw_sqd`): a 2-state
// target narrower than its initializer at the default point (N = 32) over a
// division whose divisor wraps to 0 at the operand's OWN width. At N = 4,
// U = 15 the round 5 model evaluated `4'd8 / (U + 1'b1)` at U's 4 bits and
// refused (division by zero); round 6's context reading through the
// Squash2 admitted it (0 at 16 bits, which Icarus 12.0 and the Yosys 0.53
// netlist also give). The round 5 rule admits no shape that was loud, so the
// own-width reading must still be defined (Param.lean evalAt): loud again.
// Where it is (N = 4, U = 7; the default; N = 33) the value is unchanged.
module fold_sqd #(parameter int N = 32, parameter logic [N-1:0] U = 5) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3);
  localparam shortint H1 = 4'd8 / (U + 1'b1);
  localparam byte H2 = 4'd9 % (U + 1'b1);
  localparam bit [15:0] H3 = 4'd8 / (U + 1'b1);
  assign o1 = H1 + a;
  assign o2 = H2 + a;
  assign o3 = H3 + a;
endmodule
