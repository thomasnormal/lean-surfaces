// Round 3 repair, refusal row: an instance parameter override that is a
// TYPED context-propagating expression. IEEE 1800-2023 10.8 makes a typed
// parameter's override an assignment-like context, so `U + 8'd100` (8-bit
// U = 200) into the 16-bit `P` and the `int Q` is evaluated at the target's
// width: 300 in Icarus 12.0. Yosys 0.53 (the synthesized netlist) and
// Verilator 5.042 evaluate it at its own 8 bits: 44. The tools split, and
// the constant tier evaluates an override without the child's parameter
// type: refused, `InstanceSymbol:override-context`.
module fold_ovr_child #(parameter logic [15:0] P = 0, parameter int Q = 0) (
  input  logic [15:0] a,
  output logic [15:0] o1,
  output logic [15:0] o2
);
  assign o1 = P ^ a;
  assign o2 = Q ^ a;
endmodule

module fold_ovr #(parameter int N = 8) (
  input  logic [15:0] a,
  output logic [15:0] o1,
  output logic [15:0] o2
);
  localparam logic [N-1:0] U = 8'd200;
  fold_ovr_child #(.P(U + 8'd100), .Q(U + 8'd100)) c (.a(a), .o1(o1), .o2(o2));
endmodule
