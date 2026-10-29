// Unsized x/z literal port actuals into a port of parameter width N, whose
// default is 32 bits (round 5 repair, Lane A, 2026-10-29; verifier repro
// `vp1`). At the bound (default) point nothing is widened, so the round-5
// `PortConnection:unsized-xz` did not fire, and Lean zero-extended the
// 32-bit literal into the wider port at N = 33, 40, 64 — Icarus 12.0's
// padding (N = 40: 8 zeros, 28 x, 0000), against the Yosys 0.53 netlist
// (36 x then 0000) and Xcelium. Now any actual holding an unsized x/z-top
// literal is loud (`PortConnection:unsized-xz`).
module pa_unsized_xz_p_c #(parameter int W = 32) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o
);
  assign o = i;
endmodule
module pa_unsized_xz_p #(parameter int N = 32) (
  input  logic clk,
  input  logic [3:0] a,
  output logic [N-1:0] y1,
  output logic [N-1:0] y2,
  output logic [N-1:0] y3
);
  pa_unsized_xz_p_c #(.W(N)) u1 (.i('hx0), .o(y1));
  pa_unsized_xz_p_c #(.W(N)) u2 (.i('hz1), .o(y2));
  pa_unsized_xz_p_c #(.W(N)) u3 (.i('bx), .o(y3));
endmodule
