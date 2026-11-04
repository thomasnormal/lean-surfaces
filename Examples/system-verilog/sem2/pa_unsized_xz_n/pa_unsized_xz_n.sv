// `pa_unsized_xz_p` with a NARROWER default, N = 8 (round 5 repair, Lane A,
// 2026-10-29; verifier repro `vp7`): slang folded the actual to an 8-bit
// literal at the bound port width, and Lean zero-extended it at every wider
// point — at N = 40 the model gave 32 zeros then xxxx0000, Icarus 12.0 8
// zeros, 28 x, 0000, the Yosys 0.53 netlist 36 x then 0000: wrong against
// both. Now loud (`PortConnection:unsized-xz`).
module pa_unsized_xz_n_c #(parameter int W = 32) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o
);
  assign o = i;
endmodule
module pa_unsized_xz_n #(parameter int N = 8) (
  input  logic clk,
  input  logic [3:0] a,
  output logic [N-1:0] y1,
  output logic [N-1:0] y2,
  output logic [N-1:0] y3
);
  pa_unsized_xz_n_c #(.W(N)) u1 (.i('hx0), .o(y1));
  pa_unsized_xz_n_c #(.W(N)) u2 (.i('hz1), .o(y2));
  pa_unsized_xz_n_c #(.W(N)) u3 (.i('bx), .o(y3));
endmodule
