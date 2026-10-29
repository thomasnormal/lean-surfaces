// The generate-for twin of `pa_unsized_xz_p` (round 5 repair, Lane A,
// 2026-10-29; verifier repro `vp2`): a NON-parametric top; slang binds the
// loop body at g = 0 (a 32-bit port), and at g = 1 the port is 40 bits.
// The model gave Icarus 12.0's zero padding there (8 zeros, 28 x, 0000),
// the Yosys 0.53 netlist 36 x then 0000; no cross-check applies. Now loud
// (`PortConnection:unsized-xz`).
module pa_unsized_xz_g_c #(parameter int W = 32) (
  input  logic [W-1:0] i,
  output logic [39:0] o
);
  assign o = i;
endmodule
module pa_unsized_xz_g (
  input  logic clk,
  input  logic [3:0] a,
  output logic [39:0] y0,
  output logic [39:0] y1
);
  logic [1:0][39:0] yv;
  for (genvar g = 0; g < 2; g++) begin : G
    pa_unsized_xz_g_c #(.W(32 + 8*g)) u (.i('hx0), .o(yv[g]));
  end
  assign y0 = yv[0];
  assign y1 = yv[1];
endmodule
