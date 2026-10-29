// Unsized literals whose high-order bit is x or z, as declaration
// initializers at fixed widths (2026-10-28, round 4 repair, INIT verifier
// `w_ux`/`w_var2`). IEEE 1800-2023 §5.7.1 extends such a literal with that
// bit to the size of the expression; the round-4 lowering padded it with 0
// (`y` read 8 zeros then 32 x). Icarus 12.0, Xcelium 24.03 (refsim on
// vip-ng) and the Yosys 0.53 `synth -flatten; abc -g gates` netlist give
// y = 39 x then a, z = 36 z then 0001, u = 36 x then 0000, v = a then 35 z,
// t = 0001 (truncation), w = 36 x then 0101, r = 36 z.
module pi_unsized_xz (
  input  logic        clk,
  input  logic        a,
  output logic [39:0] y = 'bx,
  output logic [39:0] z = 'hz1,
  output logic [39:0] u = 'hx0,
  output logic [35:0] v = 'bz,
  output logic [3:0]  t = 'hz1,
  output logic [39:0] w,
  output logic [35:0] r
);
  logic [39:0] s = 'hx5;
  logic [35:0] q = 'hz;
  always @(posedge clk) begin
    y[0] <= a;
    v[35] <= a;
  end
  assign w = s;
  assign r = q;
endmodule
