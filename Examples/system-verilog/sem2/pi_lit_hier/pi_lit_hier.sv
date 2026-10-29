// Plain literal initializers in parametric CHILDREN of a non-parametric top
// (2026-10-28, round 4 repair, INIT verifier `h_lit`/`h_slit`; no
// cross-check reaches them, so the round-4 model was silent): the child
// output `o = 2'b01` at W = 5 lost `o[W-1] <= a` (z = 00001 where Icarus
// gives 10001), and `t = 4'sb1010` at W = 8 read 00001010 (Icarus
// 11111010). Icarus 12.0, Xcelium 24.03 and the Yosys 0.53 netlist give
// z = a then 0001, s = 11111010, q = 10.
module pi_lit_hier_o #(parameter int W = 2) (
  input  logic         clk,
  input  logic         a,
  output logic [W-1:0] o = 2'b01
);
  always @(posedge clk) o[W-1] <= a;
endmodule

module pi_lit_hier_t #(parameter int W = 4) (
  output logic [W-1:0] o
);
  logic [W-1:0] t = 4'sb1010;
  assign o = t;
endmodule

module pi_lit_hier (
  input  logic       clk,
  input  logic       a,
  output logic [4:0] z,
  output logic [7:0] s,
  output logic [1:0] q
);
  pi_lit_hier_o #(.W(5)) v (.clk(clk), .a(a), .o(z));
  pi_lit_hier_t #(.W(8)) u (.o(s));
  pi_lit_hier_t #(.W(2)) w (.o(q));
endmodule
