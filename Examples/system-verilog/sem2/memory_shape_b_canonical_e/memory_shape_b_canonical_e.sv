// Source-shaped parameterized child storage through canonical E hierarchy.
module memory_shape_b_child #(parameter integer W = 4, parameter integer P = 3) (
    input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  logic [W-1:0] s [P];
  always_ff @(posedge clk) begin
    for (int i = 1; i < P; i++) s[i] <= s[i-1];
    s[0] <= d;
  end
  assign q = s[P-1];
endmodule
module memory_shape_b_canonical_e #(parameter integer W = 4, parameter integer P = 3) (
    input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  memory_shape_b_child #(.W(W), .P(P)) child(.clk(clk), .d(d), .q(q));
endmodule
