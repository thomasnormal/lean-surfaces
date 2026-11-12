module packed_rhs_e #(parameter int N = 8) (input logic clk, input logic v, output logic [N-1:0] q);
  logic [N-1:0] t;
  always_ff @(posedge clk) t <= {t[N-2:0], v};
  assign q = t;
endmodule
