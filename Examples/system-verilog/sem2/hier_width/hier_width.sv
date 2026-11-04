// F3 differential design: port-width coercion. A port connection is a
// continuous assignment: a narrower source is zero-extended, a wider one
// truncated, in both directions.
module hw_pass #(parameter int W = 4) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o
);
  assign o = ~i;
endmodule

module hier_width #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [1:0]   s,
  output logic [N+1:0] out_wide,
  output logic [1:0]   out_narrow,
  output logic [N-1:0] in_wide,
  output logic [N+1:0] in_narrow,
  output logic [N-1:0] in_safe
);
  hw_pass #(.W(N))     u1 (.i(a), .o(out_wide));
  hw_pass #(.W(N))     u2 (.i(a), .o(out_narrow));
  hw_pass #(.W(N - 1)) u3 (.i(a), .o(in_wide[N-2:0]));
  hw_pass #(.W(N + 2)) u4 (.i(s), .o(in_narrow));
  hw_pass #(.W(N))     u5 (.i(s ^ 2'b10), .o(in_safe));
  assign in_wide[N-1] = 1'b0;
endmodule
