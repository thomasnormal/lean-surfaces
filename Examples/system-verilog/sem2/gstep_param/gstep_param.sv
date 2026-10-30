// REFUSED (loud, `GenerateFor:step`; WP-L1): the step amount is a parameter. It is
// folded at the default point only, so `g = g + S` is never read as `g++` even
// when `S` is 1 there.
module gstep_param #(parameter int N = 4, parameter int S = 1) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  generate
    for (genvar i = 0; i < N; i = i + S) begin : g
      assign y[i] = a[i];
    end
  endgenerate
endmodule
