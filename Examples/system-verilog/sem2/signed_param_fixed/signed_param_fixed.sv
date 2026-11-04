// A parameter-dependent signed four-state packed port.  The copy keeps the
// source width at every point, and the comparison exercises signed ordering
// without a width-changing conversion.
module signed_param_fixed #(parameter N = 4) (
  input logic signed [N-1:0] a,
  input logic signed [N-1:0] b,
  output logic signed [N-1:0] y,
  output logic lt
);
  always_comb begin
    y = a;
    lt = a < b;
  end
endmodule
