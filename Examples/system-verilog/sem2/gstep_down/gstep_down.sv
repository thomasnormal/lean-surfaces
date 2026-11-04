// Decreasing genvar loops written as assignments (WP-L1): `g = g - 1` and
// `g -= 1` are the same step node as `g--`. Two bit reversals.
module gstep_down #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] r1, r2
);
  generate
    for (genvar i = N - 1; i >= 0; i = i - 1) begin : d1
      assign r1[N-1-i] = a[i];
    end
    for (genvar j = N - 1; j >= 0; j -= 1) begin : d2
      assign r2[j] = a[N-1-j];
    end
  endgenerate
endmodule
