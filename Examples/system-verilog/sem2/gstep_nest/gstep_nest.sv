// Nested genvar loops with assignment steps (WP-L1): the outer `i = i + 1`, the
// inner `j += 1`; an N x M AND matrix, row-major.
module gstep_nest #(parameter int N = 3, parameter int M = 2) (
  input  logic [N-1:0]   a,
  input  logic [M-1:0]   b,
  output logic [N*M-1:0] p
);
  generate
    for (genvar i = 0; i < N; i = i + 1) begin : row
      for (genvar j = 0; j < M; j += 1) begin : col
        assign p[i*M+j] = a[i] & b[j];
      end
    end
  endgenerate
endmodule
