// Genvar step spelled as an assignment (WP-L1, 2026-10-30; the extractor lowers
// `g = g + 1`, `g = 1 + g`, `g += 1` to the SAME step node as `g++`): four loops,
// one spelling each, over inline and separately declared genvars.
module gstep_up #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] x1, x2, x3, x4
);
  genvar k;
  generate
    for (genvar i = 0; i < N; i = i + 1) begin : l1
      assign x1[i] = a[i] & b[i];
    end
    for (genvar i = 0; i < N; i += 1) begin : l2
      assign x2[i] = a[i] | b[i];
    end
    for (genvar i = 0; i < N; i = 1 + i) begin : l3
      assign x3[i] = a[i] ^ b[i];
    end
    for (k = 0; k < N; k = (k + 1)) begin : l4
      assign x4[k] = a[k] & ~b[k];
    end
  endgenerate
endmodule
