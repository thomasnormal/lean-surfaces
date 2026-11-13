// Canonical-E source-shaped memory with nested generate-if/for expansion.
module generate_memory_canonical_e #(
  parameter integer W=4, parameter integer N=2
) (
  input logic clk, input logic [W-1:0] d,
  output logic [W-1:0] q
);
  logic [W-1:0] s [N];
  genvar g;
  generate
    if (N == 2) begin : selected
      for (g=0; g<N; g++) begin : gen
        always_ff @(posedge clk) s[g] <= d + g;
      end
    end else begin : fallback
      always_ff @(posedge clk) s[0] <= d;
    end
  endgenerate
  assign q = s[0];
endmodule
