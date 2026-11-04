// The N-bit ripple-carry adder of Examples/system-verilog/ripple_add, with the genvar loop step
// written as an ASSIGNMENT (`i = i + 1`, IEEE 1800-2023 27.4) instead of `i++` (WP-L1,
// 2026-10-30). The extractor lowers the step to the SAME node as `i++`, so `ripple_step.pdesign`
// has the generate items of `ripple_add.pdesign` and the existing tactics prove it (comb_proof.lean).
module ripple_step #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[N];
endmodule
