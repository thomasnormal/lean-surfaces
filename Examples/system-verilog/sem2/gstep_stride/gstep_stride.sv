// REFUSED (loud, `GenerateFor:step`; WP-L1): a stride-2 genvar step. It is legal
// SystemVerilog (IEEE 1800-2023 27.4) and every simulator evaluates it, but ls-sv's
// generate vocabulary is the +/-1 step (the semantic tier, the proof tactics): the
// step is outside the tier, and so are `g = g * 2` and a parameter amount.
module gstep_stride #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  generate
    for (genvar i = 0; i < N; i += 2) begin : g
      assign y[i] = a[i];
    end
  endgenerate
endmodule
