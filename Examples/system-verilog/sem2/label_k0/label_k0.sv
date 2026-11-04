// Literal labels over a localparam-dependent range: `t` is `[K-1:0]`, the
// canonical `[3:0]` at the default N = 8 but the ASCENDING 2-bit `[-1:0]` at
// N = 4 (K = 0). The selects are `ArraySel` paths, normalized against the
// declared range at every point (IEEE 1800-2023 §7.4.2, §11.5.1): an
// out-of-range bit reads x, a write to one does nothing.
module label_k0 #(parameter int N = 8) (
  input  logic [1:0] b,
  input  logic [7:0] v,
  output logic [1:0] o,
  output logic       ob
);
  localparam int K = N - 4;
  logic [K-1:0] t;
  always_comb begin
    t = v;
    t[1 +: 1] = b[0];
  end
  assign o  = t[1 +: 2];
  assign ob = t[0 +: 1];
endmodule
