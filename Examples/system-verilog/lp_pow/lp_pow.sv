// `**` in localparams (IEEE 1800-2023 §11.4.3): `P = 2 ** L`, the least power of two above N (L = $clog2(N + 1)), as a
// declared width and in a generate bound, and `T = 3 ** 2` (a 2-state `int`, which the elaborator squashes to 2 states)
// as a declared width and a generate bound. The bits of `w` above N are zeros, so `y` is `a`; `p` is `a[0]`.
module lp_pow #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y,
  output logic         p
);
  localparam integer L = $clog2(N + 1);
  localparam integer P = 2 ** L;
  localparam int T = 3 ** 2;
  logic [P-1:0] w;
  logic [T-1:0] t;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_lo
      assign w[i] = a[i];
    end
    for (i = 0; i < P - N; i++) begin : g_hi
      assign w[N + i] = 1'b0;
    end
    for (i = 0; i < T; i++) begin : g_t
      assign t[i] = a[0];
    end
  endgenerate
  assign y = w[N-1:0];
  assign p = t[T-1];
endmodule
