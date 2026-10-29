// Unsized INT-class constants (`-1`, `37`, `N - 1`, `-7 / 2`, `B * 2`, ...)
// assigned to parameter-width targets. slang binds each as a conversion to
// the target type of the DEFAULT point (`[8:0]` at N = 7); the envelope keeps
// the UNCONVERTED constant tree and the model materializes it at the
// instantiated width (IEEE 1800-2023 §11.6.1, §11.8.2, §10.7: the
// right-hand side keeps its own signedness, its width is the context's).
// Before 2026-10-28 the fold baked the default width in: verifier
// w_stale_flat (`[N+1:0]`, default N = 4) read `-1` at N = 7 as 000111111
// where every simulator reads 111111111.
module int_const_flat #(parameter int N = 7, parameter byte B = -3) (
  input  logic [3:0]   a,
  output logic [N+1:0] o1, o2, o3, o4, o5, o6, o7, o8, o9, o10,
  output logic [N+1:0] o11, o12, o13, o14, o15, o16, o17, o18
);
  localparam int K = N - 4;
  assign o1  = -1;
  assign o2  = 37;
  assign o3  = N - 1;
  assign o4  = -N;
  assign o5  = 2 * N + 1;
  assign o6  = 100 / 3;
  assign o7  = -7 / 2;
  assign o8  = K;
  assign o9  = ~0;
  assign o10 = 1 << N;
  assign o11 = -8 >>> 1;
  assign o12 = (N * N) % 5;
  assign o13 = 2 ** N;
  assign o14 = B * 2;
  assign o15 = -N / 2;
  assign o16 = B;
  always_comb o17 = -2;
  always_comb begin
    o18 = '0;
    o18 = -N - 1;
  end
endmodule
