// Localparams defined by the four shifts of an `int` (IEEE 1800-2023 §11.4.10), used as declared widths and select
// bounds: `M = N << 1` (2N), `H = M >> 1` (N), `Q = (N <<< 2) >>> 2` (N: `<<<` is `<<`, and `>>>` of a signed `int` is
// arithmetic). `P = (1 << (K - 1)) - 1` shifts by a parameter amount (it is unused: its value is read, the obligations
// never meet the power).
module lp_shifts #(parameter int N = 8, parameter int K = 3) (
  input  logic [N-1:0] a, b,
  output logic [2*N-1:0] y,
  output logic [N-1:0] z
);
  localparam integer M = N << 1;
  localparam integer H = M >> 1;
  localparam integer Q = (N <<< 2) >>> 2;
  localparam integer P = (1 << (K - 1)) - 1;
  logic [M-1:0] t;
  assign t = {a, b};
  assign y = t;
  assign z = t[H-1:0] ^ t[M-1:Q];
endmodule
