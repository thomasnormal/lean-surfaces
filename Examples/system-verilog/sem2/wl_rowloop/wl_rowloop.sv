// WP-B2 gate 4a pin P19: genvar-indexed WHOLE ROWS of a two-dimensional packed array, read and written. (1) parameter dimensions: a chain of inverted rows (`r[i + 1] = ~r[i]`: the legacy `BitSel` over a two-dimensional base; `r[0]`, `r[N]` are `ArraySel`); (2) localparam dimensions, rows 2N wide, a row chosen by `?:` on bit i of `b`; (3) an `always_comb` per iteration over rows of a parametric array (the shape of a shift-and-add multiplier; every row is written procedurally, as a simulator that refuses to mix `assign` and `always_comb` on one variable requires); (4) literal dimensions (every label is the legacy `BitSel`). An x/z bit travels along the chain row by row.
module wl_rowloop #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  input  logic [2:0] c,
  output logic [N-1:0] y,
  output logic [2*N-1:0] z,
  output logic [2*N-1:0] p,
  output logic [2:0] w
);
  logic [N:0][N-1:0] r;
  assign r[0] = a;
  for (genvar i = 0; i < N; i++) begin : g1
    assign r[i + 1] = ~r[i];
  end
  assign y = r[N];

  localparam integer R = N + 1;
  localparam integer C = 2 * N;
  logic [R-1:0][C-1:0] q;
  assign q[0] = {a, b};
  for (genvar i = 0; i < N; i++) begin : g2
    assign q[i + 1] = b[i] ? ~q[i] : q[i];
  end
  assign z = q[N];

  logic [N:0][2*N-1:0] s;
  logic [2*N-1:0] ae;
  assign ae = a;
  always_comb s[0] = '0;
  for (genvar i = 0; i < N; i++) begin : g3
    always_comb begin
      if (b[i]) s[i + 1] = s[i] ^ ae;
      else      s[i + 1] = s[i];
    end
  end
  assign p = s[N];

  logic [3:0][2:0] t;
  assign t[0] = c;
  for (genvar i = 0; i < 3; i++) begin : g4
    assign t[i + 1] = ~t[i];
  end
  assign w = t[3];
endmodule
