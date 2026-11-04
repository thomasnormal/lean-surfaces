// Packed-array select paths over ascending, descending and non-zero-based
// ranges whose bounds depend on parameters: element and part targets, and
// `+:`/`-:` parts with genvar-expression bases (sv-0.2 `ArraySel`).
module array_ranges #(parameter int N = 3, parameter int L = 2) (
  input  logic [4*N-1:0] src,
  output logic [4*N-1:0] q_flat,
  output logic [4*N-1:0] r_flat,
  output logic [3:0]     first,
  output logic [1:0]     mid
);
  logic [0:N-1][L+3:L] q;  // ascending outer, non-zero-based descending inner
  logic [N:1][0:3]     r;  // non-zero-based descending outer, ascending inner
  genvar i, j;
  for (i = 0; i < N; i++) begin : g_q
    for (j = L; j <= L + 3; j++) begin : g_qj
      assign q[i][j] = src[4*i + j - L];
    end
  end
  for (i = 1; i <= N; i++) begin : g_r
    assign r[i][0:1] = q[i-1][L+3 -: 2];
    assign r[i][2:3] = q[i-1][L +: 2];
  end
  assign q_flat = q;
  assign r_flat = r;
  assign first  = q[0];
  assign mid    = r[N][1:2];
endmodule
