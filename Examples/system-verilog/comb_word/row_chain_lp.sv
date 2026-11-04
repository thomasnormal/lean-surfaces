// WP-B2 gate 4a: the same chain over LOCALPARAM dimensions, rows 2N bits wide.
module row_chain_lp #(parameter int N = 4) (
  input  logic [2*N-1:0] x,
  output logic [2*N-1:0] y
);
  localparam integer R = N + 1;
  localparam integer C = 2 * N;
  logic [R-1:0][C-1:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < N; i++) begin : g
    assign r[i + 1] = ~r[i];
  end
  assign y = r[N];
endmodule
