// WP-B2 gate 4a: a chain of rows of a two-dimensional packed array indexed by a genvar. `r[i + 1]` and `r[i]` are whole rows
// (slang's legacy `BitSel` over a two-dimensional base); `r[0]` and `r[N]` over the parameter-dependent range are `ArraySel`.
module row_chain #(parameter int N = 4) (
  input  logic [N-1:0] x,
  output logic [N-1:0] y
);
  logic [N:0][N-1:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < N; i++) begin : g
    assign r[i + 1] = ~r[i];
  end
  assign y = r[N];
endmodule
