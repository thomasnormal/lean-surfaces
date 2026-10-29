// A packed struct whose member widths depend on a parameter: the semantic
// tier stores it as ONE vector with fixed member windows, which would be the
// DEFAULT point's layout at every point (verifier row `vg2`: at N = 8 `s.x`
// read the default window). Refused: `VariableSymbol:default-point-aggregate`.
module aggregate_point #(parameter int N = 3) (
  input  logic [N-1:0] a,
  input  logic [1:0]   b,
  output logic [N+1:0] o,
  output logic [N-1:0] x
);
  typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;
  st_t s;
  assign s = {a, b};
  assign o = s;
  assign x = s.x;
endmodule
