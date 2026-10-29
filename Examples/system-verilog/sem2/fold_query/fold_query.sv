// Round 3 folds, item 4: `$high`/`$size` of a declared signal read its
// FIRST packed dimension at each point (IEEE 1800-2023 20.7) -- not
// `width - 1` / `width`: `$high(u)` of `[7:4]` is 7, `$size(m)` of
// `[3:0][N-1:0]` is 4, `$high(v)` of `[N-1:0]` at N = 0 (the ascending
// [-1:0]) is 0. Read in value positions: Icarus 12.0 cannot evaluate
// them in a generate condition or a localparam.
module fold_query #(parameter int N = 3) (
  input  logic [N-1:0]      v,
  input  logic [7:4]        u,
  input  logic [3:0][N-1:0] m,
  output logic [7:0]        o1,
  output logic [7:0]        o2,
  output logic [7:0]        o3,
  output logic [7:0]        o4
);
  assign o1 = $high(u);
  assign o2 = $size(m);
  assign o3 = $high(v);
  assign o4 = $size(v);
endmodule
