// Round 6 folds: the fixed-width typedef companion of `fold_tdw` (no
// dependent typedef): `s8_t`/`b8_t` keep slang's exact bounds at every M.
module fold_tdf #(parameter int M = 32) (
  input  logic [3:0] a,
  input  logic [M-1:0] b,
  output logic [63:0] o3, o4, o5);
  typedef logic signed [7:0] s8_t;
  typedef bit [7:0] b8_t;
  localparam s8_t T8 = -2;
  localparam b8_t B8 = -2;
  assign o3 = T8 + a;
  assign o4 = B8 + a;
  assign o5 = T8 + b;
endmodule
