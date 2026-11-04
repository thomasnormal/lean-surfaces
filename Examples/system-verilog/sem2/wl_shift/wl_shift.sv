// WP-B2 pin P1: shifts. The left operand is extended to the CONTEXT width before the shift and the result truncated (`a << 1` into 5 bits keeps the carried-out bit; `a << N` into 4 bits is 0); an x/z bit of the left operand MOVES, an x/z bit of the amount makes every result bit x; an amount >= the width gives 0.
module wl_shift #(parameter int N = 4) (
  input  logic [3:0] a,
  input  logic [3:0] sh,
  output logic [3:0] y_same,
  output logic [3:0] y_over,
  output logic [3:0] v_same,
  output logic [4:0] y_wide,
  output logic [4:0] z_wide,
  output logic [4:0] v_wide
);
  assign y_same = a << 1;
  assign y_wide = a << 1;
  assign y_over = a << N;
  assign z_wide = a >> 1;
  assign v_same = a << sh;
  assign v_wide = a >> sh;
endmodule
