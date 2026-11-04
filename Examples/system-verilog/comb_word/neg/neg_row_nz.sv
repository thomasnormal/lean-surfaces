// WP-B2 gate 4a: a whole row of a two-dimensional array whose first range is not zero-based (`[4:1]`) stays outside the fragment.
module neg_row_nz (input logic [2:0] x, output logic [2:0] y);
  logic [4:1][2:0] r;
  assign r[1] = x;
  assign y = r[1];
endmodule
