// WP-B2 gate 4a: a whole row of a THREE-dimensional packed array (`r[0]` selects a 2x3-bit block) is outside the fragment.
module neg_row_3d (input logic [2:0] x, output logic [5:0] y);
  logic [1:0][1:0][2:0] r;
  assign r[0] = {x, x};
  assign y = r[0];
endmodule
