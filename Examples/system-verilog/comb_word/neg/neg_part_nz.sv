// WP-B2 gate 4a: a part select of a declaration whose range is not zero-based (`[8:1]`) is outside the fragment.
module neg_part_nz (input logic [8:1] v, output logic [2:0] y);
  assign y = v[4:2];
endmodule
