// WP-B2 gate 3 pin P17: shifts by an unsized constant amount (32 bits wide, never widening the result): `a << 1`, `a >> 2`, an amount at least the width (`a << 4` into 4 bits is 0) and a shift into a wider target.
module wl_shl_const #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y1,
  output logic [N-1:0] y2,
  output logic [N-1:0] y3,
  output logic [N:0] y4
);
  assign y1 = a << 1;
  assign y2 = a >> 2;
  assign y3 = a << N;
  assign y4 = a << 1;
endmodule
