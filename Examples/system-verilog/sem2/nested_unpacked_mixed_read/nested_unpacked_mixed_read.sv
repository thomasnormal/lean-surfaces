// A constant inner index still selects from the dynamic outer dimension.
module nested_unpacked_mixed_read (
  input logic i,
  input logic [7:0] a [0:1][0:2],
  output logic [7:0] y
);
  always_comb y = a[i][1];
endmodule
