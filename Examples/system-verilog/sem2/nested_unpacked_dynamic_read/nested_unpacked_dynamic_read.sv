// Run-time reads through finite multidimensional unpacked arrays.
module nested_unpacked_dynamic_read (
  input logic i,
  input logic [1:0] j,
  input logic [7:0] a [0:1][0:2],
  output logic [7:0] y
);
  always_comb y = a[i][j];
endmodule
