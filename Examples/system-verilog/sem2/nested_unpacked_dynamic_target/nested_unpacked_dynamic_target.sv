// Run-time writes through finite multidimensional unpacked arrays.
module nested_unpacked_dynamic_target (
  input logic i,
  input logic [1:0] j,
  input logic [7:0] v,
  output logic [7:0] a [0:1][0:2]
);
  always_comb a[i][j] = v;
endmodule
