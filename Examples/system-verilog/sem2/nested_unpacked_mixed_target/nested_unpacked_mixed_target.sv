// A constant inner index still selects from the dynamic outer dimension.
module nested_unpacked_mixed_target (
  input logic i,
  input logic [7:0] v,
  output logic [7:0] a [0:1][0:2]
);
  always_comb a[i][1] = v;
endmodule
