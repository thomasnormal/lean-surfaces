// Nested fixed unpacked signed ports retain each cell's source layout.
module nested_unpacked_port_fixed (
  input  logic signed [3:0] a [1:0][2:1],
  output logic signed [3:0] y [1:0][2:1]
);
  assign y[1][2] = a[1][2] + 4'sd1;
  assign y[1][1] = -a[1][1];
  assign y[0][2] = a[0][2] + 4'sd1;
  assign y[0][1] = -a[0][1];
endmodule
