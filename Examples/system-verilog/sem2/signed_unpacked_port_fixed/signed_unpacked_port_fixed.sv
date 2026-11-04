// Signed fixed-unpacked ports preserve signed arithmetic through flattened cells.
module signed_unpacked_port_fixed (
  input logic signed [3:0] a [0:1],
  output logic signed [3:0] y [0:1]
);
  assign y[0] = a[0] + 4'sd1;
  assign y[1] = -a[1];
endmodule
