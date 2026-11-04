// Fixed unpacked integral ports are flattened into existing scalar cells.
module unpacked_port_fixed (
  input logic [3:0] a [0:1],
  output logic [3:0] y [0:1]
);
  assign y[0] = a[0] ^ 4'b0011;
  assign y[1] = a[1] + 4'b0001;
endmodule
