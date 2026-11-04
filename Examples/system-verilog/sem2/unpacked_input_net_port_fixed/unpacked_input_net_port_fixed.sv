// Fixed unpacked input nets carry connection values through existing cells.
module unpacked_input_net_port_fixed (
  input wire logic [3:0] a [0:1],
  output logic [3:0] y
);
  assign y = a[0] ^ a[1];
endmodule
