// An undriven output wire-array cell remains high impedance.
module partial_output_net_port_array (
  input logic [3:0] a,
  output wire logic [3:0] y [0:1]
);
  assign y[0] = a;
endmodule
