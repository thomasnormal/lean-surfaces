// Fixed output wire-array cells with exactly one plain driver each are flat-safe.
module unpacked_output_net_port_fixed (
  input  logic [3:0] a,
  output wire logic [3:0] y [0:1]
);
  assign y[0] = a;
  assign y[1] = ~a;
endmodule
