// Port-width clean-room wall: net input select and net output target.
module port_net_child (
  input logic [3:0] i,
  output logic [1:0] o
);
  assign o = i[1:0];
endmodule

module port_net_width (
  input wire [1:0] w,
  output wire [3:0] y
);
  port_net_child u (.i(w[1:0]), .o(y));
endmodule
