// A child output NET driven on one bit only: the other bit is z (IEEE
// 1800-2023 §6.6). Refused in the child: `PortSymbol:net-z`.
module net_z_part_child (input logic a, output wire logic [1:0] y);
  assign y[0] = a;
endmodule

module net_z_part (input logic a, output logic [1:0] o);
  net_z_part_child u (.a(a), .y(o));
endmodule
