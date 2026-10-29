// An undriven child output NET (`output wire logic`) connected to the
// parent's variable: the parent reads z. Refused in the child:
// `PortSymbol:net-z`.
module net_z_child (
  input  logic [1:0] a,
  output wire logic [1:0] yn,
  output logic [1:0] y
);
  assign y = a;
endmodule

module net_z_hier (
  input  logic [1:0] a,
  output logic [1:0] on,
  output logic [1:0] o
);
  net_z_child u (.a(a), .yn(on), .y(o));
endmodule
